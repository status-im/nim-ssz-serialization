# ssz_serialization
# Copyright (c) 2018-2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

# This module contains the parts necessary to create a Merkle hash from the core
# SSZ types outlined in the spec:
# https://github.com/ethereum/consensus-specs/blob/v1.0.1/ssz/simple-serialize.md#merkleization

{.push raises: [].}

# TODO https://github.com/nim-lang/Nim/issues/19357 and general pointer aliasing
# misdetection means we use output parameters rather than return values for a
# large part of the internal implemenation thus avoiding spurious `zeroMem`
# calls and other artefacts of the introduction of hidden temporaries

import
  std/[algorithm, options, sequtils],
  stew/[assign2, bitops2, endians2, objects, ptrops, shims/macros],
  results,
  nimcrypto/[hash, sha2],
  serialization/[case_objects, testing/tracing],
  "."/[bitseqs, codec, digest, types]

export
  results, hash.fromHex, codec, bitseqs, types, digest

when hasSerializationTracing:
  import stew/byteutils, typetraits

type BatchRequest* = object
  indices: ptr UncheckedArray[GeneralizedIndex]
  indicesHigh: int
  roots: ptr UncheckedArray[Digest]
  rootsHigh: int
  loopOrder: ptr UncheckedArray[int]
  loopOrderHigh: int

template init*[T: BatchRequest](
    t: typedesc[T],
    indicesParam: openArray[GeneralizedIndex],
    rootsParam: var openArray[Digest],
    loopOrderParam: seq[int] | static seq[int]): BatchRequest =
  BatchRequest(
    indices: makeUncheckedArray indicesParam.baseAddr,
    indicesHigh: indicesParam.high,
    roots: makeUncheckedArray rootsParam.baseAddr,
    rootsHigh: rootsParam.high,
    loopOrder: makeUncheckedArray loopOrderParam.baseAddr,
    loopOrderHigh: loopOrderParam.high)

template indexAt(i: int): GeneralizedIndex =
  block:
    let v = batch.indices.toOpenArray(0, batch.indicesHigh)[
      batch.loopOrder.toOpenArray(0, batch.loopOrderHigh)[i]]
    if atLayer != 0:
      let n = leadingZeros(v) + 1 + atLayer
      if n < 64:
        let x = ((v shl n) or 1.GeneralizedIndex).GeneralizedIndex
        rotateRight(x, n)
      else:  # `v shl 64` doesn't shift and silently becomes a noop
        doAssert n == 64
        1.GeneralizedIndex
    else:
      v

template rootAt(i: int): var Digest =
  batch.roots.toOpenArray(0, batch.rootsHigh)[
    batch.loopOrder.toOpenArray(0, batch.loopOrderHigh)[i]]

const unsupportedIndex =
  err(Result[void, string], "Generalized index not supported.")

template chunkForIndex(chunkIndex: GeneralizedIndex): Limit =
  block:
    (chunkIndex - firstChunkIndex).Limit

template chunksForIndex(index: GeneralizedIndex): Slice[Limit] =
  block:
    let
      numLayersAboveChunks = chunkLayer - indexLayer
      chunkIndexLow = index shl numLayersAboveChunks
      chunkIndexHigh = chunkIndexLow or
        ((1.GeneralizedIndex shl numLayersAboveChunks) - 1.GeneralizedIndex)

    chunkForIndex(chunkIndexLow) .. chunkForIndex(chunkIndexHigh)

template chunkContainingIndex(index: GeneralizedIndex): Limit =
  block:
    let
      numLayersBelowChunks = indexLayer - chunkLayer
      chunkIndex = index shr numLayersBelowChunks

    chunkForIndex(chunkIndex)

const
  zero64 = default array[64, byte]
  zeroDigest = Digest()
  bitsPerChunk = bytesPerChunk * 8

func binaryTreeHeight*(totalElements: Limit): Limit =
  bitWidth(nextPow2(uint64 totalElements)).Limit

type
  SszMerkleizer2*[height: static[Limit]] = object
    ## The Merkleizer incrementally computes the SSZ-style Merkle root of a tree
    ## with `2**(height-1)` leaf nodes.
    ##
    ## As chunks are added, the combined hash of each pair of chunks is computed
    ## and partially propagated up the tree in the `combinedChunks` array -
    ## finally, `getFinalHash` computes the rest of the tree as if all-zeroes
    ## chunks filled the rest of the tree up to the `limit`.
    # The code is structured in a way that some buffering and caching happens
    # in this module - therefore, we make sure to fill a 64-byte buffer
    # whenever possible to avoid the internal buffer copying that
    # `sha256.update` otherwise would do.
    # The two digests represent the left and right nodes that get combined to
    # a parent node in the tree.
    # `SszMerkleizer` used chunk count as limit
    # TODO it's possible to further parallelize by using even wider buffers here
    when height >= 0:
      combinedChunks: array[height, (Digest, Digest)]
    else:
      combinedChunks: seq[(Digest, Digest)]
    totalChunks*: uint64 # Public for historical reasons
    topIndex: int
    internal: bool
      # Avoid copying chunk data into merkleizer when not needed - may result
      # in an incomplete root-to-leaf proof

template limit(height: Limit): Limit =
  if height == 0: 0'i64 else: 1'i64 shl (height - 1)

template limit*(v: SszMerkleizer2): Limit =
  when typeof(v).height >= 0:
    typeof(v).height.limit
  else:
    v.combinedChunks.len.limit

template getChunkCount*(m: SszMerkleizer2): uint64 =
  m.totalChunks

func getCombinedChunks*(m: SszMerkleizer2): seq[Digest] =
  mapIt(toOpenArray(m.combinedChunks, 0, m.topIndex), it[0])

template mergeBranches(
    existing: Digest, newData: array[32, byte], res: var Digest) =
  trs "MERGING BRANCHES ARRAY"
  digest(existing.data, newData, res)

template mergeBranches(a, b: Digest, res: var Digest) =
  trs "MERGING BRANCHES DIGEST"
  digest(a.data, b.data, res)

func computeZeroHashes: array[sizeof(Limit) * 8, Digest] =
  result[0] = Digest()
  for i in 1 .. result.high:
    mergeBranches(result[i - 1], result[i - 1], result[i])

const zeroHashes* = computeZeroHashes()

func combineToTop(merkleizer: var SszMerkleizer2, res: var Digest) =
  let
    bottomHashIdx = firstOne(max(merkleizer.totalChunks, 1)) - 1
    submittedChunksHeight = bitWidth(max(merkleizer.totalChunks, 1) - 1)
    topHashIdx = merkleizer.topIndex

  trs "BOTTOM HASH ", bottomHashIdx
  trs "SUBMITTED HEIGHT ", submittedChunksHeight
  trs "TOP HASH IDX ", topHashIdx

  if bottomHashIdx != submittedChunksHeight:
    # Our tree is not finished. We must complete the work in progress
    # branches and then extend the tree to the right height.
    assign(
      merkleizer.combinedChunks[bottomHashIdx][1],
      zeroHashes[bottomHashIdx])

    block:
      mergeBranches(
        merkleizer.combinedChunks[bottomHashIdx][0],
        merkleizer.combinedChunks[bottomHashIdx][1],
        merkleizer.combinedChunks[bottomHashIdx + 1][1])

    for i in bottomHashIdx + 1 ..< topHashIdx:
      if i == topHashIdx - 1:
        if getBitLE(merkleizer.totalChunks, i):
          trs "COMBINED"
          mergeBranches(
            merkleizer.combinedChunks[i][0], merkleizer.combinedChunks[i][1],
            res)
        else:
          trs "COMBINED WITH ZERO"
          mergeBranches(merkleizer.combinedChunks[i][1], zeroHashes[i], res)
      else:
        if getBitLE(merkleizer.totalChunks, i):
          trs "COMBINED"
          mergeBranches(
            merkleizer.combinedChunks[i][0], merkleizer.combinedChunks[i][1],
            merkleizer.combinedChunks[i + 1][1])
        else:
          trs "COMBINED WITH ZERO"
          mergeBranches(
            merkleizer.combinedChunks[i][1], zeroHashes[i],
            merkleizer.combinedChunks[i + 1][1])

  elif bottomHashIdx == topHashIdx:
    # We have a perfect tree (chunks == 2**n) at just the right height!
    res = merkleizer.combinedChunks[bottomHashIdx][0]
  else:
    # We have a perfect tree of user chunks, but we have more work to
    # do - we must extend it to reach the desired height
    if bottomHashIdx == topHashIdx - 1:
      mergeBranches(
        merkleizer.combinedChunks[topHashIdx - 1][0],
        zeroHashes[topHashIdx - 1], res)
    else:
      mergeBranches(
        merkleizer.combinedChunks[bottomHashIdx][0],
        zeroHashes[bottomHashIdx],
        merkleizer.combinedChunks[bottomHashIdx + 1][1])

      for i in bottomHashIdx + 1 ..< topHashIdx - 1:
        mergeBranches(
          merkleizer.combinedChunks[i][1], zeroHashes[i],
          merkleizer.combinedChunks[i + 1][1])

      mergeBranches(
        merkleizer.combinedChunks[topHashIdx - 1][1],
        zeroHashes[topHashIdx - 1], res)

func combineChunks(merkleizer: var SszMerkleizer2, start: int) =
  for i in start..<merkleizer.topIndex:
    trs "CALLING MERGE BRANCHES"
    if getBitLE(merkleizer.totalChunks, i + 1):
      mergeBranches(
        merkleizer.combinedChunks[i][0], merkleizer.combinedChunks[i][1],
        merkleizer.combinedChunks[i + 1][1])
    else:
      mergeBranches(
        merkleizer.combinedChunks[i][0], merkleizer.combinedChunks[i][1],
        merkleizer.combinedChunks[i + 1][0])
      break

template addChunkDirect(merkleizer: var SszMerkleizer2, body: untyped) =
  # add chunk allowing `body` to write directly to `chunk` memory thus avoiding
  # an extra copy - body must completely fill the chunk, including any zero
  # padding

  # TODO panic here isn't great - turn this into a bool-returning function?
  doAssert merkleizer.totalChunks < merkleizer.limit.uint64,
    "Adding chunks would exceed merklelizer limit " & $merkleizer.limit

  let
    odd = getBitLE(merkleizer.totalChunks, 0)
    # addr needed to work around compile-time evaluation issue
    chunkAddr = if odd:
      addr merkleizer.combinedChunks[0][1]
    else:
      addr merkleizer.combinedChunks[0][0]

  block:
    template chunk: Digest {.inject.} = chunkAddr[]
    body

  if odd:
    merkleizer.combineChunks(0)
  else:
    trs "WROTE BASE CHUNK ", toHex(chunkAddr[].data)

  inc merkleizer.totalChunks

func addChunk*(merkleizer: var SszMerkleizer2, data: openArray[byte]) =
  doAssert data.len > 0 and data.len <= bytesPerChunk

  const doesSupportChunks =
    when merkleizer.height >= 0:
      merkleizer.limit > 0
    else:
      true
  when not doesSupportChunks:
    raiseAssert "Cannot add chunks to 0-length merkleizer"
  else:
    when merkleizer.height < 0:
      if merkleizer.limit <= 0:
        raiseAssert "Cannot add chunks to 0-length merkleizer"

    addChunkDirect(merkleizer):
      assign(chunk.data.toOpenArray(0, data.high), data)
      if data.len < bytesPerChunk:
        zeroMem(addr chunk.data[data.len], bytesPerChunk - data.len)

template isOdd(x: SomeNumber): bool =
  (x and 1) != 0

type OnChunkAdded[height: static[Limit]] =
  proc (
    merkleizer: var SszMerkleizer2[height],
    data: openArray[byte]) {.noSideEffect.}

func doAddChunks[height: static[Limit]](
    merkleizer: var SszMerkleizer2[height], data: openArray[byte],
    onChunkAdded: OnChunkAdded[height] = nil) =
  doAssert merkleizer.totalChunks == 0
  doAssert merkleizer.limit * bytesPerChunk >= data.len,
    "Adding chunks would exceed merklelizer limit " & $merkleizer.limit

  var done = 0
  while done < data.len:
    let
      remaining = data.len - done

    if remaining >= bytesPerChunk * 2:
      const doesSupportChunks =
        when merkleizer.height >= 0:
          merkleizer.limit > 1  # Defeat compile-time index checking
        else:
          true
      when doesSupportChunks:
        if not merkleizer.internal:
          # Needed for getCombinedChunks
          assign(
            merkleizer.combinedChunks[0][0].data,
            data.toOpenArray(done, done + bytesPerChunk - 1))

        trs "COMPUTING COMBINED DATA HASH ", done

        if getBitLE(merkleizer.totalChunks, 1):
          digest(
            data.toOpenArray(done, done + bytesPerChunk * 2 - 1),
            merkleizer.combinedChunks[1][1])

          merkleizer.combineChunks(1)
        else:
          digest(
            data.toOpenArray(done, done + bytesPerChunk * 2 - 1),
            merkleizer.combinedChunks[1][0])

        done += bytesPerChunk * 2
        merkleizer.totalChunks += 2

        if onChunkAdded != nil:
          onChunkAdded(merkleizer, data)
    else:
      trs "COMPUTING REMAINDER DATA HASH ", remaining
      if remaining > bytesPerChunk:
        merkleizer.addChunk(data.toOpenArray(done, done + bytesPerChunk - 1))
        done += bytesPerChunk

      merkleizer.addChunk(data.toOpenArray(done, data.high))

      if onChunkAdded != nil:
        onChunkAdded(merkleizer, data)
      break

func addChunks*(merkleizer: var SszMerkleizer2, data: openArray[byte]) =
  doAddChunks[merkleizer.height](merkleizer, data)

func addChunks*(
    merkleizer: var SszMerkleizer2, data: openArray[byte],
    batch: BatchRequest, slice: Slice[int], atLayer: int
): Result[void, string] =
  let
    chunkLayer = merkleizer.combinedChunks.len - 1
    firstChunkIndex = 1.GeneralizedIndex shl chunkLayer
  var
    ok = true
    i = slice.a
  func collect(
      merkleizer: var SszMerkleizer2, data: openArray[byte],
      isComplete = false) =
    while ok and i <= slice.b:
      let
        index = indexAt(i)
        indexLayer = log2trunc(index)
      if indexLayer < chunkLayer:
        let chunks = chunksForIndex(index)
        if chunks.a * bytesPerChunk >= data.len:
          rootAt(i) = zeroHashes[chunkLayer - indexLayer]
        elif chunks.b < merkleizer.totalChunks.Limit:
          if getBitLE(merkleizer.totalChunks, chunkLayer - indexLayer):
            rootAt(i) = merkleizer.combinedChunks[chunkLayer - indexLayer][0]
          else:
            rootAt(i) = merkleizer.combinedChunks[chunkLayer - indexLayer][1]
        elif isComplete:
          rootAt(i) = merkleizer.combinedChunks[chunkLayer - indexLayer][1]
        else:
          break
      elif indexLayer == chunkLayer:
        let
          chunk = chunkForIndex(index)
          first = chunk * bytesPerChunk
        if first >= data.len:
          rootAt(i) = zeroHashes[0]
        else:
          let nbytes = min(data.len, first.int + bytesPerChunk) - first.int
          rootAt(i).data[0 ..< nbytes] =
            data.toOpenArray(first.int, first.int + nbytes - 1)
          rootAt(i).data[nbytes ..< bytesPerChunk] =
            zero64.toOpenArray(nbytes, bytesPerChunk - 1)
      else:
        ok = false
      inc i

  merkleizer.doAddChunks(data) do (
      merkleizer: var SszMerkleizer2, data: openArray[byte]):
    merkleizer.collect(data)

  if ok and i <= slice.b:
    merkleizer.combineToTop(merkleizer.combinedChunks[merkleizer.topIndex][1])
    merkleizer.collect(data, isComplete = true)

  if not ok or i <= slice.b:
    return unsupportedIndex
  ok()

func addChunkAndGenMerkleProof*(merkleizer: var SszMerkleizer2,
                                hash: Digest,
                                outProof: var openArray[Digest]) =
  var
    hashWrittenToMerkleizer = false
    hash = hash

  doAssert merkleizer.topIndex < outProof.len

  for level in 0 .. merkleizer.topIndex:
    if getBitLE(merkleizer.totalChunks, level):
      outProof[level] = merkleizer.combinedChunks[level][0]
      mergeBranches(merkleizer.combinedChunks[level][0], hash, hash)
    else:
      if not hashWrittenToMerkleizer:
        merkleizer.combinedChunks[level][0] = hash
        hashWrittenToMerkleizer = true
      outProof[level] = zeroHashes[level]
      mergeBranches(hash, zeroHashes[level], hash)

  merkleizer.totalChunks += 1

func completeStartedChunk(merkleizer: var SszMerkleizer2,
                          hash: Digest, atLevel: int) =
  when false:
    let
      insertedChunksCount = 1'u64 shl (atLevel - 1)
      chunksStateMask = (insertedChunksCount shl 1) - 1
    doAssert (merkleizer.totalChunks and chunksStateMask) == insertedChunksCount

  var hash = hash
  for i in atLevel .. merkleizer.topIndex:
    if getBitLE(merkleizer.totalChunks, i):
      mergeBranches(merkleizer.combinedChunks[i][0], hash, hash)
    else:
      merkleizer.combinedChunks[i][0] = hash
      break

func addChunksAndGenMerkleProofs*(merkleizer: var SszMerkleizer2,
                                  chunks: openArray[Digest]): seq[Digest] =
  doAssert chunks.len > 0 and merkleizer.topIndex > 0

  let proofHeight = merkleizer.topIndex + 1
  result = newSeq[Digest](chunks.len * proofHeight)

  if chunks.len == 1:
    merkleizer.addChunkAndGenMerkleProof(chunks[0], result)
    return

  let newTotalChunks = merkleizer.totalChunks + chunks.len.uint64

  var
    # A perfect binary tree will take either `chunks.len * 2` values if the
    # number of elements in the base layer is odd and `chunks.len * 2 - 1`
    # otherwise. Each row may also need a single extra element at most if
    # it must be combined with the existing values in the Merkleizer:
    merkleTree = newSeq[Digest](chunks.len + merkleizer.topIndex)
    merkleTreeIdx = 0
    inRowIdx = merkleizer.totalChunks
    postUpdateInRowIdx = newTotalChunks
    zeroMixed = false

  template writeResult(chunkIdx, level: int, chunk: Digest) =
    result[chunkIdx * proofHeight + level] = chunk

  # We'll start by generating the first row of the Merkle tree.
  var currPairEnd = if inRowIdx.isOdd:
    # an odd chunk number means that we must combine the
    # hash with the existing pending sibling hash in the
    # merkleizer.
    writeResult(0, 0, merkleizer.combinedChunks[0][0])
    mergeBranches(
      merkleizer.combinedChunks[0][0], chunks[0], merkleTree[merkleTreeIdx])

    # TODO: can we immediately write this out?
    merkleizer.completeStartedChunk(merkleTree[merkleTreeIdx], 1)
    merkleTreeIdx += 1
    2
  else:
    1

  if postUpdateInRowIdx.isOdd:
    merkleizer.combinedChunks[0][0] = chunks[^1]

  while currPairEnd < chunks.len:
    writeResult(currPairEnd - 1, 0, chunks[currPairEnd])
    writeResult(currPairEnd, 0, chunks[currPairEnd - 1])
    mergeBranches(
      chunks[currPairEnd - 1], chunks[currPairEnd], merkleTree[merkleTreeIdx])
    merkleTreeIdx += 1
    currPairEnd += 2

  if currPairEnd - 1 < chunks.len:
    zeroMixed = true
    writeResult(currPairEnd - 1, 0, zeroHashes[0])
    mergeBranches(
      chunks[currPairEnd - 1], zeroHashes[0], merkleTree[merkleTreeIdx])
    merkleTreeIdx += 1

  var
    level = 0
    baseChunksPerElement = 1
    treeRowStart = 0
    rowLen = merkleTreeIdx

  template writeProofs(rowChunkIdx: int, hash: Digest) =
    let
      startAbsIdx = (inRowIdx.int + rowChunkIdx) * baseChunksPerElement
      endAbsIdx = startAbsIdx + baseChunksPerElement
      startResIdx = max(startAbsIdx - merkleizer.totalChunks.int, 0)
      endResIdx = min(endAbsIdx - merkleizer.totalChunks.int, chunks.len)

    for resultPos in startResIdx ..< endResIdx:
      writeResult(resultPos, level, hash)

  if rowLen > 1:
    while level < merkleizer.topIndex:
      inc level
      baseChunksPerElement *= 2
      inRowIdx = inRowIdx div 2
      postUpdateInRowIdx = postUpdateInRowIdx div 2

      var currPairEnd = if inRowIdx.isOdd:
        # an odd chunk number means that we must combine the
        # hash with the existing pending sibling hash in the
        # merkleizer.
        writeProofs(0, merkleizer.combinedChunks[level][0])
        mergeBranches(
          merkleizer.combinedChunks[level][0], merkleTree[treeRowStart],
          merkleTree[merkleTreeIdx])

        # TODO: can we immediately write this out?
        merkleizer.completeStartedChunk(merkleTree[merkleTreeIdx], level + 1)
        merkleTreeIdx += 1
        2
      else:
        1

      if postUpdateInRowIdx.isOdd:
        merkleizer.combinedChunks[level][0] = merkleTree[treeRowStart + rowLen -
                                                      ord(zeroMixed) - 1]
      while currPairEnd < rowLen:
        writeProofs(currPairEnd - 1, merkleTree[treeRowStart + currPairEnd])
        writeProofs(currPairEnd, merkleTree[treeRowStart + currPairEnd - 1])
        mergeBranches(
          merkleTree[treeRowStart + currPairEnd - 1],
          merkleTree[treeRowStart + currPairEnd],
          merkleTree[merkleTreeIdx])
        merkleTreeIdx += 1
        currPairEnd += 2

      if currPairEnd - 1 < rowLen:
        zeroMixed = true
        writeProofs(currPairEnd - 1, zeroHashes[level])
        mergeBranches(
          merkleTree[treeRowStart + currPairEnd - 1], zeroHashes[level],
          merkleTree[merkleTreeIdx])
        merkleTreeIdx += 1

      treeRowStart += rowLen
      rowLen = merkleTreeIdx - treeRowStart

      if rowLen == 1:
        break

  doAssert rowLen == 1

  if (inRowIdx and 2) != 0:
    var tmp {.noinit.}: Digest
    mergeBranches(
      merkleizer.combinedChunks[level + 1][0], merkleTree[merkleTreeIdx], tmp)
    merkleizer.completeStartedChunk(tmp, level + 2)

  if (not zeroMixed) and (postUpdateInRowIdx and 2) != 0:
    merkleizer.combinedChunks[level + 1][0] = merkleTree[merkleTreeIdx]

  while level < merkleizer.topIndex:
    inc level
    baseChunksPerElement *= 2
    inRowIdx = inRowIdx div 2

    let hash = if getBitLE(merkleizer.totalChunks, level):
      merkleizer.combinedChunks[level][0]
    else:
      zeroHashes[level]

    writeProofs(0, hash)

  merkleizer.totalChunks = newTotalChunks

template createMerkleizer2*(
    height: static Limit, topLayer = 0,
    internalParam = false): auto =
  trs "CREATING A MERKLEIZER FOR ", height, " (topLayer: ", topLayer, ")"
  let topIndex = height.int - 1 - topLayer
  SszMerkleizer2[height](
    topIndex: if (topIndex < 0): 0 else: topIndex,
    totalChunks: 0,
    internal: internalParam)

template createMerkleizer2*(
    height: Limit, topLayer = 0,
    internalParam = false): auto =
  trs "CREATING A DYN MERKLEIZER FOR ", height, " (topLayer: ", topLayer, ")"
  let topIndex = height.int - 1 - topLayer
  SszMerkleizer2[-1](
    combinedChunks: newSeq[(Digest, Digest)](height),
    topIndex: if (topIndex < 0): 0 else: topIndex,
    totalChunks: 0,
    internal: internalParam)

func getFinalHash(merkleizer: var SszMerkleizer2, res: var Digest) =
  if merkleizer.totalChunks == 0:
    res = zeroHashes[merkleizer.topIndex]
    return

  merkleizer.combineToTop(res)

func getFinalHash*(merkleizer: var SszMerkleizer2): Digest {.noinit.} =
  getFinalHash(merkleizer, result)

func mixInLength(root: Digest, length: int, res: var Digest) =
  var buf {.noinit.}: array[64, byte]
  assign(buf.toOpenArray(0, root.data.high), root.data)
  assign(buf.toOpenArray(32, 39), uint64(length).toBytesLE())
  zeroMem(addr buf[40], 24)
  digest(buf, res)

func mixInLength*(root: Digest, length: int): Digest {.noinit.} =
  mixInLength(root, length, result)

func mixInSelector(root: Digest, selector: uint8, res: var Digest) =
  var buf {.noinit.}: array[64, byte]
  assign(buf.toOpenArray(0, root.data.high), root.data)
  buf[32] = selector
  zeroMem(addr buf[33], 31)
  digest(buf, res)

func hash_tree_root*(x: auto): Digest {.gcsafe, raises: [], noinit.}

func hash_tree_root_multi(
    x: auto,
    batch: BatchRequest,
    slice: Slice[int],
    atLayer = 0): Result[void, string] {.gcsafe, raises: [].}

func unionHashTreeRoot[T: object](x: T, res: var Digest) =
  var isSome = false
  x.withFieldPairs(key, val):
    when key != T.unionSelectorKey:
      doAssert not isSome
      isSome = true
      res = val.hash_tree_root()
  if not isSome:
    res.reset()

template addField(field) =
  trs "MERKLEIZING FIELD ", astToStr(field)
  addChunkDirect(merkleizer):
    chunk = hash_tree_root(field)
  trs "CHUNK ADDED"

func allFieldNames(T: typedesc[object|tuple]): auto #[{.compileTime.}]# =
  when T.isProgressiveContainer:
    const
      activeFields = T.activeFields
      totalChunks = activeFields.bitWidth
  else:
    const totalChunks = T.totalSerializedFields
  when T is object:
    var res: array[totalChunks, Opt[string]]
  else:
    var res: array[totalChunks, Opt[int]]
  var i = 0
  T.enumAllSerializedFields:
    when T.isProgressiveContainer:
      while not activeFields[i]:
        inc i
    when T is object:
      res[i].ok realFieldName
    else:
      res[i].ok i
    inc i
  doAssert i == totalChunks
  res

func allFieldValues[F: string|int](
    fieldNames: openArray[Opt[F]], x: NimNode): seq[NimNode] {.compileTime.} =
  var res = newSeqOfCap[NimNode](fieldNames.len)
  for i, fieldName in fieldNames:
    if fieldName.isSome:
      when F is string:
        let fieldName = ident fieldName.get
        res.add quote do: `x`.`fieldName`
      else:
        let fieldName = fieldName.get
        res.add quote do: `x`[`fieldName`]
    else:
      res.add quote do: zeroHashes[0]
  res

func doMerkleizeFields(
    allFieldValues: openArray[NimNode],
    height, x, chunks, topLayer, res: NimNode): NimNode {.compileTime.} =
  let
    merkleizer = ident "merkleizer"
    merkleize = ident "merkleize"
  var body = newStmtList()
  for i, fieldValue in allFieldValues:
    body.add quote do:
      if `i` >= `chunks`.a:
        if `i` > `chunks`.b:
          break `merkleize`
        addField `fieldValue`
  quote do:
    block:
      var merkleizer = createMerkleizer2(
        `height`, `topLayer`, internalParam = true)
      template `merkleizer`: auto = merkleizer
      block `merkleize`: `body`
      getFinalHash(merkleizer, `res`)

func doMerkleizeFields(
    allFieldValues: openArray[NimNode],
    height: NimNode, x: NimNode, res: NimNode): NimNode {.compileTime.} =
  let merkleizer = ident "merkleizer"
  var body = newStmtList()
  for fieldValue in allFieldValues:
    body.add quote do:
      addField `fieldValue`
  quote do:
    block:
      var merkleizer = createMerkleizer2(`height`, internalParam = true)
      template `merkleizer`: untyped = merkleizer
      `body`
      getFinalHash(merkleizer, `res`)

template genMerkleizeFieldsImpls(
    B: typedesc[object|tuple], F: typedesc[string|int]): untyped =
  macro merkleizeFieldsImpl[T: B](
      fieldNames: static[openArray[Opt[F]]],
      height: Limit | static Limit, x: T,
      chunks: Slice[Limit], topLayer: int, res: var Digest): untyped =
    fieldNames.allFieldValues(x).doMerkleizeFields(
      height, x, chunks, topLayer, res)

  macro merkleizeFieldsImpl[T: B](
      fieldNames: static[openArray[Opt[F]]],
      height: Limit | static Limit, x: T, res: var Digest): untyped =
    fieldNames.allFieldValues(x).doMerkleizeFields(height, x, res)

genMerkleizeFieldsImpls(object, string)
genMerkleizeFieldsImpls(tuple, int)

func merkleizeFields[T: object|tuple](
    height: Limit | static Limit, x: T,
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  T.allFieldNames.merkleizeFieldsImpl(height, x, chunks, topLayer, res)

func merkleizeFields[T: object|tuple](
    height: Limit | static Limit, x: T, res: var Digest) =
  T.allFieldNames.merkleizeFieldsImpl(height, x, res)

template writeBytesLE(chunk: var array[bytesPerChunk, byte], atParam: int,
                      val: UintN) =
  let at = atParam
  chunk[at ..< at + sizeof(val)] = toBytesLE(val)

func chunkedHashTreeRoot[T: BasicType](
    height: Limit | static Limit, arr: openArray[T],
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  static:
    doAssert bytesPerChunk mod sizeof(T) == 0
  const valuesPerChunk = bytesPerChunk div sizeof(T)
  let firstIdx = chunks.a * valuesPerChunk
  if arr.len <= firstIdx:
    res = zeroHashes[height - 1 - topLayer]
  else:
    var merkleizer = createMerkleizer2(height, topLayer, internalParam = true)
    let numFromFirst =
      min((chunks.b - chunks.a + 1) * valuesPerChunk, arr.len - firstIdx)
    when sizeof(T) == 1 or cpuEndian == littleEndian:
      let
        remainingBytes = numFromFirst * sizeof(T)
        pos = cast[ptr byte](unsafeAddr arr[firstIdx])

      merkleizer.addChunks(makeOpenArray(pos, remainingBytes.int))
    else:
      const valuesPerChunk = bytesPerChunk div sizeof(T)

      var writtenValues = 0

      var chunk: array[bytesPerChunk, byte]
      while writtenValues < numFromFirst - valuesPerChunk:
        for i in 0 ..< valuesPerChunk:
          chunk.writeBytesLE(
            i * sizeof(T), arr[firstIdx + writtenValues + i])
        addChunk(merkleizer, chunk)
        inc writtenValues, valuesPerChunk

      let remainingValues = numFromFirst - writtenValues
      if remainingValues > 0:
        var lastChunk: array[bytesPerChunk, byte]
        for i in 0 ..< remainingValues:
          lastChunk.writeBytesLE(
            i * sizeof(T), arr[firstIdx + writtenValues + i])
        addChunk(merkleizer, lastChunk)

    getFinalHash(merkleizer, res)

func chunkedHashTreeRoot[T: not BasicType](
    height: Limit | static Limit, arr: openArray[T],
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  mixin hash_tree_root, toSszType
  type S = typeof toSszType(declval T)
  when S is BasicType:
    chunkedHashTreeRoot(
      height, openArray[S](arr), chunks, topLayer, res)
  else:
    let firstIdx = chunks.a
    if arr.len <= firstIdx:
      res = zeroHashes[height - 1 - topLayer]
    else:
      var merkleizer = createMerkleizer2(height, topLayer, internalParam = true)
      let numFromFirst = min(chunks.b - chunks.a + 1, arr.len - firstIdx)
      for i in 0 ..< numFromFirst:
        addChunkDirect(merkleizer):
          chunk = hash_tree_root(arr[firstIdx + i])
      getFinalHash(merkleizer, res)

template chunkedHashTreeRoot[T](
    height: Limit | static Limit, arr: openArray[T], res: var Digest) =
  chunkedHashTreeRoot(
    height, arr, 0.Limit ..< (1.Limit shl height), topLayer = 0, res)

func bitListHashTreeRoot(
    height: Limit | static Limit, x: openArray[byte],
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  # TODO: Switch to a simpler BitList representation and
  #       replace this with `chunkedHashTreeRoot`
  var
    merkleizer = createMerkleizer2(height, topLayer, internalParam = true)
    totalBytes = x.len
    lastCorrectedByte = x[^1]

  if lastCorrectedByte == byte(1):
    if totalBytes == 1:
      # This is an empty bit list.
      # It should be hashed as a tree containing all zeros:
      res = zeroHashes[merkleizer.topIndex]
      return

    totalBytes -= 1
    lastCorrectedByte = x[^2]
  else:
    let markerPos = log2trunc(lastCorrectedByte)
    lastCorrectedByte.clearBit(markerPos)

  var
    bytesInLastChunk = totalBytes mod bytesPerChunk
    fullChunks = totalBytes div bytesPerChunk

  if bytesInLastChunk == 0:
    fullChunks -= 1
    bytesInLastChunk = 32

  for i in chunks.a .. min(chunks.b, fullChunks - 1):
    let
      chunkStartPos = i.int * bytesPerChunk
      chunkEndPos = chunkStartPos + bytesPerChunk - 1

    addChunk(merkleizer, x.toOpenArray(chunkStartPos, chunkEndPos))

  if fullChunks in chunks:
    var
      lastChunk: array[bytesPerChunk, byte]
      chunkStartPos = fullChunks * bytesPerChunk

    for i in 0 .. bytesInLastChunk - 2:
      lastChunk[i] = x[chunkStartPos + i]

    lastChunk[bytesInLastChunk - 1] = lastCorrectedByte

    addChunk(merkleizer, lastChunk.toOpenArray(0, bytesInLastChunk - 1))

  getFinalHash(merkleizer, res)

func bitListHashTreeRoot(
    height: Limit | static Limit, x: BitSeq,
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  bitListHashTreeRoot(height, bytes(x), chunks, topLayer, res)

template bitListHashTreeRoot(
    height: Limit | static Limit, x: BitSeq | openArray[byte], res: var Digest) =
  bitListHashTreeRoot(
    height, x, 0.Limit ..< (1.Limit shl height), topLayer = 0, res)

template progressiveRange(
    x: BitSeq, firstIdx: Limit, hasPartialChunks: bool): openArray[byte] =
  x.bytes.toOpenArray(
    32 * firstIdx.int,
    min(
      32 * ((firstIdx.int shl 2) or 1) - 1,
      x.bytes.high - (if hasPartialChunks: 0 else: 1)))

func doProgressiveMerkleizeFields(
    allFieldValues: openArray[NimNode],
    x, res: NimNode): NimNode {.compileTime.} =
  let contentsHash = nskVar.genSym "contentsHash"
  var code = newStmtList()
  code.add quote do:
    `res`.reset()
    var `contentsHash` {.noinit.}: Digest
  let totalChunkCount = allFieldValues.len
  var (firstIdx, depth) = totalChunkCount.progressiveBottom()
  while depth > 0:
    firstIdx = firstIdx shr 2
    dec depth
    code.add allFieldValues.progressiveRangePreChunked(firstIdx)
      .doMerkleizeFields(newLit((depth shl 1) + 1), x, contentsHash)
    code.add quote do: mergeBranches(`contentsHash`, `res`, `res`)
  code

template genProgressiveMerkleizeFieldsImpls(
    B: typedesc[object|tuple], F: typedesc[string|int]): untyped =
  macro progressiveMerkleizeFieldsImpl[T: B](
      fieldNames: static[openArray[Opt[F]]],
      x: T, res: var Digest): untyped =
    fieldNames.allFieldValues(x).doProgressiveMerkleizeFields(x, res)

genProgressiveMerkleizeFieldsImpls(object, string)
genProgressiveMerkleizeFieldsImpls(tuple, int)

func progressiveMerkleizeFields[T: object|tuple](x: T, res: var Digest) =
  T.allFieldNames.progressiveMerkleizeFieldsImpl(x, res)

func progressiveChunkedHashTreeRoot[T](x: seq[T], res: var Digest) =
  res.reset()
  var (firstIdx, depth) = x.totalChunkCount.progressiveBottom()
  while depth > 0:
    firstIdx = firstIdx shr 2
    dec depth
    var contentsHash {.noinit.}: Digest
    chunkedHashTreeRoot(
      (depth shl 1) + 1, x.progressiveRange(firstIdx), contentsHash)
    mergeBranches(contentsHash, res, res)

func chunkedBitListHashTreeRoot(
    atBottom: var bool, height: Limit, x: openArray[byte],
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  if x.len <= chunks.a * 32:
    res = zeroHashes[height - 1 - topLayer]
  elif atBottom:
    bitListHashTreeRoot(height, x, chunks, topLayer, res)
  else:
    chunkedHashTreeRoot(height, x, chunks, topLayer, res)
  atBottom = false

template chunkedBitListHashTreeRoot(
    atBottom: var bool, height: Limit, x: openArray[byte], res: var Digest) =
  atBottom.chunkedBitListHashTreeRoot(
    height, x, 0.Limit ..< (1.Limit shl height), topLayer = 0, res)

func progressiveBitListHashTreeRoot(x: BitSeq, res: var Digest) =
  res.reset()
  let
    bitlen = x.len.Limit
    totalChunkCount = (bitlen + 255) div 256
    hasPartialChunks = bitlen.uint.uint8 != 0x00
  var
    (firstIdx, depth) = totalChunkCount.progressiveBottom()
    atBottom = hasPartialChunks
  while depth > 0:
    firstIdx = firstIdx shr 2
    dec depth
    var contentsHash {.noinit.}: Digest
    atBottom.chunkedBitListHashTreeRoot(
      (depth shl 1) + 1,
      x.progressiveRange(firstIdx, hasPartialChunks),
      contentsHash)
    mergeBranches(contentsHash, res, res)

func mixInActiveFields(root: Digest, T: typedesc, res: var Digest) =
  const activeFields = static(T.activeFields)
  mergeBranches(root, activeFields.hash_tree_root(), res)

func maxChunksCount(T: type, maxLen: Limit): Limit =
  when T is BitArray|BitList:
    (maxLen + bitsPerChunk - 1) div bitsPerChunk
  elif T is array|List:
    maxChunkIdx(ElemType(T), maxLen)
  else:
    unsupported T # This should never happen

template progressiveBodyImpl(
    allFieldValues: openArray[NimNode],
    depthSym: NimNode, body: untyped): untyped =
  let totalChunkCount = allFieldValues.len
  var
    (firstIdx, depth) = totalChunkCount.progressiveBottom()
    code {.inject.} = nnkCaseStmt.newTree(depthSym)
  while depth > 0:
    firstIdx = firstIdx shr 2
    dec depth
    let
      height {.inject, used.} = newLit((depth shl 1) + 1)
      firstIdx {.inject.} = firstIdx
      impl = body
    code.add nnkOfBranch.newTree(newLit(depth), impl)
  code.add nnkElse.newTree quote do:
    raiseAssert "Unexpected depth"
  code

func doProgressiveRoot(
    allFieldValues: openArray[NimNode],
    depthSym, x, res: NimNode): NimNode {.compileTime.} =
  allFieldValues.progressiveBodyImpl(depthSym):
    allFieldValues.progressiveRangePreChunked(firstIdx)
      .doMerkleizeFields(height, x, res)

func doProgressiveChunks(
    allFieldValues: openArray[NimNode],
    depthSym, x, chunks, indexLayer, res: NimNode): NimNode {.compileTime.} =
  allFieldValues.progressiveBodyImpl(depthSym):
    allFieldValues.progressiveRangePreChunked(firstIdx)
      .doMerkleizeFields(height, x, chunks, indexLayer, res)

func doMulti(
    fieldValues: openArray[NimNode],
    x, chunk, batch, slice, atLayer: NimNode
): NimNode {.compileTime.} =
  var body = nnkCaseStmt.newTree(chunk)
  for i, fieldValue in fieldValues:
    body.add nnkOfBranch.newTree(newLit(i), quote do:
      ? hash_tree_root_multi(
        `fieldValue`, `batch`, `slice`, `atLayer`))
  body.add nnkElse.newTree quote do:
    return unsupportedIndex
  body

func doProgressiveMulti(
    allFieldValues: openArray[NimNode],
    depthSym, x, chunk, batch, slice, atLayer: NimNode
): NimNode {.compileTime.} =
  allFieldValues.progressiveBodyImpl(depthSym):
    allFieldValues.progressiveRangePreChunked(firstIdx).doMulti(
      x, chunk, batch, slice, atLayer)

template genGetBodyImpls(
    B: typedesc[object|tuple], F: typedesc[string|int]): untyped =
  macro progressiveRoot[T: B](
      fieldNames: static[openArray[Opt[F]]],
      depth: Limit, x: T, res: var Digest): untyped =
    fieldNames.allFieldValues(x).doProgressiveRoot(depth, x, res)

  macro progressiveChunks[T: B](
      fieldNames: static[openArray[Opt[F]]],
      depth: Limit, x: T, chunks: Slice[Limit],
      indexLayer: int, res: var Digest): untyped =
    fieldNames.allFieldValues(x).doProgressiveChunks(
      depth, x, chunks, indexLayer, res)

  macro multi[T: B](
      fieldNames: static[openArray[Opt[F]]],
      x: T, chunk: Limit,
      batch: BatchRequest, slice: Slice[int], atLayer: int): untyped =
    fieldNames.allFieldValues(x).doMulti(
      x, chunk, batch, slice, atLayer)

  macro progressiveMulti[T: B](
      fieldNames: static[openArray[Opt[F]]],
      depth: Limit, x: T, chunk: Limit,
      batch: BatchRequest, slice: Slice[int], atLayer: int): untyped =
    fieldNames.allFieldValues(x).doProgressiveMulti(
      depth, x, chunk, batch, slice, atLayer)

genGetBodyImpls(object, string)
genGetBodyImpls(tuple, int)

func hashTreeRootCachedPtr(x: HashSeq, depth: int, vIdx: int64): ptr Digest

func progressive_hash_tree_root_multi[T: BitSeq|seq|HashSeq|object|tuple](
    x: T,
    batch: BatchRequest,
    slice: Slice[int],
    atLayer: int): Result[void, string] =
  when T is BitSeq:
    let
      bitlen = x.len.Limit
      totalChunkCount = (bitlen + 255) div 256
      hasPartialChunks = bitlen.uint.uint8 != 0x00
    var atBottom = hasPartialChunks
  elif T is seq|HashSeq:
    type E = typeof toSszType(declval ElemType(typeof(x)))
    let totalChunkCount = x.totalChunkCount
  else:
    static: doAssert T.isProgressiveContainer
    const
      fieldNames = T.allFieldNames
      totalChunkCount = fieldNames.len
  var j = slice.b
  when T isnot HashSeq:
    let index = indexAt(j)
    var
      needAll = (index + 1).countOnes == 1
      res {.noinit.}: Digest
    if needAll:
      res.reset()
  var (firstIdx, depth) = totalChunkCount.progressiveBottom()
  while depth > 0 and j >= slice.a:
    firstIdx = firstIdx shr 2
    dec depth
    let
      nextProgressivePrefix = ((2 shl (depth + 1)) - 1).GeneralizedIndex
      depthSlice = block:
        var i = j
        while i >= slice.a:
          let
            index = indexAt(i)
            indexLayer = log2trunc(index)
          if indexLayer <= depth:
            break
          if index == nextProgressivePrefix:
            when T is HashSeq:
              if depth < x.hashes.high:
                rootAt(i) = hashTreeRootCachedPtr(x, depth.int + 1, 0)[]
              else:
                rootAt(i) = zeroHashes[0]
            else:
              doAssert needAll and i == j
              rootAt(i) = res
              needAll = false
            dec j
          else:
            let prefix = index shr (indexLayer - 1 - depth)
            if prefix == nextProgressivePrefix:
              return unsupportedIndex
            if prefix != nextProgressivePrefix - 1:
              break
          dec i
        i + 1 .. j
    if depthSlice.a <= depthSlice.b:
      when T isnot HashSeq:
        doAssert not needAll
      let
        totalChunks = ((firstIdx shl 2) or 1) - firstIdx
        firstChunkIndex = totalChunks.uint64
        chunkLayer = log2trunc(firstChunkIndex)
        atLayer = atLayer + depth.int + 1
      var i = depthSlice.a
      while i <= depthSlice.b:
        let
          index = indexAt(i)
          indexLayer = log2trunc(index)
          isSpecialCase =
            when T is HashSeq:
              indexLayer < chunkLayer
            else:
              index == 1.GeneralizedIndex
        if isSpecialCase:
          when T is HashSeq:
            rootAt(i) = hashTreeRootCachedPtr(x, depth.int, index.int64)[]
          else:
            let height {.used.} = (depth shl 1) + 1
            when T is BitSeq:
              atBottom.chunkedBitListHashTreeRoot(
                height, x.progressiveRange(firstIdx, hasPartialChunks),
                rootAt(i))
            elif T is seq|HashSeq:
              chunkedHashTreeRoot(
                height, x.progressiveRange(firstIdx), rootAt(i))
            else:
              fieldNames.progressiveRoot(depth, x, rootAt(i))
          inc i
        elif indexLayer <= chunkLayer:
          let
            height {.used.} = (depth shl 1) + 1
            chunks = chunksForIndex(index)
          when T is BitSeq:
            atBottom.chunkedBitListHashTreeRoot(
              height, x.progressiveRange(firstIdx, hasPartialChunks),
              chunks, indexLayer, rootAt(i))
          elif T is seq|HashSeq:
            chunkedHashTreeRoot(
              height, x.progressiveRange(firstIdx),
              chunks, indexLayer, rootAt(i))
          else:
            fieldNames.progressiveChunks(
              depth, x, chunks, indexLayer, rootAt(i))
          inc i
        else:
          const alwaysError =
            when T is BitSeq:
              true
            elif T is seq|HashSeq:
              E is BasicType
            else:
              false
          when alwaysError:
            return unsupportedIndex
          else:
            let chunk = chunkContainingIndex(index)
            if firstIdx + chunk >= totalChunkCount:
              return unsupportedIndex
            var k = i
            while k <= j:
              let
                index = indexAt(k)
                indexLayer = log2trunc(index)
              if indexLayer <= chunkLayer or
                  chunkContainingIndex(index) != chunk:
                break
              inc k
            when T is seq|HashSeq:
              ? hash_tree_root_multi(
                x[firstIdx + chunk], batch, i ..< k,
                atLayer + chunkLayer)
            else:
              fieldNames.progressiveMulti(
                depth, x, chunk, batch, i ..< k,
                atLayer + chunkLayer)
            i = k
      j = depthSlice.a - 1
    else:
      when T isnot HashSeq:
        if needAll:
          var contentsHash {.noinit.}: Digest
          let height {.used.} = (depth shl 1) + 1
          when T is BitSeq:
            atBottom.chunkedBitListHashTreeRoot(
              height, x.progressiveRange(firstIdx, hasPartialChunks), contentsHash)
          elif T is seq:
            chunkedHashTreeRoot(height, x.progressiveRange(firstIdx), contentsHash)
          else:
            fieldNames.progressiveRoot(depth, x, contentsHash)
          mergeBranches(contentsHash, res, res)
      else:
        discard
    when T is BitSeq:
      atBottom = false
  if j >= slice.a:
    return unsupportedIndex
  ok()

func hashTreeRootAux[T](x: T, res: var Digest) =
  mixin hash_tree_root, toSszType
  when T is bool|char:
    res.data[0] = byte(x)
    zeroMem(addr res.data[1], sizeof(res.data) - sizeof(x))
  elif T is UintN:
    when cpuEndian == bigEndian:
      res.data[0..<sizeof(x)] = toBytesLE(x)
    else:
      copyMem(addr res.data[0], unsafeAddr x, sizeof x)
    when sizeof(x) < sizeof(res.data):
      zeroMem(addr res.data[sizeof x], sizeof(res.data) - sizeof(x))
  elif T is BitArray:
    hashTreeRootAux(x.bytes, res)
  elif T is BitList:
    const totalChunks = maxChunksCount(T, x.maxLen)
    var contentsHash {.noinit.}: Digest
    bitListHashTreeRoot(binaryTreeHeight totalChunks, BitSeq x, contentsHash)
    mixInLength(contentsHash, x.len, res)
  elif T is array:
    type E = ElemType(T)
    when E is BasicType and sizeof(T) <= sizeof(res.data):
      when sizeof(E) == 1 or cpuEndian == littleEndian:
        copyMem(addr res.data[0], unsafeAddr x, sizeof x)
      else:
        var pos = 0
        for e in x:
          writeBytesLE(res.data, pos, e)
          pos += sizeof(E)
      when sizeof(x) < sizeof(res.data):
        zeroMem(addr res.data[sizeof x], sizeof(res.data) - sizeof(x))
    else:
      trs "FIXED TYPE; USE CHUNK STREAM"
      const totalChunks = maxChunksCount(T, x.len)
      chunkedHashTreeRoot(binaryTreeHeight totalChunks, x, res)
  elif T is List:
    const totalChunks = maxChunksCount(T, x.maxLen)
    var contentsHash {.noinit.}: Digest
    chunkedHashTreeRoot(binaryTreeHeight totalChunks, asSeq x, contentsHash)
    mixInLength(contentsHash, x.len, res)
  elif T is BitSeq|seq:
    when T is BitSeq:
      x.progressiveBitListHashTreeRoot(res)
    else:
      x.progressiveChunkedHashTreeRoot(res)
    mixInLength(res, x.len, res)
  elif T.isUnion:
    x.unionHashTreeRoot(res)
    mixInSelector(res, x.unionSelector.ord.uint8, res)
  elif T is object|tuple:
    when T.isProgressiveContainer:
      x.progressiveMerkleizeFields(res)
      mixInActiveFields(res, T, res)
    else:
      trs "MERKLEIZING FIELDS"
      const totalChunks = totalSerializedFields(T)
      merkleizeFields(binaryTreeHeight totalChunks, x, res)
  else:
    unsupported T

func hashTreeRootAux[T](
    x: T,
    batch: BatchRequest,
    slice: Slice[int],
    atLayer: int): Result[void, string] =
  mixin hash_tree_root, toSszType
  when T is BasicType:
    for i in slice:
      if indexAt(i) != 1.GeneralizedIndex: return unsupportedIndex
      hashTreeRootAux(x, rootAt(i))
  elif T is BitArray:
    ? hashTreeRootAux(x.bytes, batch, slice, atLayer)
  elif T is BitList:
    const
      totalChunks = maxChunksCount(T, x.maxLen)
      firstChunkIndex = nextPow2(totalChunks.uint64)
      chunkLayer = log2trunc(firstChunkIndex)
    var i = slice.a
    while i <= slice.b:
      let
        index = indexAt(i)
        indexLayer = log2trunc(index)
      if index == 1.GeneralizedIndex:
        var contentsHash {.noinit.}: Digest
        bitListHashTreeRoot(
          binaryTreeHeight totalChunks, BitSeq x, contentsHash)
        mixInLength(contentsHash, x.len, rootAt(i))
        inc i
      elif index == 3.GeneralizedIndex:
        hashTreeRootAux(x.len.uint64, rootAt(i))
        inc i
      elif index == 2.GeneralizedIndex:
        bitListHashTreeRoot(
          binaryTreeHeight totalChunks, BitSeq x, rootAt(i))
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
        let
          atLayer = atLayer + 1
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          bitListHashTreeRoot(
            binaryTreeHeight totalChunks, BitSeq x,
            chunks, indexLayer, rootAt(i))
          inc i
        else: return unsupportedIndex
      else: return unsupportedIndex
  elif T is array:
    type E = typeof toSszType(declval ElemType(T))
    when E is BasicType and sizeof(T) <= sizeof(rootAt(0).data):
      for i in slice:
        if indexAt(i) != 1.GeneralizedIndex: return unsupportedIndex
        hashTreeRootAux(x, rootAt(i))
    else:
      trs "FIXED TYPE; USE CHUNK STREAM"
      const
        totalChunks = maxChunksCount(T, x.len)
        firstChunkIndex = nextPow2(totalChunks.uint64)
        chunkLayer = log2trunc(firstChunkIndex)
      var i = slice.a
      while i <= slice.b:
        let
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if index == 1.GeneralizedIndex:
          chunkedHashTreeRoot(binaryTreeHeight totalChunks, x, rootAt(i))
          inc i
        elif indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          chunkedHashTreeRoot(binaryTreeHeight totalChunks, x, chunks, indexLayer, rootAt(i))
          inc i
        else:
          when (typeof toSszType(declval ElemType(typeof(x)))) is BasicType:
            return unsupportedIndex
          else:
            let chunk = chunkContainingIndex(index)
            if chunk >= x.len: return unsupportedIndex
            var j = i + 1
            while j <= slice.b:
              let
                index = indexAt(j)
                indexLayer = log2trunc(index)
              if indexLayer <= chunkLayer or
                  chunkContainingIndex(index) != chunk:
                break
              inc j
            ? hash_tree_root_multi(x[chunk], batch, i ..< j,
                                   atLayer + chunkLayer)
            i = j
  elif T is List:
    const
      totalChunks = maxChunksCount(T, x.maxLen)
      firstChunkIndex = nextPow2(totalChunks.uint64)
      chunkLayer = log2trunc(firstChunkIndex)
    var i = slice.a
    while i <= slice.b:
      let
        index = indexAt(i)
        indexLayer = log2trunc(index)
      if index == 1.GeneralizedIndex:
        var contentsHash {.noinit.}: Digest
        chunkedHashTreeRoot(binaryTreeHeight totalChunks, asSeq x, contentsHash)
        mixInLength(contentsHash, x.len, rootAt(i))
        inc i
      elif index == 3.GeneralizedIndex:
        hashTreeRootAux(x.len.uint64, rootAt(i))
        inc i
      elif index == 2.GeneralizedIndex:
        chunkedHashTreeRoot(binaryTreeHeight totalChunks, asSeq x, rootAt(i))
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
        let
          atLayer = atLayer + 1
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          chunkedHashTreeRoot(
            binaryTreeHeight totalChunks, asSeq x, chunks, indexLayer, rootAt(i))
          inc i
        else:
          when (typeof toSszType(declval ElemType(typeof(x)))) is BasicType:
            return unsupportedIndex
          else:
            let chunk = chunkContainingIndex(index)
            if chunk >= x.len: return unsupportedIndex
            var j = i + 1
            while j <= slice.b:
              let
                index = indexAt(j)
                indexLayer = log2trunc(index)
              if indexLayer <= chunkLayer or
                  chunkContainingIndex(index) != chunk:
                break
              inc j
            ? hash_tree_root_multi(x[chunk], batch, i ..< j,
                                   atLayer + chunkLayer)
            i = j
      else: return unsupportedIndex
  elif T.isUnion:
    var i = slice.a
    while i <= slice.b:
      let
        index = indexAt(i)
        indexLayer = log2trunc(index)
      if index == 1.GeneralizedIndex:
        var contentsHash {.noinit.}: Digest
        x.unionHashTreeRoot(contentsHash)
        mixInSelector(contentsHash, x.unionSelector.ord.uint8, rootAt(i))
        inc i
      elif index == 3.GeneralizedIndex:
        hashTreeRootAux(x.unionSelector.ord.uint8, rootAt(i))
        inc i
      elif index == 2.GeneralizedIndex:
        x.unionHashTreeRoot(rootAt(i))
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
        var isSome = false
        x.withFieldPairs(key, val):
          when key != T.unionSelectorKey:
            doAssert not isSome
            isSome = true
            var j = i + 1
            while j <= slice.b:
              let
                index = indexAt(j)
                indexLayer = log2trunc(index)
              if indexLayer <= 1 or
                  (index shr (indexLayer - 1)) != 2.GeneralizedIndex:
                break
              inc j
            let atLayer = atLayer + 1
            ? val.hash_tree_root_multi(
              batch, i ..< j, atLayer)
            i = j
        if not isSome:
          return unsupportedIndex
      else:
        return unsupportedIndex
  elif T is BitSeq|seq|object|tuple:
    const usesProgressiveShape =
      when T is BitSeq|seq:
        true
      elif T.isProgressiveContainer:
        true
      else:
        false
    when usesProgressiveShape:
      var i = slice.a
      while i <= slice.b:
        let
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if index == 1.GeneralizedIndex:
          var contentsHash {.noinit.}: Digest
          when T is BitSeq:
            x.progressiveBitListHashTreeRoot(contentsHash)
          elif T is seq:
            x.progressiveChunkedHashTreeRoot(contentsHash)
          else:
            x.progressiveMerkleizeFields(contentsHash)
          when T is BitSeq|seq:
            mixInLength(contentsHash, x.len, rootAt(i))
          else:
            mixInActiveFields(contentsHash, T, rootAt(i))
          inc i
        elif index == 3.GeneralizedIndex:
          when T is BitSeq|seq:
            hashTreeRootAux(x.len.uint64, rootAt(i))
          else:
            const activeFields = static(T.activeFields)
            rootAt(i) = activeFields.hash_tree_root()
          inc i
        elif index == 2.GeneralizedIndex:
          when T is BitSeq:
            x.progressiveBitListHashTreeRoot(rootAt(i))
          elif T is seq:
            x.progressiveChunkedHashTreeRoot(rootAt(i))
          else:
            x.progressiveMerkleizeFields(rootAt(i))
          inc i
        elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
          var j = i + 1
          while j <= slice.b:
            let
              index = indexAt(j)
              indexLayer = log2trunc(index)
            if indexLayer <= 1 or
                (index shr (indexLayer - 1)) != 2.GeneralizedIndex:
              break
            inc j
          let atLayer = atLayer + 1
          ? x.progressive_hash_tree_root_multi(
            batch, i ..< j, atLayer)
          i = j
        else:
          return unsupportedIndex
    else:
      trs "MERKLEIZING FIELDS"
      const
        fieldNames = T.allFieldNames
        totalChunks = fieldNames.len
        firstChunkIndex = nextPow2(totalChunks.uint64)
        chunkLayer = log2trunc(firstChunkIndex)
        treeHeight = binaryTreeHeight(totalChunks)
      var i = slice.a
      while i <= slice.b:
        let
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if index == 1.GeneralizedIndex:
          rootAt(i) = x.hash_tree_root()
          inc i
        elif indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          merkleizeFields(treeHeight, x, chunks, indexLayer, rootAt(i))
          inc i
        else:
          let chunk = chunkContainingIndex(index)
          var j = i + 1
          while j <= slice.b:
            let
              index = indexAt(j)
              indexLayer = log2trunc(index)
            if indexLayer <= chunkLayer or
                chunkContainingIndex(index) != chunk:
              break
            inc j
          fieldNames.multi(
            x, chunk, batch, i ..< j,
            atLayer + chunkLayer)
          i = j
  else:
    unsupported T
  ok()

func singleDataHash[T](data: openArray[T], res: var Digest) =
  mixin hash_tree_root, toSszType
  if data.len == 0:
    res.reset()
  else:
    type S = typeof toSszType(declval T)
    when S is BasicType | Digest:
      when cpuEndian == bigEndian:
        unsupported T # No bigendian support here!

      let
        bytes = cast[ptr UncheckedArray[byte]](unsafeAddr data[0])
        byteLen = data.len * sizeof(T)
        nbytes = min(byteLen, 32)
      res.data[0 ..< nbytes] = bytes.toOpenArray(0, nbytes - 1)
      res.data[nbytes ..< 32] = zero64.toOpenArray(nbytes, 31)
    else:
      res = hash_tree_root(data[0])

func mergedDataHash[T](
    data: openArray[T], maxChunks: int64, chunkIdx: int64, res: var Digest) =
  # The merged hash of the data at `chunkIdx` and `chunkIdx + 1`
  mixin hash_tree_root, toSszType
  trs "DATA HASH ", chunkIdx, " ", data.len
  type S = typeof toSszType(declval T)
  when S is BasicType | Digest:
    when cpuEndian == bigEndian:
      unsupported T # No bigendian support here!

    let
      bytes = cast[ptr UncheckedArray[byte]](unsafeAddr data[0])
      byteIdx = chunkIdx * bytesPerChunk
      byteLen = data.len * sizeof(T)

    if byteIdx >= byteLen:
      res = zeroHashes[1]
    else:
      let
        nbytes = min(byteLen - byteIdx, 64)
        padding = 64 - nbytes

      digest(
        toOpenArray(bytes, int(byteIdx), int(byteIdx + nbytes - 1)),
        toOpenArray(zero64, 0, int(padding - 1)),
        res)
  else:
    if chunkIdx + 1 > data.len():
      res = zeroHashes[maxChunks.layer]
    elif chunkIdx + 1 == data.len():
      let left {.noinit.} = hash_tree_root(data[chunkIdx])
      mergeBranches(left, zeroDigest, res)
    else:
      let
        left {.noinit.} = hash_tree_root(data[chunkIdx])
        right {.noinit.} = hash_tree_root(data[chunkIdx + 1])

      mergeBranches(left, right, res)

template refreshHash[T](
    data: openArray[T],
    maxChunks: int64,
    vIdxParam: int64,
    res: var Digest,
    cachedPtrImpl: untyped,
    params: varargs[untyped]): untyped =
  # The merged hash of the data at `vIdx` and `vIdx + 1`
  let vIdx = vIdxParam
  if maxChunks == 1:
    data.singleDataHash(res)
  elif vIdx >= maxChunks:
    let dataIdx = vIdx - maxChunks
    data.mergedDataHash(maxChunks, dataIdx, res)
  else:
    mergeBranches(
      unpackArgs(cachedPtrImpl, [data, maxChunks, vIdx, params])[],
      unpackArgs(cachedPtrImpl, [data, maxChunks, vIdx + 1, params])[],
      res)

func hashTreeRootCachedPtrArray[T](
    data: openArray[T],
    maxChunks: int64,
    vIdx: int64,
    hashes: openArray[Digest]): ptr Digest =
  # Return a short-lived pointer to the given digest - a pointer is used because
  # `var` and `lent` returns don't work for the constant zero hashes
  # The instance must not be mutated! This is an internal low-level API.

  doAssert vIdx >= 1, "Only valid for flat Merkle tree indices"
  let px = unsafeAddr hashes[vIdx]
  if not isCached(hashes[vIdx]):
    # TODO oops. so much for maintaining non-mutability.
    data.refreshHash(
      maxChunks, vIdx * 2, px[], hashTreeRootCachedPtrArray, hashes)
  px

func hashTreeRootCachedPtr(x: HashArray, vIdx: int64): ptr Digest =
  x.data.hashTreeRootCachedPtrArray(
    x.maxChunks, vIdx, x.hashes)

func hashTreeRootCachedPtrList[T](
    data: openArray[T],
    maxChunks: int64,
    vIdx: int64,
    hashes: openArray[Digest],
    indices: openArray[int64]): ptr Digest =
  # Return a short-lived pointer to the given digest - a pointer is used because
  # `var` and `lent` returns don't work for the constant zero hashes
  # The instance must not be mutated! This is an internal low-level API.

  doAssert vIdx >= 1, "Only valid for flat Merkle tree indices"

  let
    layer = layer(vIdx)
    idxInLayer = vIdx - (1'i64 shl layer)
    layerIdx = idxInLayer + indices[layer]

  trs "GETTING ", vIdx, " ", layerIdx, " ", layer, " ", indices.len

  doAssert layer < maxChunks.layer or layer == 0
  if layerIdx >= indices[layer + 1]:
    trs "ZERO ", indices[layer], " ", indices[layer + 1]
    unsafeAddr zeroHashes[maxChunks.layer - layer]
  else:
    let px = unsafeAddr hashes[layerIdx]
    if not isCached(px[]):
      trs "REFRESHING ", vIdx, " ", layerIdx, " ", layer
      # TODO oops. so much for maintaining non-mutability.
      data.refreshHash(
        maxChunks, vIdx * 2, px[], hashTreeRootCachedPtrList, hashes, indices)
    else:
      trs "CACHED ", layerIdx
    px

func hashTreeRootCachedPtr(x: HashList, vIdx: int64): ptr Digest =
  asSeq(x.data).hashTreeRootCachedPtrList(
    x.maxChunks, vIdx, x.hashes, x.indices)

func hashTreeRootCachedPtr(x: HashSeq, depth: int, vIdx: int64): ptr Digest =
  # Return a short-lived pointer to the given digest - a pointer is used because
  # `var` and `lent` returns don't work for the constant zero hashes
  # The instance must not be mutated! This is an internal low-level API.
  if vIdx == 0:
    let px = unsafeAddr x.hashes[depth][0]
    if not isCached(px[]):
      # TODO oops. so much for maintaining non-mutability.
      mergeBranches(
        x.hashTreeRootCachedPtr(depth, 1)[],
        if depth < x.hashes.high:
          x.hashTreeRootCachedPtr(depth + 1, 0)[]
        else:
          zeroHashes[0],
        px[])
    px
  else:
    var firstIdx = 0
    for _ in 0 ..< depth:
      firstIdx = (firstIdx shl 2) or 1
    let maxChunks = 1 shl (depth shl 1)
    if depth < x.hashes.high:
      x.data.progressiveRange(firstIdx).hashTreeRootCachedPtrArray(
        maxChunks, vIdx, x.hashes[depth])
    else:
      x.data.progressiveRange(firstIdx).hashTreeRootCachedPtrList(
        maxChunks, vIdx, x.hashes[depth], x.indices)

func hashTreeRootCached(x: HashArray): Digest {.noinit.} =
  hashTreeRootCachedPtr(x, 1)[] # Array does not use idx 0

func hashTreeRootCached(x: HashList): Digest {.noinit.} =
  if x.data.len == 0:
    mergeBranches(
      zeroHashes[x.maxDepth], zeroHashes[0],
      result) # mixInLength with 0!
  else:
    if not isCached(x.hashes[0]):
      # TODO oops. so much for maintaining non-mutability.
      let px = unsafeAddr x.hashes[0]
      mixInLength(hashTreeRootCachedPtr(x, 1)[], x.data.len, px[])

    result = x.hashes[0]

func hashTreeRootCached(x: HashSeq): Digest {.noinit.} =
  if x.data.len == 0:
    zeroHashes[1]
  else:
    if not isCached(x.root):
      # TODO oops. so much for maintaining non-mutability.
      let px = unsafeAddr x.root
      mixInLength(hashTreeRootCachedPtr(x, 0, 0)[], x.data.len, px[])
    x.root

func hashTreeRootCached(
    x: HashArray,
    batch: BatchRequest,
    slice: Slice[int],
    atLayer: int): Result[void, string] =
  mixin toSszType
  const
    totalChunks = x.maxChunks
    firstChunkIndex = nextPow2(totalChunks.uint64)
    chunkLayer = log2trunc(firstChunkIndex)
  var i = slice.a
  while i <= slice.b:
    let
      index = indexAt(i)
      indexLayer = log2trunc(index)
    if index == 1.GeneralizedIndex:
      rootAt(i) = hashTreeRootCached(x)
      inc i
    elif indexLayer == chunkLayer:
      let chunks = chunksForIndex(index)
      chunkedHashTreeRoot(
        binaryTreeHeight totalChunks, x.data, chunks, indexLayer, rootAt(i))
      inc i
    elif indexLayer < chunkLayer:
      rootAt(i) = hashTreeRootCachedPtr(x, index.int64)[]
      inc i
    else:
      when (typeof toSszType(declval ElemType(typeof(x)))) is BasicType:
        return unsupportedIndex
      else:
        let chunk = chunkContainingIndex(index)
        if chunk >= x.len: return unsupportedIndex
        var j = i + 1
        while j <= slice.b:
          let
            index = indexAt(j)
            indexLayer = log2trunc(index)
          if indexLayer <= chunkLayer or
              chunkContainingIndex(index) != chunk:
            break
          inc j
        ? hash_tree_root_multi(x[chunk], batch, i ..< j,
                               atLayer + chunkLayer)
        i = j
  ok()

func hashTreeRootCached(
    x: HashList,
    batch: BatchRequest,
    slice: Slice[int],
    atLayer: int): Result[void, string] =
  mixin toSszType
  const
    totalChunks = x.maxChunks
    firstChunkIndex = nextPow2(totalChunks.uint64)
    chunkLayer = log2trunc(firstChunkIndex)
  var i = slice.a
  while i <= slice.b:
    let
      index = indexAt(i)
      indexLayer = log2trunc(index)
    if index == 1.GeneralizedIndex:
      rootAt(i) = hashTreeRootCached(x)
      inc i
    elif index == 3.GeneralizedIndex:
      hashTreeRootAux(x.len.uint64, rootAt(i))
      inc i
    elif index == 2.GeneralizedIndex:
      rootAt(i) = hashTreeRootCachedPtr(x, 1)[]
      inc i
    elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
      let
        atLayer = atLayer + 1
        index = indexAt(i)
        indexLayer = log2trunc(index)
      if indexLayer == chunkLayer:
        let chunks = chunksForIndex(index)
        chunkedHashTreeRoot(
          binaryTreeHeight totalChunks, asSeq x.data, chunks, indexLayer, rootAt(i))
        inc i
      elif indexLayer < chunkLayer:
        rootAt(i) = hashTreeRootCachedPtr(x, index.int64)[]
        inc i
      else:
        when (typeof toSszType(declval ElemType(typeof(x)))) is BasicType:
          return unsupportedIndex
        else:
          let chunk = chunkContainingIndex(index)
          if chunk >= x.len: return unsupportedIndex
          var j = i + 1
          while j <= slice.b:
            let
              index = indexAt(j)
              indexLayer = log2trunc(index)
            if indexLayer <= chunkLayer or
                chunkContainingIndex(index) != chunk:
              break
            inc j
          ? hash_tree_root_multi(x[chunk], batch, i ..< j,
                                 atLayer + chunkLayer)
          i = j
    else: return unsupportedIndex
  ok()

func hashTreeRootCached(
    x: HashSeq,
    batch: BatchRequest,
    slice: Slice[int],
    atLayer: int): Result[void, string] =
  var i = slice.a
  while i <= slice.b:
    let
      index = indexAt(i)
      indexLayer = log2trunc(index)
    if index == 1.GeneralizedIndex:
      rootAt(i) = hashTreeRootCached(x)
      inc i
    elif index == 3.GeneralizedIndex:
      hashTreeRootAux(x.len.uint64, rootAt(i))
      inc i
    elif index == 2.GeneralizedIndex:
      rootAt(i) =
        if x.len > 0:
          hashTreeRootCachedPtr(x, 0, 0)[]
        else:
          zeroHashes[0]
      inc i
    elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
      var j = i + 1
      while j <= slice.b:
        let
          index = indexAt(j)
          indexLayer = log2trunc(index)
        if indexLayer <= 1 or
            (index shr (indexLayer - 1)) != 2.GeneralizedIndex:
          break
        inc j
      let atLayer = atLayer + 1
      ? x.progressive_hash_tree_root_multi(
        batch, i ..< j, atLayer)
      i = j
    else:
      return unsupportedIndex
  ok()

func hash_tree_root*(x: auto): Digest {.noinit.} =
  trs "STARTING HASH TREE ROOT FOR TYPE ", name(typeof(x))
  mixin toSszType

  when x is HashArray|HashList|HashSeq:
    result = hashTreeRootCached(x)
  else:
    hashTreeRootAux(toSszType(x), result)

  trs "HASH TREE ROOT FOR ", name(typeof(x)), " = ", "0x", $result

# Note: If this function is also called `hash_tree_root`, the Nim compiler may
# produce incorrect code when calling it, e.g., when called by this overload:
#   func hash_tree_root*(
#       x: auto,
#       indices: static openArray[GeneralizedIndex],
#       roots: var openArray[Digest]): Result[void, string]
#
# Instead of passing the static `indices` to this function, the Nim compiler
# generates a copy of `indices` with incorrect types (pointers instead of NU64).
# This copy is then passed to this function which then interprets it as NU64[].
# On 32-bit platforms such as i386 the pointer width does not match NU64 width,
# leading to incorrect followup computations and out-of-bounds memory access.
#
# Creating a minimal reproducible example showcasing this bug proved difficult.
#
# Affected: Nim Compiler Version 1.2.14 [Linux: i386]
# https://github.com/nim-lang/Nim/issues/19157
func hash_tree_root_multi(
    x: auto,
    batch: BatchRequest,
    slice: Slice[int],
    atLayer = 0): Result[void, string] =
  trs "STARTING HASH TREE ROOT FOR TYPE ", name(typeof(x)),
    slice.mapIt(indexAt(it))
  mixin toSszType

  when x is HashArray|HashList|HashSeq:
    ? hashTreeRootCached(x, batch, slice, atLayer)
  else:
    ? hashTreeRootAux(toSszType(x), batch, slice, atLayer)

  trs "HASH TREE ROOT FOR ", name(typeof(x)),
    slice.mapIt(indexAt(it)), " = ", slice.mapIt("0x" & $rootAt(it))
  ok()

func merkleizationCmp(x, y: GeneralizedIndex): int =
  # GeneralizedIndex is 1-based.
  # Looking at their bit patterns, from MSB to LSB, they:
  # - Start with a 1 bit.
  # - Continue with a 0 bit when going left or 1 bit when going right,
  #   from the tree root down to the leaf.
  # e.g., 0b1_110 is the node after picking right branch twice, then left.
  #
  #     1      Order: Left -> Right -> Parent
  #    / \     - Left/Right must be available to compute Parent (post-order).
  #   2   3
  #  / \
  # 4   5
  let xBeforeY = block:
    let
      xZeros = x.leadingZeros()
      yZeros = y.leadingZeros()
    if xZeros == yZeros:  # Same layer
      x < y
    elif xZeros < yZeros:  # `x` deeper than `y`
      let xAtLayerOfY = (x shr (yZeros - xZeros))
      if xAtLayerOfY != y:
        # No shared ancestry
        xAtLayerOfY < y
      else:
        # `x` descends from `y` --> children before parent
        true
    else:  # `y` deeper than `x`
      let yAtLayerOfX = (y shr (xZeros - yZeros))
      if yAtLayerOfX != x:
        # No shared ancestry
        x < yAtLayerOfX
      else:
        # `y` descends from `x` --> children before parent
        false
  if xBeforeY:
    -1
  else:
    1

func sortForMerkleization(sortOrder: var openArray[int], indices: auto) =
  sortOrder.sort do (x, y: auto) -> int:
    merkleizationCmp(indices[x], indices[y])

func merkleizationLoopOrder*(
    indices: openArray[GeneralizedIndex]): seq[int] =
  var sortOrder =
    when (NimMajor, NimMinor) < (2, 2):
      when nimvm:
        newSeq[int](indices.len)
      else:
        newSeqUninitialized[int](indices.len)
    else:
      newSeqUninit[int](indices.len)
  for i in 0 ..< indices.len:
    sortOrder[i] = i
  when nimvm:
    sortOrder.sortForMerkleization toSeq(indices)
  else:
    sortOrder.sortForMerkleization makeUncheckedArray(unsafeAddr indices[0])
  sortOrder

func validateIndices(
    indices: openArray[GeneralizedIndex],
    loopOrder: seq[int]): Result[void, string] =
  var
    prev = indices[loopOrder[0]]
    prevLayer = log2trunc(prev)
  if prev < 1.GeneralizedIndex: return err("Invalid generalized index.")
  for i in 1 .. loopOrder.high:
    let
      curr = indices[loopOrder[i]]
      currLayer = log2trunc(curr)
      indicesOverlap =
        if currLayer < prevLayer:
          (prev shr (prevLayer - currLayer)) == curr
        elif currLayer > prevLayer:
          (curr shr (currLayer - prevLayer)) == prev
        else:
          curr == prev
    if indicesOverlap:
      return err("Given indices cover some leafs multiple times.")
    prev = curr
    prevLayer = currLayer
  ok()

func hash_tree_root*(
    x: auto,
    indices: openArray[GeneralizedIndex],
    roots: var openArray[Digest]): Result[void, string] =
  doAssert indices.len == roots.len
  if indices.len == 0:
    ok()
  elif indices.len == 1 and indices[0] == 1.GeneralizedIndex:
    roots[0] = hash_tree_root(x)
    ok()
  else:
    let loopOrder = merkleizationLoopOrder(indices)
    ? validateIndices(indices, loopOrder)
    let batch = BatchRequest.init(indices, roots, loopOrder)
    hash_tree_root_multi(x, batch, 0 ..< loopOrder.len)

func hash_tree_root*(
    x: auto,
    indices: static openArray[GeneralizedIndex],
    roots: var openArray[Digest]): Result[void, string] =
  doAssert indices.len == roots.len
  when indices.len == 0:
    ok()
  else:
    when indices.len == 1 and indices[0] == 1.GeneralizedIndex:
      roots[0] = hash_tree_root(x)
      ok()
    else:
      const
        loopOrder = merkleizationLoopOrder(indices)
        v = validateIndices(indices, loopOrder)
      when v.isErr:
        err(v.error)
      else:
        let batch = BatchRequest.init(indices, roots, loopOrder)
        hash_tree_root_multi(x, batch, 0 ..< loopOrder.len)

func hash_tree_root*(
    x: auto,
    indices: openArray[GeneralizedIndex]
): Result[seq[Digest], string] =
  if indices.len == 0:
    ok(newSeq[Digest](0))
  elif indices.len == 1 and indices[0] == 1.GeneralizedIndex:
    ok(@[hash_tree_root(x)])
  else:
    let loopOrder = merkleizationLoopOrder(indices)
    ? validateIndices(indices, loopOrder)
    var roots = newSeq[Digest](indices.len)
    let batch = BatchRequest.init(indices, roots, loopOrder)
    ? hash_tree_root_multi(x, batch, 0 ..< loopOrder.len)
    ok(roots)

func hash_tree_root*(
    x: auto,
    indices: static openArray[GeneralizedIndex]
): auto =
  type ResultType = Result[array[indices.len, Digest], string]
  when indices.len == 0:
    ResultType.ok([])
  else:
    when indices.len == 1 and indices[0] == 1.GeneralizedIndex:
      ResultType.ok([hash_tree_root(x)])
    else:
      const
        loopOrder = merkleizationLoopOrder(indices)
        v = validateIndices(indices, loopOrder)
      when v.isErr:
        ResultType.err(v.error)
      else:
        var roots {.noinit.}: array[indices.len, Digest]
        let
          batch = BatchRequest(
            indices: makeUncheckedArray indices.baseAddr,
            indicesHigh: indices.high,
            roots: makeUncheckedArray roots.baseAddr,
            rootsHigh: roots.high,
            loopOrder: makeUncheckedArray loopOrder.baseAddr,
            loopOrderHigh: loopOrder.high)
          w = hash_tree_root_multi(x, batch, 0 ..< loopOrder.len)
        if w.isErr:
          ResultType.err(w.error)
        else:
          ResultType.ok(roots)

func hash_tree_root*(
    x: auto,
    index: GeneralizedIndex
): Result[Digest, string] =
  if index < 1.GeneralizedIndex:
    err("Invalid generalized index.")
  elif index == 1.GeneralizedIndex:
    ok(hash_tree_root(x))
  else:
    let indices = [index]
    var roots {.noinit.}: array[1, Digest]
    const loopOrder = @[0]
    let batch = BatchRequest.init(indices, roots, loopOrder)
    ? hash_tree_root_multi(x, batch, 0 ..< loopOrder.len)
    ok(roots[0])

func hash_tree_root*(
    x: auto,
    index: static GeneralizedIndex
): Result[Digest, string] =
  when index < 1.GeneralizedIndex:
    err("Invalid generalized index.")
  elif index == 1.GeneralizedIndex:
    ok(hash_tree_root(x))
  else:
    const indices = [index]
    var roots {.noinit.}: array[1, Digest]
    const loopOrder = @[0]
    let batch = BatchRequest.init(indices, roots, loopOrder)
    ? hash_tree_root_multi(x, batch, 0 ..< loopOrder.len)
    ok(roots[0])
