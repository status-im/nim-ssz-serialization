# ssz_serialization
# Copyright (c) 2018-2023 Status Research & Development GmbH
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
# large part of the internal implemenation thus avoiding spurious `zeroMem` calls
# and other artefacts of the introduction of hidden temporaries

import
  std/[algorithm, options, sequtils],
  stew/[assign2, bitops2, endians2, ptrops, results],
  nimcrypto/[hash, sha2],
  serialization/testing/tracing,
  "."/[bitseqs, codec, types]

const PREFER_BLST_SHA256* {.booldefine.} = true

when PREFER_BLST_SHA256:
  import blscurve
  when BLS_BACKEND == BLST:
    const USE_BLST_SHA256 = true
  else:
    const USE_BLST_SHA256 = false
else:
  const USE_BLST_SHA256 = false

export
  results,
  sha2.update, hash.fromHex,
  codec, bitseqs, types

when hasSerializationTracing:
  import stew/byteutils, typetraits

const
  zero64 = default array[64, byte]
  zeroDigest = Digest()
  bitsPerChunk = bytesPerChunk * 8

func binaryTreeHeight*(totalElements: Limit): int =
  bitWidth nextPow2(uint64 totalElements)

type
  SszMerkleizer2*[height: static[int]] = object
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

    combinedChunks: array[height, (Digest, Digest)]
    totalChunks*: uint64 # Public for historical reasons
    topIndex: int
    internal: bool
      # Avoid copying chunk data into merkleizer when not needed - maw result
      # in an incomplete root-to-leaf proof

template limit*(T: type SszMerkleizer2): Limit =
  if T.height == 0: 0'i64 else: 1'i64 shl (T.height - 1)

template limit*(v: SszMerkleizer2): Limit =
  typeof(v).limit

template getChunkCount*(m: SszMerkleizer2): uint64 =
  m.totalChunks

func getCombinedChunks*(m: SszMerkleizer2): seq[Digest] =
  mapIt(toOpenArray(m.combinedChunks, 0, m.topIndex), it[0])

when USE_BLST_SHA256:
  export blscurve.update
  type DigestCtx* = BLST_SHA256_CTX
else:
  export sha2.update
  type DigestCtx* = sha2.sha256

template computeDigest*(body: untyped): Digest =
  ## This little helper will init the hash function and return the sliced
  ## hash:
  ## let hashOfData = computeDigest: h.update(data)
  when nimvm:
    # In SSZ, computeZeroHashes require compile-time SHA256
    block:
      var h {.inject.}: sha256
      init(h)
      body
      finish(h)
  else:
    when USE_BLST_SHA256:
      block:
        var h  {.inject, noinit.}: DigestCtx
        init(h)
        body
        var res {.noinit.}: Digest
        finalize(res.data, h)
        res
    else:
      block:
        var h  {.inject, noinit.}: DigestCtx
        init(h)
        body
        finish(h)

when (defined(clang) or defined(gcc)) and
    (defined(arm64) or defined(amd64)):
  const hasHashTree = true

  {.compile: "../vendor/hashtree/src/hashtree.c".}

  when defined(arm64):
    {.compile: "../vendor/hashtree/src/sha256_armv8_neon_x1.S".}
    {.compile: "../vendor/hashtree/src/sha256_armv8_neon_x4.S".}

  elif defined(amd64):
    {.compile: "../vendor/hashtree/src/sha256_avx_x1.S".}
    {.compile: "../vendor/hashtree/src/sha256_avx_x4.S".}
    {.compile: "../vendor/hashtree/src/sha256_avx_x8.S".}
    {.compile: "../vendor/hashtree/src/sha256_avx_x16.S".}
    {.compile: "../vendor/hashtree/src/sha256_shani.S".}
    {.compile: "../vendor/hashtree/src/sha256_sse_x1.S".}

  type HashFcn = proc(output: pointer, input: pointer, count: uint64) {.cdecl, noSideEffect, gcsafe, raises: [].}

  func digest*(a: openArray[byte]): Digest {.noinit.}

  func digest64(output: pointer, input: pointer, count: uint64) {.cdecl, gcsafe, raises: [].} =
    cast[ptr Digest](output)[] =
      digest(cast[ptr UncheckedArray[byte]](input).toOpenArray(0, 63))
    discard

  proc hashtree_init*(override: HashFcn): cint {.importc, gcsafe, raises: [].}
  func hashtree_hash*(output: pointer, input: pointer, count: uint64) {.importc, gcsafe, raises: [].}

  if hashtree_init(nil) == 0:
    discard hashtree_init(digest64)

else:
  const hasHashTree = false

func digest(a: openArray[byte], res: var Digest) =
  trs "DIGESTING ARRAYS 1 ", toHex(a)
  when nimvm:
    res = block:
      var h: sha256
      h.init()
      h.update(a)
      h.finish()
  else:
    when hasHashTree:
      if a.len() == 64:
        hashtree_hash(baseAddr res.data, baseAddr a, 1)
        return

    when USE_BLST_SHA256:
      # BLST has a fast assembly optimized SHA256
      res.data.bls_sha256_digest(a)
    else:
      res = block:
        # We use the init-update-finish interface to avoid
        # the expensive burning/clearing memory (20~30% perf)
        var h {.noinit.}: DigestCtx
        h.init()
        h.update(a)
        h.finish()

func digest*(a: openArray[byte]): Digest {.noinit.} =
  digest(a, result)

func digest(a, b: openArray[byte], res: var Digest) =
  when nimvm:
    res =
      computeDigest:
        trs "DIGESTING ARRAYS 2 ", toHex(a), " ", toHex(b)

        h.update a
        h.update b
  else:
    if distance(baseAddr a, baseAddr b) == a.len:
      # Adjacent in memory, make a single call (avoids copies inside the
      # digester)
      digest(makeOpenArray(baseAddr a, a.len + b.len), res)
    elif a.len + b.len == 64:
      # Single call to digester
      var buf {.noinit.}: array[64, byte]
      if a.len > 0:
        copyMem(addr buf[0], unsafeAddr a[0], a.len)
      # b.len > 0 per above..
      if b.len > 0:
        copyMem(addr buf[a.len], unsafeAddr b[0], b.len)
      digest(buf, res)
    else:
      res =
        computeDigest:
          trs "DIGESTING ARRAYS 2 ", toHex(a), " ", toHex(b)

          h.update a
          h.update b
  trs "HASH RESULT ", res

template mergeBranches(existing: Digest, newData: array[32, byte], res: var Digest) =
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

  when merkleizer.limit > 0:
    addChunkDirect(merkleizer):
      assign(chunk.data.toOpenArray(0, data.high), data)
      if data.len < bytesPerChunk:
        zeroMem(addr chunk.data[data.len], bytesPerChunk - data.len)
  else:
    raiseAssert "Cannot add chunks to 0-length merkleizer"

template isOdd(x: SomeNumber): bool =
  (x and 1) != 0

func addChunks*(merkleizer: var SszMerkleizer2, data: openArray[byte]) =
  doAssert merkleizer.totalChunks == 0
  doAssert merkleizer.limit * bytesPerChunk >= data.len,
    "Adding chunks would exceed merklelizer limit " & $merkleizer.limit

  var done = 0
  while done < data.len:
    let
      remaining = data.len - done

    if remaining >= bytesPerChunk * 2:
      when merkleizer.limit > 1: # Defeat compile-time index checking
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
    else:
      trs "COMPUTING REMAINDER DATA HASH ", remaining
      if remaining > bytesPerChunk:
        merkleizer.addChunk(data.toOpenArray(done, done + bytesPerChunk - 1))
        done += bytesPerChunk

      merkleizer.addChunk(data.toOpenArray(done, data.high))
      break

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

func init*(S: type SszMerkleizer2): S =
  S(
    topIndex: S.height - 1,
    totalChunks: 0)

func init*(S: type SszMerkleizer2,
           combinedChunks: openArray[Digest],
           totalChunks: uint64): S =
  for i in 0..<combinedChunks.len:
    result.combinedChunks[i][0] = combinedChunks[i]
  result.topIndex = S.height - 1
  result.totalChunks = totalChunks

template createMerkleizer2*(
    height: static Limit, topLayer = 0,
    internalParam = false): auto =
  trs "CREATING A MERKLEIZER FOR ", height, " (topLayer: ", topLayer, ")"

  let topIndex = height - 1 - topLayer

  SszMerkleizer2[height](
    topIndex: if (topIndex < 0): 0 else: topIndex,
    totalChunks: 0,
    internal: internalParam)

template createMerkleizer*(
    totalElements: static Limit, topLayer = 0,
    internalParam = false): auto =
  const treeHeight = binaryTreeHeight totalElements
  createMerkleizer2(treeHeight, topLayer, internalParam)

func getFinalHash(merkleizer: var SszMerkleizer2, res: var Digest) =
  if merkleizer.totalChunks == 0:
    res = zeroHashes[merkleizer.topIndex]
    return

  let
    bottomHashIdx = firstOne(merkleizer.totalChunks) - 1
    submittedChunksHeight = bitWidth(merkleizer.totalChunks - 1)
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
    mergeBranches(
      merkleizer.combinedChunks[bottomHashIdx][0], zeroHashes[bottomHashIdx],
      res)

    for i in bottomHashIdx + 1 ..< topHashIdx:
      mergeBranches(res, zeroHashes[i], res)

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

func hash_tree_root*(x: auto): Digest {.gcsafe, raises: [], noinit.}

func hash_tree_root_multi(
    x: auto,
    indices: openArray[GeneralizedIndex],
    roots: var openArray[Digest],
    loopOrder: seq[int],
    slice: Slice[int],
    atLayer = 0): Result[void, string] {.gcsafe, raises: [].}

template addField(field) =
  trs "MERKLEIZING FIELD ", astToStr(field)
  addChunkDirect(merkleizer):
    chunk = hash_tree_root(field)
  trs "CHUNK ADDED"

template merkleizeFields(totalChunks: static Limit, res: var Digest, body: untyped) =
  var merkleizer {.inject.} = createMerkleizer(totalChunks, internalParam = true)

  body

  getFinalHash(merkleizer, res)

template writeBytesLE(chunk: var array[bytesPerChunk, byte], atParam: int,
                      val: UintN) =
  let at = atParam
  chunk[at ..< at + sizeof(val)] = toBytesLE(val)

func chunkedHashTreeRoot[T: BasicType](
    merkleizer: var SszMerkleizer2, arr: openArray[T],
    firstIdx, numFromFirst: Limit, res: var Digest) =
  static:
    doAssert bytesPerChunk mod sizeof(T) == 0

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
        chunk.writeBytesLE(i * sizeof(T), arr[firstIdx + writtenValues + i])
      addChunk(merkleizer, chunk)
      inc writtenValues, valuesPerChunk

    let remainingValues = numFromFirst - writtenValues
    if remainingValues > 0:
      var lastChunk: array[bytesPerChunk, byte]
      for i in 0 ..< remainingValues:
        lastChunk.writeBytesLE(i * sizeof(T), arr[firstIdx + writtenValues + i])
      addChunk(merkleizer, lastChunk)

  getFinalHash(merkleizer, res)

func chunkedHashTreeRoot[T: not BasicType](
    merkleizer: var SszMerkleizer2, arr: openArray[T],
    firstIdx, numFromFirst: Limit, res: var Digest) =
  for i in 0 ..< numFromFirst:
    addChunkDirect(merkleizer):
      chunk = hash_tree_root(arr[firstIdx + i])
  getFinalHash(merkleizer, res)

func chunkedHashTreeRoot[T](
    height: static Limit, arr: openArray[T],
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  const valuesPerChunk =
    when T is BasicType:
      bytesPerChunk div sizeof(T)
    else:
      1
  let firstIdx = chunks.a * valuesPerChunk
  if arr.len <= firstIdx:
    res = zeroHashes[height - 1 - topLayer]
  else:
    var merkleizer = createMerkleizer2(height, topLayer, internalParam = true)
    let numFromFirst =
      min((chunks.b - chunks.a + 1) * valuesPerChunk, arr.len - firstIdx)
    chunkedHashTreeRoot(merkleizer, arr, firstIdx, numFromFirst, res)

func chunkedHashTreeRoot[T](
    height: static Limit, arr: openArray[T], res: var Digest) =
  if arr.len <= 0:
    res = zeroHashes[height - 1]
  else:
    var merkleizer = createMerkleizer2(height, internalParam = true)
    chunkedHashTreeRoot(merkleizer, arr, 0, arr.len, res)

func bitListHashTreeRoot(
    merkleizer: var SszMerkleizer2, x: BitSeq, chunks: Slice[Limit],
    res: var Digest) =
  # TODO: Switch to a simpler BitList representation and
  #       replace this with `chunkedHashTreeRoot`
  var
    totalBytes = bytes(x).len
    lastCorrectedByte = bytes(x)[^1]

  if lastCorrectedByte == byte(1):
    if totalBytes == 1:
      # This is an empty bit list.
      # It should be hashed as a tree containing all zeros:
      res = zeroHashes[merkleizer.topIndex]
      return

    totalBytes -= 1
    lastCorrectedByte = bytes(x)[^2]
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

    addChunk(merkleizer, bytes(x).toOpenArray(chunkStartPos, chunkEndPos))

  if fullChunks in chunks:
    var
      lastChunk: array[bytesPerChunk, byte]
      chunkStartPos = fullChunks * bytesPerChunk

    for i in 0 .. bytesInLastChunk - 2:
      lastChunk[i] = bytes(x)[chunkStartPos + i]

    lastChunk[bytesInLastChunk - 1] = lastCorrectedByte

    addChunk(merkleizer, lastChunk.toOpenArray(0, bytesInLastChunk - 1))

  getFinalHash(merkleizer, res)

template bitListHashTreeRoot(
    totalChunks: static Limit, x: BitSeq,
    chunks: Slice[Limit], topLayer: int, res: var Digest) =
  var merkleizer = createMerkleizer(totalChunks, topLayer, internalParam = true)
  bitListHashTreeRoot(merkleizer, x, chunks, res)

template bitListHashTreeRoot(
    totalChunks: static Limit, x: BitSeq, res: var Digest) =
  bitListHashTreeRoot(totalChunks, x, 0.Limit ..< totalChunks, topLayer = 0, res)

func maxChunksCount(T: type, maxLen: Limit): Limit =
  when T is BitArray|BitList:
    (maxLen + bitsPerChunk - 1) div bitsPerChunk
  elif T is array|List:
    maxChunkIdx(ElemType(T), maxLen)
  else:
    unsupported T # This should never happen

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

template indexAt(i: int): GeneralizedIndex =
  block:
    let v = indices[loopOrder[i]]
    if atLayer != 0:
      let
        n = leadingZeros(v) + 1 + atLayer
        x = ((v shl n) or 1.GeneralizedIndex).GeneralizedIndex
      rotateRight(x, n)
    else:
      v

template rootAt(i: int): Digest =
  roots[loopOrder[i]]

const unsupportedIndex =
  err(Result[void, string], "Generalized index not supported.")

func hashTreeRootAux[T](x: T, res: var Digest) =
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
    bitListHashTreeRoot(totalChunks, BitSeq x, contentsHash)
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
  elif T is OptionalType:
    if x.isSome:
      mixInLength(hash_tree_root(toSszType(x.get)), length = 1, res)
    else:
      res = zeroHashes[1]
  elif T is object|tuple:
    # when T.isCaseObject():
    #   # TODO: Need to implement this for case object (SSZ Union)
    #   unsupported T
    trs "MERKLEIZING FIELDS"
    const totalChunks = totalSerializedFields(T)
    merkleizeFields(Limit totalChunks, res):
      x.enumerateSubFields(f):
        addField f
  else:
    unsupported T

func hashTreeRootAux[T](
    x: T,
    indices: openArray[GeneralizedIndex],
    roots: var openArray[Digest],
    loopOrder: seq[int],
    slice: Slice[int],
    atLayer: int): Result[void, string] =
  when T is BasicType:
    for i in slice:
      if indexAt(i) != 1.GeneralizedIndex: return unsupportedIndex
      hashTreeRootAux(x, rootAt(i))
  elif T is BitArray:
    ? hashTreeRootAux(x.bytes, indices, roots, loopOrder, slice, atLayer)
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
        bitListHashTreeRoot(totalChunks, BitSeq x, contentsHash)
        mixInLength(contentsHash, x.len, rootAt(i))
        inc i
      elif index == 3.GeneralizedIndex:
        hashTreeRootAux(x.len.uint64, rootAt(i))
        inc i
      elif index == 2.GeneralizedIndex:
        bitListHashTreeRoot(totalChunks, BitSeq x, rootAt(i))
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
        let
          atLayer = atLayer + 1
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          bitListHashTreeRoot(
            totalChunks, BitSeq x, chunks, indexLayer, rootAt(i))
          inc i
        else: return unsupportedIndex
      else: return unsupportedIndex
  elif T is array:
    type E = ElemType(T)
    when E is BasicType and sizeof(T) <= sizeof(roots[0].data):
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
          when ElemType(typeof(x)) is BasicType: return unsupportedIndex
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
            ? hash_tree_root_multi(x[chunk], indices, roots, loopOrder, i ..< j,
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
          when ElemType(typeof(x)) is BasicType: return unsupportedIndex
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
            ? hash_tree_root_multi(x[chunk], indices, roots, loopOrder, i ..< j,
                                   atLayer + chunkLayer)
            i = j
      else: return unsupportedIndex
  elif T is OptionalType:
    const
      totalChunks = Limit 1
      firstChunkIndex = nextPow2(totalChunks.uint64)
      chunkLayer = log2trunc(firstChunkIndex)
    var i = slice.a
    while i <= slice.b:
      let
        index = indexAt(i)
        indexLayer = log2trunc(index)
      if index == 1.GeneralizedIndex:
        if x.isSome:
          mixInLength(hash_tree_root(toSszType(x.get)), length = 1, rootAt(i))
        else:
          rootAt(i) = zeroHashes[1]
        inc i
      elif index == 3.GeneralizedIndex:
        if x.isSome:
          hashTreeRootAux(1.uint64, rootAt(i))
        else:
          rootAt(i) = zeroHashes[0]
        inc i
      elif index == 2.GeneralizedIndex:
        if x.isSome:
          rootAt(i) = hash_tree_root(x.get)
        else:
          rootAt(i) = zeroHashes[0]
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
        if x.isNone: return unsupportedIndex
        let
          atLayer = atLayer + 1
          index = indexAt(i)
          indexLayer = log2trunc(index)
          chunk = chunkContainingIndex(index)
        var j = i + 1
        while j <= slice.b:
          let
            index = indexAt(j)
            indexLayer = log2trunc(index)
          if indexLayer <= chunkLayer or
              chunkContainingIndex(index) != chunk:
            break
          inc j
        ? hash_tree_root_multi(x.get, indices, roots, loopOrder, i ..< j,
                               atLayer + chunkLayer)
        i = j
      else: return unsupportedIndex
  elif T is object|tuple:
    # when T.isCaseObject():
    #   # TODO: Need to implement this for case object (SSZ Union)
    #   unsupported T
    trs "MERKLEIZING FIELDS"
    const
      totalChunks = totalSerializedFields(T)
      treeHeight = binaryTreeHeight(totalChunks)
      firstChunkIndex = nextPow2(totalChunks.uint64)
      chunkLayer = log2trunc(firstChunkIndex)
    var
      i = slice.a
      fieldIndex = 0.Limit
      isActive = false
      index {.noinit.}: GeneralizedIndex
      indexLayer {.noinit.}: int
      chunks {.noinit.}: Slice[Limit]
      merkleizer {.noinit.}: SszMerkleizer2[treeHeight]
      chunk {.noinit.}: Limit
      nextField {.noinit.}: Limit
    x.enumerateSubFields(f):
      if i <= slice.b:
        if not isActive:
          index = indexAt(i)
          indexLayer = log2trunc(index)
          nextField =
            if indexLayer == chunkLayer:
              chunkForIndex(index)
            elif indexLayer < chunkLayer:
              chunks = chunksForIndex(index)
              merkleizer.topIndex = chunkLayer - indexLayer
              merkleizer.totalChunks = 0
              chunks.a
            else:
              chunk = chunkContainingIndex(index)
              chunk
          isActive = true
        if fieldIndex >= nextField:
          if indexLayer == chunkLayer:
            rootAt(i) = hash_tree_root(f)
            inc i
            isActive = false
          elif indexLayer < chunkLayer:
            addField f
            if fieldIndex >= chunks.b:
              rootAt(i) = getFinalHash(merkleizer)
              inc i
              isActive = false
          else:
            var j = i + 1
            while j <= slice.b:
              let
                index = indexAt(j)
                indexLayer = log2trunc(index)
              if indexLayer <= chunkLayer or
                  chunkContainingIndex(index) != chunk:
                break
              inc j
            ? hash_tree_root_multi(f, indices, roots, loopOrder, i ..< j,
                                   atLayer + chunkLayer)
            i = j
            isActive = false
      inc fieldIndex
    doAssert log2trunc(fieldIndex.uint64) == log2trunc(totalChunks.uint64)
    while i <= slice.b:
      index = indexAt(i)
      indexLayer = log2trunc(index)
      if indexLayer == chunkLayer:
        rootAt(i) = static(Digest())
        inc i
        isActive = false
      elif indexLayer < chunkLayer:
        if not isActive:
          merkleizer.topIndex = chunkLayer - indexLayer
          merkleizer.totalChunks = 0
        rootAt(i) = getFinalHash(merkleizer)
        inc i
        isActive = false
      else: return unsupportedIndex
  else:
    unsupported T
  ok()

func mergedDataHash(x: HashArray|HashList, chunkIdx: int64, res: var Digest) =
  # The merged hash of the data at `chunkIdx` and `chunkIdx + 1`
  trs "DATA HASH ", chunkIdx, " ", x.data.len

  when x.T is BasicType or x.T is Digest:
    when cpuEndian == bigEndian:
      unsupported typeof(x) # No bigendian support here!

    let
      bytes = cast[ptr UncheckedArray[byte]](unsafeAddr x.data[0])
      byteIdx = chunkIdx * bytesPerChunk
      byteLen = x.data.len * sizeof(x.T)

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
    if chunkIdx + 1 > x.data.len():
      res = zeroHashes[x.maxDepth]
    elif chunkIdx + 1 == x.data.len():
      let left {.noinit.} = hash_tree_root(x.data[chunkIdx])
      mergeBranches(left, zeroDigest, res)
    else:
      let
        left {.noinit.} = hash_tree_root(x.data[chunkIdx])
        right {.noinit.} = hash_tree_root(x.data[chunkIdx + 1])

      mergeBranches(left, right, res)

template mergedHash(x: HashArray|HashList, vIdxParam: int64, res: var Digest) =
  # The merged hash of the data at `vIdx` and `vIdx + 1`
  let vIdx = vIdxParam
  if vIdx >= x.maxChunks:
    let dataIdx = vIdx - x.maxChunks
    mergedDataHash(x, dataIdx, res)
  else:
    mergeBranches(
      hashTreeRootCachedPtr(x, vIdx)[], hashTreeRootCachedPtr(x, vIdx + 1)[],
      res)

func hashTreeRootCachedPtr*(x: HashArray, vIdx: int64): ptr Digest =
  # Return a short-lived pointer to the given digest - a pointer is used because
  # `var` and `lent` returns don't work for the constant zero hashes
  # The instance must not be mutated! This is an internal low-level API.

  doAssert vIdx >= 1, "Only valid for flat Merkle tree indices"

  let px = unsafeAddr x.hashes[vIdx]
  if not isCached(x.hashes[vIdx]):
    # TODO oops. so much for maintaining non-mutability.
    mergedHash(x, vIdx * 2, px[])
  px

func hashTreeRootCachedPtr*(x: HashList, vIdx: int64): ptr Digest =
  # Return a short-lived pointer to the given digest - a pointer is used because
  # `var` and `lent` returns don't work for the constant zero hashes
  # The instance must not be mutated! This is an internal low-level API.

  doAssert vIdx >= 1, "Only valid for flat Merkle tree indices"

  let
    layer = layer(vIdx)
    idxInLayer = vIdx - (1'i64 shl layer)
    layerIdx = idxInLayer + x.indices[layer]

  trs "GETTING ", vIdx, " ", layerIdx, " ", layer, " ", x.indices.len

  doAssert layer < x.maxDepth
  if layerIdx >= x.indices[layer + 1]:
    trs "ZERO ", x.indices[layer], " ", x.indices[layer + 1]
    unsafeAddr zeroHashes[x.maxDepth - layer]
  else:
    let px = unsafeAddr x.hashes[layerIdx]
    if not isCached(px[]):
      trs "REFRESHING ", vIdx, " ", layerIdx, " ", layer
      # TODO oops. so much for maintaining non-mutability.
      mergedHash(x, vIdx * 2, px[])
    else:
      trs "CACHED ", layerIdx
    px

func hashTreeRootCached*(x: HashArray): Digest {.noinit.} =
  hashTreeRootCachedPtr(x, 1)[] # Array does not use idx 0

func hashTreeRootCached*(x: HashList): Digest {.noinit.} =
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

func hashTreeRootCached*(
    x: HashArray,
    indices: openArray[GeneralizedIndex],
    roots: var openArray[Digest],
    loopOrder: seq[int],
    slice: Slice[int],
    atLayer: int): Result[void, string] =
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
      when ElemType(typeof(x)) is BasicType:
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
        ? hash_tree_root_multi(x[chunk], indices, roots, loopOrder, i ..< j,
                               atLayer + chunkLayer)
        i = j
  ok()

func hashTreeRootCached*(
    x: HashList,
    indices: openArray[GeneralizedIndex],
    roots: var openArray[Digest],
    loopOrder: seq[int],
    slice: Slice[int],
    atLayer: int): Result[void, string] =
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
        when ElemType(typeof(x)) is BasicType: return unsupportedIndex
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
          ? hash_tree_root_multi(x[chunk], indices, roots, loopOrder, i ..< j,
                                 atLayer + chunkLayer)
          i = j
    else: return unsupportedIndex
  ok()

func hash_tree_root*(x: auto): Digest {.noinit.} =
  trs "STARTING HASH TREE ROOT FOR TYPE ", name(typeof(x))
  mixin toSszType

  when x is HashArray|HashList:
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
    indices: openArray[GeneralizedIndex],
    roots: var openArray[Digest],
    loopOrder: seq[int],
    slice: Slice[int],
    atLayer = 0): Result[void, string] =
  trs "STARTING HASH TREE ROOT FOR TYPE ", name(typeof(x)),
    slice.mapIt(indexAt(it))
  mixin toSszType

  when x is HashArray|HashList:
    ? hashTreeRootCached(x, indices, roots, loopOrder, slice, atLayer)
  else:
    ? hashTreeRootAux(toSszType(x), indices, roots, loopOrder, slice, atLayer)

  trs "HASH TREE ROOT FOR ", name(typeof(x)),
    slice.mapIt(indexAt(it)), " = ", slice.mapIt("0x" & $rootAt(it))
  ok()

template normalize(v: GeneralizedIndex): GeneralizedIndex =
  # GeneralizedIndex is 1-based.
  # Looking at their bit patterns, from MSB to LSB, they:
  # - Start with a 1 bit.
  # - Continue with a 0 bit when going left or 1 bit when going right,
  #   from the tree root down to the leaf.
  # i.e., 0b1_110 is the node after picking right branch twice, then left.
  #
  # For depth-first ordering, shorter bit-strings are parents of nodes
  # that include them as their prefix.
  # i.e., 0b1_110 is parent of 0b1_1100 (left) and 0b1_1101 (right)
  # An extra 1 bit is added to distinguish parents from their left child.
  ((v shl 1) or 1) shl leadingZeros(v)

# Comparison utility for sorting indices in depth-first order (in-order).
# This order is needed because `enumInstanceSerializedFields` does not allow
# random access to specific fields. With depth-first order only a single pass
# is required to fill in all the roots. `enumAllSerializedFields` cannot be
# used for pre-computation at compile time, because the generalized indices
# depend on the specific case values defined by the specific object instance.
func cmpDepthFirst(x, y: GeneralizedIndex): int =
  cmp(x.normalize, y.normalize)

func merkleizationLoopOrderNimvm(
    indices: openArray[GeneralizedIndex]): seq[int] {.compileTime.} =
  result = toSeq(indices.low .. indices.high)
  let idx = toSeq(indices)
  result.sort do (x, y: int) -> int:
    cmpDepthFirst(idx[x], idx[y])

func merkleizationLoopOrderRegular(
    indices: openArray[GeneralizedIndex]): seq[int] =
  result = toSeq(indices.low .. indices.high)
  let idx = makeUncheckedArray(unsafeAddr indices[0])
  result.sort do (x, y: int) -> int:
    cmpDepthFirst(idx[x], idx[y])

func merkleizationLoopOrder(
    indices: openArray[GeneralizedIndex]): seq[int] =
  when nimvm:
    merkleizationLoopOrderNimvm(indices)
  else:
    merkleizationLoopOrderRegular(indices)

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
    let slice = 0 ..< loopOrder.len
    hash_tree_root_multi(x, indices, roots, loopOrder, slice)

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
        const slice = 0 ..< loopOrder.len
        hash_tree_root_multi(x, indices, roots, loopOrder, slice)

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
    let slice = 0 ..< loopOrder.len
    var roots = newSeq[Digest](indices.len)
    ? hash_tree_root_multi(x, indices, roots, loopOrder, slice)
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
      var roots {.noinit.}: array[indices.len, Digest]
      const
        loopOrder = merkleizationLoopOrder(indices)
        v = validateIndices(indices, loopOrder)
      when v.isErr:
        ResultType.err(v.error)
      else:
        const slice = 0 ..< loopOrder.len
        let w = hash_tree_root_multi(x, indices, roots, loopOrder, slice)
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
    const
      loopOrder = @[0]
      slice = 0 ..< loopOrder.len
    var roots {.noinit.}: array[1, Digest]
    ? hash_tree_root_multi(x, [index], roots, loopOrder, slice)
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
    const
      loopOrder = @[0]
      slice = 0 ..< loopOrder.len
    var roots {.noinit.}: array[1, Digest]
    ? hash_tree_root_multi(x, [index], roots, loopOrder, slice)
    ok(roots[0])
