# ssz_serialization
# Copyright (c) 2018-2022 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

# This module contains the parts necessary to create a merkle hash from the core
# SSZ types outlined in the spec:
# https://github.com/ethereum/consensus-specs/blob/v1.0.1/ssz/simple-serialize.md#merkleization

{.push raises: [Defect].}

import
  std/[algorithm, sequtils],
  stew/[bitops2, endians2, ptrops, results],
  stew/ranges/ptr_arith, nimcrypto/[hash, sha2],
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
  bitsPerChunk = bytesPerChunk * 8

func binaryTreeHeight*(totalElements: Limit): int =
  bitWidth nextPow2(uint64 totalElements)

type
  SszMerkleizerImpl = object
    combinedChunks: ptr UncheckedArray[Digest]
    totalChunks: uint64
    topIndex: int

  SszMerkleizer*[limit: static[Limit]] = object
    combinedChunks: ref array[binaryTreeHeight limit, Digest]
    impl: SszMerkleizerImpl

template chunks*(m: SszMerkleizerImpl): openArray[Digest] =
  m.combinedChunks.toOpenArray(0, m.topIndex)

template getChunkCount*(m: SszMerkleizer): uint64 =
  m.impl.totalChunks

template getCombinedChunks*(m: SszMerkleizer): openArray[Digest] =
  toOpenArray(m.impl.combinedChunks, 0, m.impl.topIndex)

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

func digest*(a: openArray[byte]): Digest {.noinit.} =
  when nimvm:
    block:
      var h: sha256
      h.init()
      h.update(a)
      h.finish()
  else:
    when USE_BLST_SHA256:
      # BLST has a fast assembly optimized SHA256
      result.data.bls_sha256_digest(a)
    else:
      block:
        # We use the init-update-finish interface to avoid
        # the expensive burning/clearing memory (20~30% perf)
        var h {.noinit.}: DigestCtx
        h.init()
        h.update(a)
        h.finish()

func digest(a, b: openArray[byte]): Digest =
  result = computeDigest:
    trs "DIGESTING ARRAYS ", toHex(a), " ", toHex(b)
    trs toHex(a)
    trs toHex(b)

    h.update a
    h.update b
  trs "HASH RESULT ", result

func digest(a, b, c: openArray[byte]): Digest =
  result = computeDigest:
    trs "DIGESTING ARRAYS ", toHex(a), " ", toHex(b), " ", toHex(c)

    h.update a
    h.update b
    h.update c
  trs "HASH RESULT ", result

func mergeBranches(existing: Digest, newData: openArray[byte]): Digest =
  trs "MERGING BRANCHES OPEN ARRAY"

  let paddingBytes = bytesPerChunk - newData.len
  digest(existing.data, newData, zero64.toOpenArray(0, paddingBytes - 1))

template mergeBranches(existing: Digest, newData: array[32, byte]): Digest =
  trs "MERGING BRANCHES ARRAY"
  digest(existing.data, newData)

template mergeBranches(a, b: Digest): Digest =
  trs "MERGING BRANCHES DIGEST"
  digest(a.data, b.data)

func computeZeroHashes: array[sizeof(Limit) * 8, Digest] =
  result[0] = Digest()
  for i in 1 .. result.high:
    result[i] = mergeBranches(result[i - 1], result[i - 1])

const zeroHashes* = computeZeroHashes()

func addChunk*(merkleizer: var SszMerkleizerImpl, data: openArray[byte]) =
  doAssert data.len > 0 and data.len <= bytesPerChunk

  if getBitLE(merkleizer.totalChunks, 0):
    var hash = mergeBranches(merkleizer.combinedChunks[0], data)

    for i in 1 .. merkleizer.topIndex:
      trs "ITERATING"
      if getBitLE(merkleizer.totalChunks, i):
        trs "CALLING MERGE BRANCHES"
        hash = mergeBranches(merkleizer.combinedChunks[i], hash)
      else:
        trs "WRITING FRESH CHUNK AT ", i, " = ", hash
        merkleizer.combinedChunks[i] = hash
        break
  else:
    let paddingBytes = bytesPerChunk - data.len

    merkleizer.combinedChunks[0].data[0..<data.len] = data
    merkleizer.combinedChunks[0].data[data.len..<bytesPerChunk] =
      zero64.toOpenArray(0, paddingBytes - 1)

    trs "WROTE BASE CHUNK ",
      toHex(merkleizer.combinedChunks[0].data), " ", data.len

  inc merkleizer.totalChunks

template isOdd(x: SomeNumber): bool =
  (x and 1) != 0

func addChunkAndGenMerkleProof*(merkleizer: var SszMerkleizerImpl,
                                hash: Digest,
                                outProof: var openArray[Digest]) =
  var
    hashWrittenToMerkleizer = false
    hash = hash

  doAssert merkleizer.topIndex < outProof.len

  for level in 0 .. merkleizer.topIndex:
    if getBitLE(merkleizer.totalChunks, level):
      outProof[level] = merkleizer.combinedChunks[level]
      hash = mergeBranches(merkleizer.combinedChunks[level], hash)
    else:
      if not hashWrittenToMerkleizer:
        merkleizer.combinedChunks[level] = hash
        hashWrittenToMerkleizer = true
      outProof[level] = zeroHashes[level]
      hash = mergeBranches(hash, zeroHashes[level])

  merkleizer.totalChunks += 1

func completeStartedChunk(merkleizer: var SszMerkleizerImpl,
                          hash: Digest, atLevel: int) =
  when false:
    let
      insertedChunksCount = 1'u64 shl (atLevel - 1)
      chunksStateMask = (insertedChunksCount shl 1) - 1
    doAssert (merkleizer.totalChunks and chunksStateMask) == insertedChunksCount

  var hash = hash
  for i in atLevel .. merkleizer.topIndex:
    if getBitLE(merkleizer.totalChunks, i):
      hash = mergeBranches(merkleizer.combinedChunks[i], hash)
    else:
      merkleizer.combinedChunks[i] = hash
      break

func addChunksAndGenMerkleProofs*(merkleizer: var SszMerkleizerImpl,
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
    merkleTree = newSeqOfCap[Digest](chunks.len + merkleizer.topIndex)
    inRowIdx = merkleizer.totalChunks
    postUpdateInRowIdx = newTotalChunks
    zeroMixed = false

  template writeResult(chunkIdx, level: int, chunk: Digest) =
    result[chunkIdx * proofHeight + level] = chunk

  # We'll start by generating the first row of the merkle tree.
  var currPairEnd = if inRowIdx.isOdd:
    # an odd chunk number means that we must combine the
    # hash with the existing pending sibling hash in the
    # merkleizer.
    writeResult(0, 0, merkleizer.combinedChunks[0])
    merkleTree.add mergeBranches(merkleizer.combinedChunks[0], chunks[0])

    # TODO: can we immediately write this out?
    merkleizer.completeStartedChunk(merkleTree[^1], 1)
    2
  else:
    1

  if postUpdateInRowIdx.isOdd:
    merkleizer.combinedChunks[0] = chunks[^1]

  while currPairEnd < chunks.len:
    writeResult(currPairEnd - 1, 0, chunks[currPairEnd])
    writeResult(currPairEnd, 0, chunks[currPairEnd - 1])
    merkleTree.add mergeBranches(chunks[currPairEnd - 1],
                                 chunks[currPairEnd])
    currPairEnd += 2

  if currPairEnd - 1 < chunks.len:
    zeroMixed = true
    writeResult(currPairEnd - 1, 0, zeroHashes[0])
    merkleTree.add mergeBranches(chunks[currPairEnd - 1],
                                 zeroHashes[0])
  var
    level = 0
    baseChunksPerElement = 1
    treeRowStart = 0
    rowLen = merkleTree.len

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
        writeProofs(0, merkleizer.combinedChunks[level])
        merkleTree.add mergeBranches(merkleizer.combinedChunks[level],
                                     merkleTree[treeRowStart])

        # TODO: can we immediately write this out?
        merkleizer.completeStartedChunk(merkleTree[^1], level + 1)
        2
      else:
        1

      if postUpdateInRowIdx.isOdd:
        merkleizer.combinedChunks[level] = merkleTree[treeRowStart + rowLen -
                                                      ord(zeroMixed) - 1]
      while currPairEnd < rowLen:
        writeProofs(currPairEnd - 1, merkleTree[treeRowStart + currPairEnd])
        writeProofs(currPairEnd, merkleTree[treeRowStart + currPairEnd - 1])
        merkleTree.add mergeBranches(merkleTree[treeRowStart + currPairEnd - 1],
                                     merkleTree[treeRowStart + currPairEnd])
        currPairEnd += 2

      if currPairEnd - 1 < rowLen:
        zeroMixed = true
        writeProofs(currPairEnd - 1, zeroHashes[level])
        merkleTree.add mergeBranches(merkleTree[treeRowStart + currPairEnd - 1],
                                     zeroHashes[level])

      treeRowStart += rowLen
      rowLen = merkleTree.len - treeRowStart

      if rowLen == 1:
        break

  doAssert rowLen == 1

  if (inRowIdx and 2) != 0:
    merkleizer.completeStartedChunk(
      mergeBranches(merkleizer.combinedChunks[level + 1], merkleTree[^1]),
      level + 2)

  if (not zeroMixed) and (postUpdateInRowIdx and 2) != 0:
    merkleizer.combinedChunks[level + 1] = merkleTree[^1]

  while level < merkleizer.topIndex:
    inc level
    baseChunksPerElement *= 2
    inRowIdx = inRowIdx div 2

    let hash = if getBitLE(merkleizer.totalChunks, level):
      merkleizer.combinedChunks[level]
    else:
      zeroHashes[level]

    writeProofs(0, hash)

  merkleizer.totalChunks = newTotalChunks

proc init*(S: type SszMerkleizer): S =
  new result.combinedChunks
  result.impl = SszMerkleizerImpl(
    combinedChunks: cast[ptr UncheckedArray[Digest]](
      addr result.combinedChunks[][0]),
    topIndex: binaryTreeHeight(result.limit) - 1,
    totalChunks: 0)

proc init*(S: type SszMerkleizer,
           combinedChunks: openArray[Digest],
           totalChunks: uint64): S =
  new result.combinedChunks
  result.combinedChunks[][0 ..< combinedChunks.len] = combinedChunks
  result.impl = SszMerkleizerImpl(
    combinedChunks: cast[ptr UncheckedArray[Digest]](
      addr result.combinedChunks[][0]),
    topIndex: binaryTreeHeight(result.limit) - 1,
    totalChunks: totalChunks)

proc copy*[L: static[Limit]](cloned: SszMerkleizer[L]): SszMerkleizer[L] =
  new result.combinedChunks
  result.combinedChunks[] = cloned.combinedChunks[]
  result.impl = SszMerkleizerImpl(
    combinedChunks: cast[ptr UncheckedArray[Digest]](
      addr result.combinedChunks[][0]),
    topIndex: binaryTreeHeight(L) - 1,
    totalChunks: cloned.totalChunks)

template addChunksAndGenMerkleProofs*(
    merkleizer: var SszMerkleizer,
    chunks: openArray[Digest]): seq[Digest] =
  addChunksAndGenMerkleProofs(merkleizer.impl, chunks)

template addChunk*(merkleizer: var SszMerkleizer, data: openArray[byte]) =
  addChunk(merkleizer.impl, data)

template totalChunks*(merkleizer: SszMerkleizer): uint64 =
  merkleizer.impl.totalChunks

template getFinalHash*(merkleizer: SszMerkleizer): Digest =
  merkleizer.impl.getFinalHash

template createMerkleizer*(
    totalElements: static Limit, topLayer = 0): SszMerkleizerImpl =
  trs "CREATING A MERKLEIZER FOR ", totalElements, " (topLayer: ", topLayer, ")"

  const treeHeight = binaryTreeHeight totalElements
  var combinedChunks {.noinit.}: array[treeHeight, Digest]

  let topIndex = treeHeight - 1 - topLayer

  SszMerkleizerImpl(
    combinedChunks: cast[ptr UncheckedArray[Digest]](addr combinedChunks),
    topIndex: if (topIndex < 0): 0 else: topIndex,
    totalChunks: 0)

func getFinalHash*(merkleizer: SszMerkleizerImpl): Digest =
  if merkleizer.totalChunks == 0:
    return zeroHashes[merkleizer.topIndex]

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
    result = mergeBranches(merkleizer.combinedChunks[bottomHashIdx],
                           zeroHashes[bottomHashIdx])

    for i in bottomHashIdx + 1 ..< topHashIdx:
      if getBitLE(merkleizer.totalChunks, i):
        result = mergeBranches(merkleizer.combinedChunks[i], result)
        trs "COMBINED"
      else:
        result = mergeBranches(result, zeroHashes[i])
        trs "COMBINED WITH ZERO"

  elif bottomHashIdx == topHashIdx:
    # We have a perfect tree (chunks == 2**n) at just the right height!
    result = merkleizer.combinedChunks[bottomHashIdx]
  else:
    # We have a perfect tree of user chunks, but we have more work to
    # do - we must extend it to reach the desired height
    result = mergeBranches(merkleizer.combinedChunks[bottomHashIdx],
                           zeroHashes[bottomHashIdx])

    for i in bottomHashIdx + 1 ..< topHashIdx:
      result = mergeBranches(result, zeroHashes[i])

func mixInLength*(root: Digest, length: int): Digest =
  var dataLen: array[32, byte]
  dataLen[0..<8] = uint64(length).toBytesLE()
  mergeBranches(root, dataLen)

func hash_tree_root*(x: auto): Digest {.gcsafe, raises: [Defect].}

func hash_tree_root_multi(
    x: auto,
    indices: openArray[GeneralizedIndex],
    roots: var openArray[Digest],
    loopOrder: seq[int],
    slice: Slice[int],
    atLayer = 0): Result[void, string] {.gcsafe, raises: [Defect].}

template addField(field) =
  let hash = hash_tree_root(field)
  trs "MERKLEIZING FIELD ", astToStr(field), " = ", hash
  addChunk(merkleizer, hash.data)
  trs "CHUNK ADDED"

template merkleizeFields(totalChunks: static Limit, body: untyped): Digest =
  var merkleizer {.inject.} = createMerkleizer(totalChunks)

  body

  getFinalHash(merkleizer)

template writeBytesLE(chunk: var array[bytesPerChunk, byte], atParam: int,
                      val: UintN) =
  let at = atParam
  chunk[at ..< at + sizeof(val)] = toBytesLE(val)

func chunkedHashTreeRoot[T: BasicType](
    merkleizer: var SszMerkleizerImpl, arr: openArray[T],
    firstIdx, numFromFirst: Limit): Digest =
  static:
    doAssert bytesPerChunk mod sizeof(T) == 0

  when sizeof(T) == 1 or cpuEndian == littleEndian:
    var
      remainingBytes = numFromFirst * sizeof(T)
      pos = cast[ptr byte](unsafeAddr arr[firstIdx])

    while remainingBytes >= bytesPerChunk:
      addChunk(merkleizer, makeOpenArray(pos, bytesPerChunk))
      pos = offset(pos, bytesPerChunk)
      remainingBytes -= bytesPerChunk

    if remainingBytes > 0:
      addChunk(merkleizer, makeOpenArray(pos, remainingBytes.int))
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

  getFinalHash(merkleizer)

template chunkedHashTreeRoot[T: not BasicType](
    merkleizer: var SszMerkleizerImpl, arr: openArray[T],
    firstIdx, numFromFirst: Limit): Digest =
  for i in 0 ..< numFromFirst:
    let elemHash = hash_tree_root(arr[firstIdx + i])
    addChunk(merkleizer, elemHash.data)
  getFinalHash(merkleizer)

template chunkedHashTreeRoot[T](
    totalChunks: static Limit, arr: openArray[T],
    chunks: Slice[Limit], topLayer: int): Digest =
  const valuesPerChunk =
    when T is BasicType:
      bytesPerChunk div sizeof(T)
    else:
      1
  let firstIdx = chunks.a * valuesPerChunk
  if arr.len <= firstIdx:
    const treeHeight = binaryTreeHeight totalChunks
    zeroHashes[treeHeight - 1 - topLayer]
  else:
    var merkleizer = createMerkleizer(totalChunks, topLayer)
    let numFromFirst =
      min((chunks.b - chunks.a + 1) * valuesPerChunk, arr.len - firstIdx)
    chunkedHashTreeRoot(merkleizer, arr, firstIdx, numFromFirst)

template chunkedHashTreeRoot[T](
    totalChunks: static Limit, arr: openArray[T]): Digest =
  if arr.len <= 0:
    const treeHeight = binaryTreeHeight totalChunks
    zeroHashes[treeHeight - 1]
  else:
    var merkleizer = createMerkleizer(totalChunks)
    chunkedHashTreeRoot(merkleizer, arr, 0, arr.len)

func bitListHashTreeRoot(
    merkleizer: var SszMerkleizerImpl, x: BitSeq,
    chunks: Slice[Limit]): Digest =
  # TODO: Switch to a simpler BitList representation and
  #       replace this with `chunkedHashTreeRoot`
  var
    totalBytes = bytes(x).len
    lastCorrectedByte = bytes(x)[^1]

  if lastCorrectedByte == byte(1):
    if totalBytes == 1:
      # This is an empty bit list.
      # It should be hashed as a tree containing all zeros:
      return zeroHashes[merkleizer.topIndex]

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

  getFinalHash(merkleizer)

template bitListHashTreeRoot(
    totalChunks: static Limit, x: BitSeq,
    chunks: Slice[Limit], topLayer: int): Digest =
  var merkleizer = createMerkleizer(totalChunks, topLayer)
  bitListHashTreeRoot(merkleizer, x, chunks)

template bitListHashTreeRoot(
    totalChunks: static Limit, x: BitSeq): Digest =
  bitListHashTreeRoot(totalChunks, x, 0.Limit ..< totalChunks, topLayer = 0)

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

func hashTreeRootAux[T](x: T): Digest =
  when T is bool|char:
    result.data[0] = byte(x)
  elif T is UintN:
    when cpuEndian == bigEndian:
      result.data[0..<sizeof(x)] = toBytesLE(x)
    else:
      copyMem(addr result.data[0], unsafeAddr x, sizeof x)
  elif T is BitArray:
    hashTreeRootAux(x.bytes)
  elif T is BitList:
    const totalChunks = maxChunksCount(T, x.maxLen)
    let contentsHash = bitListHashTreeRoot(totalChunks, BitSeq x)
    mixInLength(contentsHash, x.len)
  elif T is array:
    type E = ElemType(T)
    when E is BasicType and sizeof(T) <= sizeof(result.data):
      when sizeof(E) == 1 or cpuEndian == littleEndian:
        copyMem(addr result.data[0], unsafeAddr x, sizeof x)
      else:
        var pos = 0
        for e in x:
          writeBytesLE(result.data, pos, e)
          pos += sizeof(E)
    else:
      trs "FIXED TYPE; USE CHUNK STREAM"
      const totalChunks = maxChunksCount(T, x.len)
      chunkedHashTreeRoot(totalChunks, x)
  elif T is List:
    const totalChunks = maxChunksCount(T, x.maxLen)
    let contentsHash = chunkedHashTreeRoot(totalChunks, asSeq x)
    mixInLength(contentsHash, x.len)
  elif T is SingleMemberUnion:
    doAssert x.selector == 0'u8
    merkleizeFields(Limit 2):
      addField hash_tree_root(toSszType(x.value))
  elif T is object|tuple:
    # when T.isCaseObject():
    #   # TODO: Need to implement this for case object (SSZ Union)
    #   unsupported T
    trs "MERKLEIZING FIELDS"
    const totalChunks = totalSerializedFields(T)
    merkleizeFields(Limit totalChunks):
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
      rootAt(i) = hashTreeRootAux(x)
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
        let contentsHash = bitListHashTreeRoot(totalChunks, BitSeq x)
        rootAt(i) = mixInLength(contentsHash, x.len)
        inc i
      elif index == 3.GeneralizedIndex:
        rootAt(i) = hashTreeRootAux(x.len.uint64)
        inc i
      elif index == 2.GeneralizedIndex:
        rootAt(i) = bitListHashTreeRoot(totalChunks, BitSeq x)
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
        let
          atLayer = atLayer + 1
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          rootAt(i) = bitListHashTreeRoot(totalChunks, BitSeq x,
                                          chunks, indexLayer)
          inc i
        else: return unsupportedIndex
      else: return unsupportedIndex
  elif T is array:
    type E = ElemType(T)
    when E is BasicType and sizeof(T) <= sizeof(roots[0].data):
      for i in slice:
        if indexAt(i) != 1.GeneralizedIndex: return unsupportedIndex
        rootAt(i) = hashTreeRootAux(x)
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
          rootAt(i) = chunkedHashTreeRoot(totalChunks, x)
          inc i
        elif indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          rootAt(i) = chunkedHashTreeRoot(totalChunks, x,
                                          chunks, indexLayer)
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
        let contentsHash = chunkedHashTreeRoot(totalChunks, asSeq x)
        rootAt(i) = mixInLength(contentsHash, x.len)
        inc i
      elif index == 3.GeneralizedIndex:
        rootAt(i) = hashTreeRootAux(x.len.uint64)
        inc i
      elif index == 2.GeneralizedIndex:
        rootAt(i) = chunkedHashTreeRoot(totalChunks, asSeq x)
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
        let
          atLayer = atLayer + 1
          index = indexAt(i)
          indexLayer = log2trunc(index)
        if indexLayer <= chunkLayer:
          let chunks = chunksForIndex(index)
          rootAt(i) = chunkedHashTreeRoot(totalChunks, asSeq x,
                                          chunks, indexLayer)
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
  elif T is SingleMemberUnion:
    doAssert x.selector == 0'u8
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
        var merkleizer = createMerkleizer(Limit 2)
        addField hash_tree_root(x.value)
        rootAt(i) = getFinalHash(merkleizer)
        inc i
      elif index == 3.GeneralizedIndex:
        rootAt(i) = Digest()
        inc i
      elif index == 2.GeneralizedIndex:
        rootAt(i) = hash_tree_root(x.value)
        inc i
      elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
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
        ? hash_tree_root_multi(x.value, indices, roots, loopOrder, i ..< j,
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
      firstChunkIndex = nextPow2(totalChunks.uint64)
      chunkLayer = log2trunc(firstChunkIndex)
    var
      combinedChunks {.noinit.}: array[chunkLayer + 1, Digest]
      i = slice.a
      fieldIndex = 0.Limit
      isActive = false
      index {.noinit.}: GeneralizedIndex
      indexLayer {.noinit.}: int
      chunks {.noinit.}: Slice[Limit]
      merkleizer {.noinit.}: SszMerkleizerImpl
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
              merkleizer = SszMerkleizerImpl(
                combinedChunks:
                  cast[ptr UncheckedArray[Digest]](addr combinedChunks),
                topIndex: chunkLayer - indexLayer)
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
          merkleizer = SszMerkleizerImpl(
            combinedChunks:
              cast[ptr UncheckedArray[Digest]](addr combinedChunks),
            topIndex: chunkLayer - indexLayer)
        rootAt(i) = getFinalHash(merkleizer)
        inc i
        isActive = false
      else: return unsupportedIndex
  else:
    unsupported T
  ok()

func mergedDataHash(x: HashArray|HashList, chunkIdx: int64): Digest =
  # The merged hash of the data at `chunkIdx` and `chunkIdx + 1`
  trs "DATA HASH ", chunkIdx, " ", x.data.len

  when x.T is BasicType:
    when cpuEndian == bigEndian:
      unsupported typeof(x) # No bigendian support here!

    let
      bytes = cast[ptr UncheckedArray[byte]](unsafeAddr x.data[0])
      byteIdx = chunkIdx * bytesPerChunk
      byteLen = x.data.len * sizeof(x.T)

    if byteIdx >= byteLen:
      zeroHashes[1]
    else:
      let
        nbytes = min(byteLen - byteIdx, 64)
        padding = 64 - nbytes

      digest(
        toOpenArray(bytes, int(byteIdx), int(byteIdx + nbytes - 1)),
        toOpenArray(zero64, 0, int(padding - 1)))
  else:
    if chunkIdx + 1 > x.data.len():
      zeroHashes[x.maxDepth]
    elif chunkIdx + 1 == x.data.len():
      mergeBranches(
        hash_tree_root(x.data[chunkIdx]),
        Digest())
    else:
      mergeBranches(
        hash_tree_root(x.data[chunkIdx]),
        hash_tree_root(x.data[chunkIdx + 1]))

template mergedHash(x: HashArray|HashList, vIdxParam: int64): Digest =
  # The merged hash of the data at `vIdx` and `vIdx + 1`
  let vIdx = vIdxParam
  if vIdx >= x.maxChunks:
    let dataIdx = vIdx - x.maxChunks
    mergedDataHash(x, dataIdx)
  else:
    mergeBranches(
      hashTreeRootCached(x, vIdx),
      hashTreeRootCached(x, vIdx + 1))

func hashTreeRootCached*(x: HashArray, vIdx: int64): Digest =
  doAssert vIdx >= 1, "Only valid for flat merkle tree indices"

  if not isCached(x.hashes[vIdx]):
    # TODO oops. so much for maintaining non-mutability.
    let px = unsafeAddr x

    px[].hashes[vIdx] = mergedHash(x, vIdx * 2)

  return x.hashes[vIdx]

func hashTreeRootCached*(x: HashList, vIdx: int64): Digest =
  doAssert vIdx >= 1, "Only valid for flat merkle tree indices"

  let
    layer = layer(vIdx)
    idxInLayer = vIdx - (1'i64 shl layer)
    layerIdx = idxInLayer + x.indices[layer]

  trs "GETTING ", vIdx, " ", layerIdx, " ", layer, " ", x.indices.len

  doAssert layer < x.maxDepth
  if layerIdx >= x.indices[layer + 1]:
    trs "ZERO ", x.indices[layer], " ", x.indices[layer + 1]
    zeroHashes[x.maxDepth - layer]
  else:
    if not isCached(x.hashes[layerIdx]):
      # TODO oops. so much for maintaining non-mutability.
      let px = unsafeAddr x

      trs "REFRESHING ", vIdx, " ", layerIdx, " ", layer

      px[].hashes[layerIdx] = mergedHash(x, vIdx * 2)
    else:
      trs "CACHED ", layerIdx

    x.hashes[layerIdx]

func hashTreeRootCached*(x: HashArray): Digest =
  hashTreeRootCached(x, 1) # Array does not use idx 0

func hashTreeRootCached*(x: HashList): Digest =
  if x.data.len == 0:
    mergeBranches(
      zeroHashes[x.maxDepth],
      zeroHashes[0]) # mixInLength with 0!
  else:
    if not isCached(x.hashes[0]):
      # TODO oops. so much for maintaining non-mutability.
      let px = unsafeAddr x
      px[].hashes[0] = mixInLength(hashTreeRootCached(x, 1), x.data.len)

    x.hashes[0]

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
      rootAt(i) = chunkedHashTreeRoot(totalChunks, x.data,
                                      chunks, indexLayer)
      inc i
    elif indexLayer < chunkLayer:
      rootAt(i) = hashTreeRootCached(x, index.int64)
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
      rootAt(i) = hashTreeRootAux(x.len.uint64)
      inc i
    elif index == 2.GeneralizedIndex:
      rootAt(i) = hashTreeRootCached(x, 1)
      inc i
    elif (index shr (indexLayer - 1)) == 2.GeneralizedIndex:
      let
        atLayer = atLayer + 1
        index = indexAt(i)
        indexLayer = log2trunc(index)
      if indexLayer == chunkLayer:
        let chunks = chunksForIndex(index)
        rootAt(i) = chunkedHashTreeRoot(totalChunks, asSeq x.data,
                                        chunks, indexLayer)
        inc i
      elif indexLayer < chunkLayer:
        rootAt(i) = hashTreeRootCached(x, index.int64)
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

func hash_tree_root*(x: auto): Digest =
  trs "STARTING HASH TREE ROOT FOR TYPE ", name(typeof(x))
  mixin toSszType

  result =
    when x is HashArray|HashList:
      hashTreeRootCached(x)
    else:
      hashTreeRootAux(toSszType(x))

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
proc cmpDepthFirst(x, y: GeneralizedIndex): int =
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
  let idx = cast[ptr UncheckedArray[GeneralizedIndex]](unsafeAddr indices[0])
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
