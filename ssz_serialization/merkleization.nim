# ssz_serialization
# Copyright (c) 2018-2021 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

# This module contains the parts necessary to create a merkle hash from the core
# SSZ types outlined in the spec:
# https://github.com/ethereum/consensus-specs/blob/v1.0.1/ssz/simple-serialize.md#merkleization

{.push raises: [Defect].}

import
  stew/[bitops2, endians2, ptrops],
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
  codec, bitseqs, types

when hasSerializationTracing:
  import stew/byteutils, typetraits

const
  zero64 = default array[64, byte]
  bitsPerChunk = bytesPerChunk * 8

func binaryTreeHeight*(totalElements: Limit): int =
  bitWidth nextPow2(uint64 totalElements)

type
  # TODO Figure out what would be the right type for this.
  #      It probably fits in uint16 for all practical purposes.
  GeneralizedIndex* = uint32

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
        var h  {.inject, noInit.}: DigestCtx
        init(h)
        body
        var res {.noInit.}: Digest
        finalize(res.data, h)
        res
    else:
      block:
        var h  {.inject, noInit.}: DigestCtx
        init(h)
        body
        finish(h)

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

template createMerkleizer*(totalElements: static Limit): SszMerkleizerImpl =
  trs "CREATING A MERKLEIZER FOR ", totalElements

  const treeHeight = binaryTreeHeight totalElements
  var combinedChunks {.noInit.}: array[treeHeight, Digest]

  let topIndex = treeHeight - 1

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

template merkleizeFields(totalChunks: static Limit, body: untyped): Digest =
  var merkleizer {.inject.} = createMerkleizer(totalChunks)

  template addField(field) =
    let hash = hash_tree_root(field)
    trs "MERKLEIZING FIELD ", astToStr(field), " = ", hash
    addChunk(merkleizer, hash.data)
    trs "CHUNK ADDED"

  body

  getFinalHash(merkleizer)

template writeBytesLE(chunk: var array[bytesPerChunk, byte], atParam: int,
                      val: UintN) =
  let at = atParam
  chunk[at ..< at + sizeof(val)] = toBytesLE(val)

func chunkedHashTreeRoot[T: BasicType](
    merkleizer: var SszMerkleizerImpl, arr: openArray[T]): Digest =
  static:
    doAssert bytesPerChunk mod sizeof(T) == 0

  if arr.len == 0:
    return getFinalHash(merkleizer)

  when sizeof(T) == 1 or cpuEndian == littleEndian:
    var
      remainingBytes = arr.len * sizeof(T)
      pos = cast[ptr byte](unsafeAddr arr[0])

    while remainingBytes >= bytesPerChunk:
      addChunk(merkleizer, makeOpenArray(pos, bytesPerChunk))
      pos = offset(pos, bytesPerChunk)
      remainingBytes -= bytesPerChunk

    if remainingBytes > 0:
      addChunk(merkleizer, makeOpenArray(pos, remainingBytes))

  else:
    const valuesPerChunk = bytesPerChunk div sizeof(T)

    var writtenValues = 0

    var chunk: array[bytesPerChunk, byte]
    while writtenValues < arr.len - valuesPerChunk:
      for i in 0 ..< valuesPerChunk:
        chunk.writeBytesLE(i * sizeof(T), arr[writtenValues + i])
      addChunk(merkleizer, chunk)
      inc writtenValues, valuesPerChunk

    let remainingValues = arr.len - writtenValues
    if remainingValues > 0:
      var lastChunk: array[bytesPerChunk, byte]
      for i in 0 ..< remainingValues:
        lastChunk.writeBytesLE(i * sizeof(T), arr[writtenValues + i])
      addChunk(merkleizer, lastChunk)

  getFinalHash(merkleizer)

template chunkedHashTreeRoot[T: not BasicType](
    merkleizer: var SszMerkleizerImpl, arr: openArray[T]): Digest =
  for elem in arr:
    let elemHash = hash_tree_root(elem)
    addChunk(merkleizer, elemHash.data)
  getFinalHash(merkleizer)

func bitListHashTreeRoot(merkleizer: var SszMerkleizerImpl, x: BitSeq): Digest =
  # TODO: Switch to a simpler BitList representation and
  #       replace this with `chunkedHashTreeRoot`
  var
    totalBytes = bytes(x).len
    lastCorrectedByte = bytes(x)[^1]

  if lastCorrectedByte == byte(1):
    if totalBytes == 1:
      # This is an empty bit list.
      # It should be hashed as a tree containing all zeros:
      return mergeBranches(zeroHashes[merkleizer.topIndex],
                           zeroHashes[0]) # this is the mixed length

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

  for i in 0 ..< fullChunks:
    let
      chunkStartPos = i * bytesPerChunk
      chunkEndPos = chunkStartPos + bytesPerChunk - 1

    addChunk(merkleizer, bytes(x).toOpenArray(chunkStartPos, chunkEndPos))

  var
    lastChunk: array[bytesPerChunk, byte]
    chunkStartPos = fullChunks * bytesPerChunk

  for i in 0 .. bytesInLastChunk - 2:
    lastChunk[i] = bytes(x)[chunkStartPos + i]

  lastChunk[bytesInLastChunk - 1] = lastCorrectedByte

  addChunk(merkleizer, lastChunk.toOpenArray(0, bytesInLastChunk - 1))
  let contentsHash = getFinalHash(merkleizer)
  mixInLength contentsHash, x.len

func maxChunksCount(T: type, maxLen: Limit): Limit =
  when T is BitArray|BitList:
    (maxLen + bitsPerChunk - 1) div bitsPerChunk
  elif T is array|List:
    maxChunkIdx(ElemType(T), maxLen)
  else:
    unsupported T # This should never happen

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
    var merkleizer = createMerkleizer(totalChunks)
    bitListHashTreeRoot(merkleizer, BitSeq x)
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
      var merkleizer = createMerkleizer(totalChunks)
      chunkedHashTreeRoot(merkleizer, x)
  elif T is List:
    const totalChunks = maxChunksCount(T, x.maxLen)
    var merkleizer = createMerkleizer(totalChunks)
    let contentsHash = chunkedHashTreeRoot(merkleizer, asSeq x)
    mixInLength(contentsHash, x.len)
  elif T is SingleMemberUnion:
    doAssert x.selector == 0'u8
    merkleizeFields(Limit 2):
      addField hashTreeRoot(toSszType(x.value))
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
    layerIdx = idxInlayer + x.indices[layer]

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

func hash_tree_root*(x: auto): Digest =
  trs "STARTING HASH TREE ROOT FOR TYPE ", name(typeof(x))
  mixin toSszType

  result =
    when x is HashArray|HashList:
      hashTreeRootCached(x)
    else:
      hashTreeRootAux(toSszType(x))

  trs "HASH TREE ROOT FOR ", name(typeof(x)), " = ", "0x", $result
