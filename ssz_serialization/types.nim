# ssz_serialization
# Copyright (c) 2018-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  std/[tables, typetraits, strformat],
  stew/shims/macros, stew/[assign2, byteutils, bitops2, objects],
  results,
  stint,
  nimcrypto/hash,
  serialization/[object_serialization, errors],
  json_serialization,
  "."/bitseqs

from nimcrypto/utils import fromHex  # needed to disambiguate properly

export stint, bitseqs, json_serialization

const
  offsetSize* = 4
  bytesPerChunk* = 32

type
  GeneralizedIndex* = uint64

  UintN* = SomeUnsignedInt|UInt128|UInt256
  BasicType* = bool|UintN
  OptionalType* = Option|Opt

  Limit* = int64

  Digest* = MDigest[32 * 8]

# A few index types from here onwards:
# * dataIdx - leaf index starting from 0 to maximum length of collection
# * chunkIdx - leaf data index after chunking starting from 0
# * vIdx - virtual index in Merkle tree - the root is found at index 1, its
#          two children at 2, 3 then 4, 5, 6, 7 etc

func nextPow2Int64(x: int64): int64 =
  # TODO the nextPow2 in bitops2 works with uint64 - there's a bug in the nim
  #      compiler preventing it to be used - it seems that a conversion to
  #      uint64 cannot be done with the static maxLen :(
  #
  #      Works in Nim 2.0 and newer, so remove workaround when Nim 1.6 support
  #      is dropped
  var v = x - 1

  # round down, make sure all bits are 1 below the threshold, then add 1
  v = v or v shr 1
  v = v or v shr 2
  v = v or v shr 4
  when bitsof(x) > 8:
    v = v or v shr 8
  when bitsof(x) > 16:
    v = v or v shr 16
  when bitsof(x) > 32:
    v = v or v shr 32

  v + 1

template dataPerChunk(T: type): int =
  # How many data items fit in a chunk
  mixin toSszType
  const isCompressed =
    when compiles(typeof toSszType(declval T)):
      (typeof toSszType(declval T)) is BasicType
    else:
      T is BasicType
  when isCompressed:
    bytesPerChunk div sizeof(T)
  else:
    1

template chunkIdx*(T: type, dataIdx: int64): int64 =
  # Given a data index, which chunk does it belong to?
  dataIdx div dataPerChunk(T)

template maxChunkIdx*(T: type, maxLen: Limit): int64 =
  # Given a number of data items, how many chunks are needed?
  # TODO compiler bug:
  # beacon_chain/ssz/types.nim(75, 53) Error: cannot generate code for: maxLen
  # nextPow2(chunkIdx(T, maxLen + dataPerChunk(T) - 1).uint64).int64
  nextPow2Int64(chunkIdx(T, maxLen.int64 + dataPerChunk(T) - 1))

template layer*(vIdx: int64): int =
  ## Layer 0 = layer at which the root hash is
  ## We place the root hash at index 1 which simplifies the math and leaves
  ## index 0 for the mixed-in-length
  log2trunc(vIdx.uint64).int

func hashListIndicesLen(maxChunkIdx: int64): int =
  # TODO: This exists only to work-around a compilation issue when the complex
  # expression is used directly in the HastList array size definition below
  # https://github.com/nim-lang/Nim/issues/22491
  int(layer(maxChunkIdx)) + 1

type
  List*[T; maxLen: static Limit] = distinct seq[T]
  BitList*[maxLen: static Limit] = distinct BitSeq

  HashArray*[maxLen: static Limit; T] = object
    ## Array implementation that caches the hash of each chunk of data - see
    ## also HashList for more details.
    data*: array[maxLen, T]
    hashes* {.dontSerialize.}: array[max(maxChunkIdx(T, maxLen), 2), Digest]

  HashList*[T; maxLen: static Limit] = object
    ## List implementation that caches the hash of each chunk of data as well
    ## as the combined hash of each level of the Merkle tree using a flattened
    ## list of hashes.
    ##
    ## The Merkle tree of a list is formed by imagining a virtual buffer of
    ## `maxLen` length which is zero-filled where there is no data. Then,
    ## a Merkle tree of hashes is formed as usual - at each level of the tree,
    ## iff the hash is combined from two zero-filled chunks, the hash is not
    ## stored in the `hashes` list - instead, `indices` keeps track of where in
    ## the list each level starts. When the length of `data` changes, the
    ## `hashes` and `indices` structures must be updated accordingly using
    ## `resizeHashes`.
    ##
    ## All mutating operators (those that take `var HashList`) will
    ## automatically invalidate the cache for the relevant chunks - the leaf and
    ## all intermediate chunk hashes up to the root. When large changes are made
    ## to `data`, it might be more efficient to batch the updates then reset
    ## the cache using resetCache` instead.

    data*: List[T, maxLen]
    hashes* {.dontSerialize.}: seq[Digest] ## \
      ## Flattened tree store that skips "empty" branches of the tree - the
      ## starting index in this sequence of each "level" in the tree is found
      ## in `indices`.
    indices* {.dontSerialize.}: array[
        hashListIndicesLen(max(maxChunkIdx(T, maxLen), 2)), int64] ##\
      ## Holds the starting index in the hashes list for each level of the tree

  # Note for readers:
  # We use `array` for `Vector` and
  #        `BitArray` for `BitVector`

  SszError* = object of SerializationError

  MalformedSszError* = object of SszError

  SszSizeMismatchError* = object of SszError
    deserializedType*: cstring
    actualSszSize*: int
    elementSize*: int

  # These are directly supported by the SSZ library - anything that's not
  # covered here needs to create overloads for toSszType / fromSszBytes
  # (basic types) or writeValue / readValue (complex types)
  SszType* =
    BasicType | array | HashArray | List | HashList | BitArray | BitList |
    Digest | object | tuple

  # Convenience aliases from specification
  ByteList*[maxLen: static Limit] = List[byte, maxLen]
  ByteVector*[maxLen: static Limit] = array[maxLen, byte]

template asSeq*(x: List): auto = distinctBase(x)

template init*[T, N](L: type List[T, N], x: seq[T]): auto =
  List[T, N](x)

template `$`*(x: List): auto = $(distinctBase(x))
template len*(x: List): auto = len(distinctBase(x))
template low*(x: List): auto = low(distinctBase(x))
template high*(x: List): auto = high(distinctBase(x))
template `[]`*(x: List, idx: auto): untyped = distinctBase(x)[idx]
template `[]=`*(x: var List, idx: auto, val: auto) = distinctBase(x)[idx] = val
template `==`*(a, b: List): bool = distinctBase(a) == distinctBase(b)

template `&`*(a, b: List): auto = (type(a)(distinctBase(a) & distinctBase(b)))

template items* (x: List): untyped = items(distinctBase(x))
template pairs* (x: List): untyped = pairs(distinctBase(x))
template mitems*(x: var List): untyped = mitems(distinctBase(x))
template mpairs*(x: var List): untyped = mpairs(distinctBase(x))
template contains* (x: List, val: auto): untyped = contains(distinctBase(x), val)

func add*(x: var List, val: auto): bool =
  if x.len < x.maxLen:
    add(distinctBase(x), val)
    true
  else:
    false

func setLenUninitialized*(x: var List, newLen: int): bool =
  if newLen <= x.maxLen:
    # TODO https://github.com/nim-lang/Nim/issues/19727
    when List.T is SomeNumber:
      if x.len !=  newLen:
        distinctBase(x) = when (NimMajor, NimMinor) < (2, 2):
                            newSeqUninitialized[x.T](newLen)
                          else:
                            newSeqUninit[x.T](newLen)
    else:
      setLen(distinctBase(x), newLen)
    true
  else:
    false

func setLen*(x: var List, newLen: int): bool =
  if newLen <= x.maxLen:
    setLen(distinctBase(x), newLen)
    true
  else:
    false

template init*(L: type BitList, x: seq[byte], N: static Limit): auto =
  BitList[N](data: x)

template init*[N](L: type BitList[N], x: seq[byte]): auto =
  L(data: x)

template init*(T: type BitList, len: int): auto = T init(BitSeq, len)
template len*(x: BitList): auto = len(BitSeq(x))
template bytes*(x: BitList): auto = seq[byte](x)
template `[]`*(x: BitList, idx: auto): auto = BitSeq(x)[idx]
template `[]=`*(x: var BitList, idx: auto, val: bool) = BitSeq(x)[idx] = val
template `==`*(a, b: BitList): bool = BitSeq(a) == BitSeq(b)
template setBit*(x: var BitList, idx: Natural) = setBit(BitSeq(x), idx)
template getBit*(x: var BitList, idx: Natural): bool = getBit(BitSeq(x), idx)
template clearBit*(x: var BitList, idx: Natural) = clearBit(BitSeq(x), idx)
template overlaps*(a, b: BitList): bool = overlaps(BitSeq(a), BitSeq(b))
template incl*(a: var BitList, b: BitList) = incl(BitSeq(a), BitSeq(b))
template isSubsetOf*(a, b: BitList): bool = isSubsetOf(BitSeq(a), BitSeq(b))
template isZeros*(x: BitList): bool = isZeros(BitSeq(x))
template countOnes*(x: BitList): int = countOnes(BitSeq(x))
template countZeros*(x: BitList): int = countZeros(BitSeq(x))
template countOverlap*(x, y: BitList): int = countOverlap(BitSeq(x), BitSeq(y))
template `$`*(a: BitList): string = $(BitSeq(a))

iterator items*(x: BitList): bool =
  for i in 0 ..< x.len:
    yield x[i]

iterator pairs*(x: BitList): (int, bool) =
  for i in 0 ..< x.len:
    yield (i, x[i])

template isCached*(v: Digest): bool =
  ## An entry is "in the cache" if the first 8 bytes are zero - conveniently,
  ## Nim initializes values this way, and while there may be false positives,
  ## that's fine.

  when nimvm:
    v.data.toOpenArray(0, sizeof(uint64) - 1) !=
      default(array[sizeof(uint64), byte])
  else:
    # Checking and resetting the cache status are hotspots - profile before
    # touching!
    var tmp {.noinit.}: uint64
    copyMem(addr tmp, unsafeAddr v.data[0], sizeof(tmp))
    tmp != 0

template clearCache*(v: var Digest) =
  zeroMem(addr v.data[0], sizeof(uint64))

template maxChunks*(a: HashList|HashArray): int64 =
  ## Layer where data is
  const v = maxChunkIdx(a.T, a.maxLen) # force compile-time eval
  static: doAssert (v mod 2 == 0) or (v == 1)
  v

template maxDepth*(a: HashList|HashArray): int =
  ## Layer where data is
  static: doAssert a.maxChunks <= high(int64) div 2
  const v = layer(nextPow2(a.maxChunks.uint64).int64) # force compile-time eval
  v

template chunkIdx(a: HashList|HashArray, dataIdx: int64): int64 =
  chunkIdx(a.T, dataIdx)

func clearCaches*(a: var HashArray, dataIdx: auto) =
  ## Clear all cache entries after data at dataIdx has been modified
  var idx = 1 shl (a.maxDepth - 1) + (chunkIdx(a, dataIdx) shr 1)
  while idx != 0:
    clearCache(a.hashes[idx])
    idx = idx shr 1

func nodesAtLayer*(layer, depth, leaves: int): int =
  ## Given a number of leaves, how many nodes do you need at a given layer
  ## in a binary tree structure?
  let leavesPerNode = 1'i64 shl (depth - layer)
  int((leaves + leavesPerNode - 1) div leavesPerNode)

func cacheNodes*(depth, leaves: int): int =
  ## Total number of nodes needed to cache a tree of a given depth with
  ## `leaves` items in it - chunks that are zero-filled have well-known hash
  ## trees and don't need to be stored in the tree.
  var res = 0
  for i in 0..<depth:
    res += nodesAtLayer(i, depth, leaves)
  res

# Indicates that after growing, the hashes, while they'll be considered cached,
# also do not allow inference that layers nearer the Merkle hash tree have also
# been cleared and that the hash cache clearing must continue to the root.
#
# False positives are possible, but harmless: if a cleared entry coincidentally
# matches this pattern, then it inefficiently recomputes some Merkle tree nodes
# and still creates a correct result.
const uninitSentinel = Digest(data: [
  byte 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1])

# Aside from these conditions, the specific value of the sentinel is arbitrary.
static:
  doAssert uninitSentinel != default(Digest)
  doAssert not uninitSentinel.isCached

func clearCaches*(a: var HashList, dataIdx: int64) =
  ## Clear each level of the Merkle tree up to the root affected by a data
  ## change at `dataIdx`.
  if a.hashes.len == 0:
    return

  var
    idx = 1'i64 shl (a.maxDepth - 1) + (chunkIdx(a, dataIdx) shr 1)
    layer = a.maxDepth - 1
  while idx > 0:
    let
      idxInLayer = idx - (1'i64 shl layer)
      layerIdx = idxInLayer + a.indices[layer]

    if layerIdx < a.indices[layer + 1]:
      if  (not isCached(a.hashes[layerIdx])) and
          a.hashes[layerIdx] != uninitSentinel:
        return

      # Only clear cache when we're actually storing it - ie it hasn't been
      # skipped by the "combined zero hash" optimization
      clearCache(a.hashes[layerIdx])

    idx = idx shr 1
    layer = layer - 1

  clearCache(a.hashes[0])

func clearCache*(a: var HashList) =
  # Clear the full Merkle tree, in anticipation of a complete rewrite of the
  # contents
  for c in a.hashes.mitems(): clearCache(c)

func resizeHashes*(a: var HashList) =
  ## Ensure the hash cache is the correct size for the data in the list - must
  ## be called whenever `data` shrinks or grows.
  let
    leaves = int(
      chunkIdx(a, a.data.len() + dataPerChunk(a.T) - 1))
    newSize = 1 + max(cacheNodes(a.maxDepth, leaves), 1)

  # Growing might be because of add(), addDefault(), or in-place reading of a
  # larger HashList. In-place reading of a smaller HashList causes shrinking.
  if a.hashes.len == newSize:
    return

  var
    newHashes = newSeq[Digest](newSize)
    newIndices = default(type a.indices)

  # newSeqWith already does this, just with potentially less efficient `=`
  # rather than assign(): https://github.com/nim-lang/Nim/issues/22554
  for i in 0 ..< newSize:
    assign(newHashes[i], uninitSentinel)

  newIndices[0] = nodesAtLayer(0, a.maxDepth, leaves)
  for i in 1 .. max(a.maxDepth, 1):
    newIndices[i] =
      newIndices[i - 1] + nodesAtLayer(i - 1, a.maxDepth, leaves)

  # When shrinking, truncate each layer
  for i in 1 ..< max(a.maxDepth, 1):
    for j in 0 ..< min(
        a.indices[i] - a.indices[i-1], newIndices[i] - newIndices[i - 1]):
      newHashes[newIndices[i - 1] + j] = a.hashes[a.indices[i - 1] + j]

  swap(a.hashes, newHashes)
  a.indices = newIndices

func resetCache*(a: var HashList) =
  ## Perform a full reset of the hash cache, for example after data has been
  ## rewritten "manually" without going through the exported operators
  a.hashes.setLen(0)
  a.indices = default(type a.indices)
  a.resizeHashes()

func resetCache*(a: var HashArray) =
  for h in a.hashes.mitems():
    clearCache(h)

template len*(a: type HashArray): auto = int(a.maxLen)

func add*(x: var HashList, val: auto): bool =
  if add(x.data, val):
    x.resizeHashes()
    if x.data.len() > 0:
      # Otherwise, adding an empty list to an empty list fails
      clearCaches(x, x.data.len() - 1)
    true
  else:
    false

func addDefault*(x: var HashList): ptr x.T =
  if x.data.len >= x.maxLen:
    return nil

  distinctBase(x.data).setLen(x.data.len + 1)
  x.resizeHashes()
  clearCaches(x, x.data.len() - 1)
  addr x.data[^1]

template init*[T, N](L: type HashList[T, N], x: seq[T]): auto =
  var tmp = HashList[T, N](data: List[T, N].init(x))
  tmp.resizeHashes()
  tmp

template len*(x: HashList|HashArray): auto = len(x.data)
template low*(x: HashList|HashArray): auto = low(x.data)
template high*(x: HashList|HashArray): auto = high(x.data)
template `[]`*(x: HashList|HashArray, idx: auto): auto = x.data[idx]
template `[]`*(x: var HashList, idx: auto): auto =
  {.fatal: "Use item / mitem with `var HashXxx` to differentiate read/write access".}
  discard
template `[]`*(x: var HashArray, idx: auto): auto =
  {.fatal: "Use item / mitem with `var HashXxx` to differentiate read/write access".}
  discard

template item*(x: HashList|HashArray, idx: auto): auto =
  # We must use a template, or the magic `unsafeAddr x[idx]` won't work, but
  # we don't want to accidentally return a `var` instance that gets mutated
  # so we avoid overloading the `[]` name
  x.data[idx]

func mitem*(a: var HashArray, b: auto): var a.T =
  # Access mutable item clearing its cache
  clearCaches(a, b.Limit)
  a.data[b]

func `[]=`*(a: var HashArray, b: auto, c: auto) =
  clearCaches(a, b.Limit)
  a.data[b] = c

func mitem*(x: var HashList, idx: auto): var x.T =
  # Access mutable item clearing its cache
  clearCaches(x, idx.int64)
  x.data[idx]

func `[]=`*(x: var HashList, idx: auto, val: auto) =
  clearCaches(x, idx.int64)
  x.data[idx] = val

template `==`*(a, b: HashList|HashArray): bool = a.data == b.data
template asSeq*(x: HashList): auto = asSeq(x.data)
template `$`*(x: HashList): auto = $(x.data)

template items* (x: HashList|HashArray): untyped = items(x.data)
template pairs* (x: HashList|HashArray): untyped = pairs(x.data)

template swap*(a, b: var HashList) =
  swap(a.data, b.data)
  swap(a.hashes, b.hashes)
  swap(a.indices, b.indices)

template clear*(a: var HashList) =
  if not a.data.setLen(0):
    raiseAssert "length 0 should always succeed"
  a.hashes.setLen(0)
  a.indices = default(type a.indices)

template fill*(a: var HashArray, c: auto) =
  mixin fill
  fill(a.data, c)
template sum*[maxLen; T](a: var HashArray[maxLen, T]): T =
  mixin sum
  sum(a.data)

macro unsupported*(T: typed): untyped =
  # TODO: {.fatal.} breaks compilation even in `compiles()` context,
  # so we use this macro instead. It's also much better at figuring
  # out the actual type that was used in the instantiation.
  # File both problems as issues.
  when T is enum:
    error "Nim `enum` types map poorly to SSZ and make it easy to introduce security issues because of spurious Defect's"
  else:
    error "SSZ serialization of the type " & humaneTypeName(T) & " is not supported, overload toSszType and fromSszBytes"

template ElemType*(T0: type OptionalType): untyped =
  T0.T

template ElemType*(T0: type HashArray): untyped =
  T0.T

template ElemType*(T0: type HashList): untyped =
  T0.T

template ElemType*(T: type array): untyped =
  type(default(T)[low(T)])

template ElemType*(T: type seq): untyped =
  type(default(T)[0])

template ElemType*(T0: type List): untyped =
  T0.T

func supportsBulkCopy*(T: type): bool {.compileTime.} =
  # Bulk copy types are those that match the following requirements:
  # * have no padding / alignment differences compared to their raw SSZ encoding
  # * have no validity constraints (ie bool which must be 0/1)
  # * supportsCopyMem (of course)
  when T is array:
    supportsBulkCopy(ElemType(T))
  elif T is Digest:
    true
  else:
    when cpuEndian == bigEndian:
      T is byte
    else:
      T is UintN

func isFixedSize*(T0: type): bool {.compileTime.} =
  mixin toSszType, enumAllSerializedFields

  type T = type toSszType(default T0)

  when T is BasicType:
    return true
  elif T is array|HashArray:
    return isFixedSize(ElemType(T))
  elif T is OptionalType:
    return false
  elif T is object|tuple:
    when isCaseObject(T):
      return false
    else:
      enumAllSerializedFields(T):
        when not isFixedSize(FieldType):
          return false
      return true

func fixedPortionSize*(T0: type): int {.compileTime.} =
  mixin enumAllSerializedFields, toSszType

  type T = type toSszType(declval T0)

  when T is BasicType: sizeof(T)
  elif T is array|HashArray:
    type E = ElemType(T)
    when isFixedSize(E): int(len(T)) * fixedPortionSize(E)
    else: int(len(T)) * offsetSize
  elif T is object|tuple:
    enumAllSerializedFields(T):
      when isFixedSize(FieldType):
        result += fixedPortionSize(FieldType)
      else:
        result += offsetSize
  else:
    unsupported T0

func minSize*(T0: type): int {.compileTime.} =
  mixin enumAllSerializedFields, toSszType

  type T = type toSszType(declval T0)

  when isFixedSize(T):
    fixedPortionSize(T)
  elif T is array|HashArray:
    type E = ElemType(T)
    static: doAssert not isFixedSize(E)
    T.len * (offsetSize + minSize(E))
  elif T is List|HashList:
    0
  elif T is BitList:
    1  # Trailing 1-bit
  elif T is object:
    var res = fixedPortionSize(T)
    enumAllSerializedFields(T):
      when not isFixedSize(FieldType):
        res += minSize(FieldType)
    res
  else:
    unsupported T0

func maxSize*(T0: type): int {.compileTime.} =
  mixin enumAllSerializedFields, toSszType

  type T = type toSszType(declval T0)

  when isFixedSize(T):
    fixedPortionSize(T)
  elif T is array|HashArray:
    type E = ElemType(T)
    static: doAssert not isFixedSize(E)
    T.len * (offsetSize + maxSize(E))
  elif T is List|HashList:
    type E = ElemType(T)
    when isFixedSize(E):
      T.maxLen * fixedPortionSize(E)
    else:
      T.maxLen * (offsetSize + maxSize(E))
  elif T is BitList:
    ((T.maxLen + 1) + 7) div 8
  elif T is object:
    var res = fixedPortionSize(T)
    enumAllSerializedFields(T):
      when not isFixedSize(FieldType):
        res += maxSize(FieldType)
    res
  else:
    unsupported T0

iterator fieldInfos(RecordType: type): tuple[name: string,
                                             offset: int,
                                             fixedSize: int,
                                             branchKey: string] =
  mixin enumAllSerializedFields

  var
    offsetInBranch = {"": 0}.toTable
    nestedUnder = initTable[string, string]()

  enumAllSerializedFields(RecordType):
    const
      isFixed = isFixedSize(FieldType)
      fixedSize = when isFixed: fixedPortionSize(FieldType)
                  else: 0
      branchKey = when  fieldCaseDiscriminator.len == 0: ""
                  else: fieldCaseDiscriminator & ":" & $fieldCaseBranches
      fieldSize = when isFixed: fixedSize
                  else: offsetSize

    nestedUnder[fieldName] = branchKey

    var fieldOffset: int
    offsetInBranch.withValue(branchKey, val):
      fieldOffset = val[]
      val[] += fieldSize
    do:
      try:
        let parentBranch = nestedUnder.getOrDefault(fieldCaseDiscriminator, "")
        fieldOffset = offsetInBranch[parentBranch]
        offsetInBranch[branchKey] = fieldOffset + fieldSize
      except KeyError as e:
        raiseAssert e.msg

    yield (fieldName, fieldOffset, fixedSize, branchKey)

func getFieldBoundingOffsetsImpl(RecordType: type,
                                 fieldName: static string):
     tuple[fieldOffset, nextFieldOffset: int, isFirstOffset: bool] {.compileTime.} =
  result = (-1, -1, false)
  var fieldBranchKey: string
  var isFirstOffset = true

  for f in fieldInfos(RecordType):
    if fieldName == f.name:
      result[0] = f.offset
      if f.fixedSize > 0:
        result[1] = result[0] + f.fixedSize
        return
      else:
        fieldBranchKey = f.branchKey
      result.isFirstOffset = isFirstOffset

    elif result[0] != -1 and
         f.fixedSize == 0 and
         f.branchKey == fieldBranchKey:
      # We have found the next variable sized field
      result[1] = f.offset
      return

    if f.fixedSize == 0:
      isFirstOffset = false

func getFieldBoundingOffsets*(RecordType: type,
                              fieldName: static string):
     tuple[fieldOffset, nextFieldOffset: int, isFirstOffset: bool] {.compileTime.} =
  ## Returns the start and end offsets of a field.
  ##
  ## For fixed-size fields, the start offset points to the first
  ## byte of the field and the end offset points to 1 byte past the
  ## end of the field.
  ##
  ## For variable-size fields, the returned offsets point to the
  ## statically known positions of the 32-bit offset values written
  ## within the SSZ object. You must read the 32-bit values stored
  ## at the these locations in order to obtain the actual offsets.
  ##
  ## For variable-size fields, the end offset may be -1 when the
  ## designated field is the last variable sized field within the
  ## object. Then the SSZ object boundary known at run-time marks
  ## the end of the variable-size field.
  type T = RecordType
  anonConst getFieldBoundingOffsetsImpl(T, fieldName)

template enumerateSubFields*(holder, fieldVar, body: untyped) =
  enumInstanceSerializedFields(holder, _{.used.}, fieldVar): body

method formatMsg*(
  err: ref SszSizeMismatchError,
  filename: string): string {.gcsafe, raises: [].} =
  try:
    &"SSZ size mismatch, element {err.elementSize}, actual {err.actualSszSize}, type {err.deserializedType}, file {filename}"
  except CatchableError:
    "SSZ size mismatch"

template readValue*(reader: var JsonReader, value: var List) =
  mixin readValue
  when type(value[0]) is byte:
    value = type(value)(utils.fromHex(reader.readValue(string)))
  else:
    value = type(value)(readValue(reader, seq[type value[0]]))

template writeValue*(writer: var JsonWriter, value: List) =
  when type(value[0]) is byte:
    writeValue(writer, to0xHex(distinctBase(value)))
  else:
    writeValue(writer, asSeq value)

proc writeValue*(
    writer: var JsonWriter, value: HashList) {.raises: [IOError].} =
  writeValue(writer, value.data)

proc readValue*(reader: var JsonReader, value: var HashList)
               {.raises: [IOError, SerializationError].} =
  readValue(reader, value.data)

template readValue*(reader: var JsonReader, value: var BitList) =
  type T = type(value)
  value = T readValue(reader, BitSeq)

template writeValue*(writer: var JsonWriter, value: BitList) =
  writeValue(writer, BitSeq value)
