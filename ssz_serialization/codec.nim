# ssz_serialization
# Copyright (c) 2018-2025 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [], gcsafe.}

# Coding and decoding of primitive SSZ types - every "simple" type passed to
# and from the SSZ library must have a `fromSssBytes` and `toSszType` overload.

import
  std/typetraits,
  results,
  stew/[endians2, objects], stew/shims/macros,
  ./types

from stew/assign2 import assign

export
  types

func reallyRaiseMalformedSszError(typeName, msg: string) {.
    raises: [MalformedSszError], noinline, noreturn.} =
  # `noinline` helps keep the C code tight on the happy path
  # passing `typeName` in avoids generating generic copies of this function
  raise (ref MalformedSszError)(msg: "SSZ " & typeName & ": " & msg)

template raiseMalformedSszError*(T: type, msg: string) =
  const typeName = name(T)
  reallyRaiseMalformedSszError(typeName, msg)

template raiseIncorrectSize*(T: type) =
  raiseMalformedSszError(T, "incorrect size")

template setOutputSize[R, T](a: var array[R, T], length: int) =
  if length != a.len:
    raiseIncorrectSize a.type

func setOutputSize(list: var List, length: int) {.raises: [SszError].} =
  # We will overwrite all bytes
  if not list.setLenUninitialized length:
    raiseMalformedSszError(typeof(list), "length exceeds list limit")

func setOutputSize[T](x: var seq[T], length: int) {.raises: [SszError].} =
  # We will overwrite all bytes
  when T is SomeNumber:
    if x.len != length:
      when (NimMajor, NimMinor) < (2, 2):
        x = newSeqUninitialized[T](length)
      else:
        x = newSeqUninit[T](length)
  else:
    x.setLen(length)

# fromSszBytes copies the wire representation to a Nim variable,
# assuming there's enough data in the buffer
func fromSszBytes*(
    T: type UintN, data: openArray[byte]): T {.raises: [SszError].} =
  ## Convert directly to bytes the size of the int. (e.g. ``uint16 = 2 bytes``)
  ## All integers are serialized as **little endian**.
  if data.len != sizeof(result):
    raiseIncorrectSize T

  T.fromBytesLE(data)

func fromSszBytes*(
    T: type bool, data: openArray[byte]): T {.raises: [SszError].} =
  # Strict: only allow 0 or 1
  if data.len != 1 or byte(data[0]) > byte(1):
    raiseMalformedSszError(bool, "invalid boolean value")
  data[0] == 1

func fromSszBytes*(
    T: type Digest, data: openArray[byte]): T {.raises: [SszError], noinit.} =
  if data.len != sizeof(result.data):
    raiseIncorrectSize T
  copyMem(result.data.addr, unsafeAddr data[0], sizeof(result.data))

func `[]`[T, U, V](s: openArray[T], x: HSlice[U, V]) {.error:
  "Please don't use openArray's [] as it allocates a result sequence".}

template checkForForbiddenBits(ResulType: type,
                               input: openArray[byte],
                               expectedBits: static int64) =
  ## This checks if the input contains any bits set above the maximum
  ## sized allowed. We only need to check the last byte to verify this:
  const bitsInLastByte = (expectedBits mod 8)
  when bitsInLastByte != 0:
    # As an example, if there are 3 bits expected in the last byte,
    # we calculate a bitmask equal to 11111000. If the input has any
    # raised bits in range of the bitmask, this would be a violation
    # of the size of the BitArray:
    const forbiddenBitsMask = byte(byte(0xff) shl bitsInLastByte)

    if (input[^1] and forbiddenBitsMask) != 0:
      raiseIncorrectSize ResulType

# Compile time `isUnion` checks if the case object
# has as first field the discriminator, and that all case branches only
# have 1 field, and that no additional fields exist outside of the case
# branches. Also following rules should apply:
# - enum size range < 127 (or perhaps just max sizeof 1 byte).
# - Must have at least 1 type option.
# - Must have at least 2 type options if the first is None.
# - Empty case branch (No fields) only for first discriminator value (0).
macro isUnion*(x: type): untyped =
  let T = x.getType[1]
  let recList = T.getTypeImpl[2]

  # no additional fields exist outside of the case
  # branches
  if recList.len != 1:
    macros.error("no additional fields can exists outside of the case branches",
      recList)

  # case object has as first field the discriminator
  let recCase = recList[0]
  if recCase.kind != nnkRecCase:
    macros.error("first field should be union discriminator", recCase)

  # no need to check for this condition:
  # Must have at least 1 type option.
  # minus discriminator

  # Must have at least 2 type options if the first is None.
  let enumVal = recCase[1][0].intVal
  if enumVal == 0:
    # minus discriminator
    if recCase.len - 1 < 2:
      macros.error("union must have at least 2 type options if the first is None",
        recCase)

  # begin with 1: skip the discriminator
  for i in 1..<recCase.len:
    let branch = recCase[i]
    let recList = if branch.kind == nnkOfBranch:
                    branch[1]
                  else:
                    branch[0] # else branch

    let enumVal = if branch.kind == nnkOfBranch:
                    branch[0].intVal
                  else:
                    # assume else branch
                    # have the highest val
                    recCase.len-1

    # all case branches only have 1 field
    if recList.len > 1:
      macros.error("union branches can only have 1 field", recList)

    if enumVal >= 127:
      macros.error("enum size exceeds 127, got " & $enumVal, branch)

    # Empty case branch (No fields) only for first discriminator value (0).
    if recList.len == 0 and enumVal != 0:
      macros.error("only None discriminator can have empty case branch", recList)

  result = newEmptyNode()

macro unionSizeImpl(id: typed, x: type): untyped =
  let
    T = x.getType[1]
    recList = T.getTypeImpl[2]
    recCase = recList[0]
    kind = recCase[0][0]
    TKind = recCase[0][1]

  var hasNull = false

  result = quote do:
    case `id`.`kind`
    of `TKind`(0): 1

  # begin with 1: skip the discriminator
  for i in 1..<recCase.len:
    let branch = recCase[i]
    if branch.kind == nnkOfBranch:
      let recList = branch[1]
      let enumVal = branch[0].intVal
      if enumVal == 0:
        hasNull = true
      else:
        let field = recList[0][0]
        result.add nnkOfBranch.newTree(
          (quote do: `TKind`(`enumVal`)),
          quote do: 1 + sszSize(`id`.`field`)
        )
    else:
      # else branch
      let recList = branch[0]
      let field = recList[0][0]
      result.add nnkElse.newTree(
        quote do: 1 + sszSize(`id`.`field`)
      )

  if not hasNull:
    macros.error("no null branch detected", recCase)

func unionSize*(val: auto): int {.gcsafe, raises:[].} =
  type T = type val
  unionSizeImpl(val, T)

macro initSszUnionImpl(RecordType: type, input: openArray[byte]): untyped =
  var res = newStmtList()
  let TInst = RecordType.getTypeInst[1]
  let T = RecordType.getType[1]
  var recordDef = getImpl(T)

  for field in recordFields(recordDef):
    if (field.isDiscriminator):
      let
        selectorFieldName = field.name
        selectorFieldType = field.typ
        SelectorFieldNameLit = newLit($selectorFieldName)

      res.add quote do:
        block:
          if `input`.len == 0:
            raiseMalformedSszError(`type recordDef`, "empty union not allowed")

          var selector: `selectorFieldType`
          # `checkedEnumAssign` also checks for holes in an enum.
          if not checkedEnumAssign(selector, `input`[0]):
            raiseMalformedSszError(`type recordDef`, "union selector is out of bounds")

          var caseObj = `TInst`(`selectorFieldName`: selector)

          var fieldCount = 0
          enumInstanceSerializedFields(caseObj, fieldName, field):
            when fieldName != `SelectorFieldNameLit`:
              readSszBytes(`input`.toOpenArray(1, `input`.len - 1), field)
              fieldCount.inc()

          if fieldCount == 0: # This represents a `None` in the Union
            if `input`.len != 1:
              raiseMalformedSszError(`type recordDef`, "Union None should have no value")

          caseObj

      break

  res

func initSszUnion(T: type, input: openArray[byte]): T {.raises: [SszError].} =
  initSszUnionImpl(T, input)

proc readSszValue*[T](
    input: openArray[byte], val: var T) {.raises: [SszError].} =
  mixin fromSszBytes, toSszType, readSszBytes

  template readOffsetUnchecked(n: int): uint32 {.used.} =
    fromSszBytes(uint32, input.toOpenArray(n, n + offsetSize - 1))

  template readOffset(n: int): int {.used.} =
    let offset = readOffsetUnchecked(n)
    if offset > input.len.uint32:
      raiseMalformedSszError(
        T, "list element offset points past the end of the input")
    int(offset)

  when compiles(fromSszBytes(T, input)):
    val = fromSszBytes(T, input)
  elif val is BitList|BitSeq:
    if input.len == 0:
      raiseMalformedSszError(T, "invalid empty value")

    # Since our BitLists have an in-memory representation that precisely
    # matches their SSZ encoding, we can deserialize them as regular Lists:
    when val is BitList:
      const maxExpectedSize = (val.maxLen div 8) + 1
      type MatchingListType = List[byte, maxExpectedSize]
    else:
      type MatchingListType = seq[byte]

    when false:
      # TODO: Nim doesn't like this simple type coercion,
      #       we'll rely on `cast` for now (see below)
      # https://github.com/nim-lang/Nim/issues/22523
      readSszBytes(input, MatchingListType val)
    else:
      static:
        # As a sanity check, we verify that the coercion is accepted by the compiler:
        doAssert MatchingListType(val) is MatchingListType
      readSszBytes(input, cast[ptr MatchingListType](addr val)[])

    let resultBytesCount = len bytes(val)

    if bytes(val)[resultBytesCount - 1] == 0:
      raiseMalformedSszError(T, "missing termination")

    when val is BitList:
      if resultBytesCount == maxExpectedSize:
        checkForForbiddenBits(T, input, val.maxLen + 1)

  elif val is Digest:
    readSszBytes(input, val.data)
  elif val is HashArray:
    readSszBytes(input, toSszType(val.data))
    val.resetCache()
  elif val is HashList|List|array|seq:
    type E = typeof toSszType(declval ElemType(typeof val))
    when val is HashList:
      template v: untyped = val.data
    else:
      template v: untyped = val

    when isFixedSize(E):
      const elemSize = fixedPortionSize(E)
      when elemSize > 1:
        if input.len mod elemSize != 0:
          var ex = new SszSizeMismatchError
          ex.deserializedType = cstring typetraits.name(T)
          ex.actualSszSize = input.len
          ex.elementSize = elemSize
          raise ex

      v.setOutputSize input.len div elemSize
      when supportsBulkCopy(type v[0]):
        if v.len > 0:
          copyMem addr v[0], unsafeAddr input[0], input.len

        when val is HashList:
          # There's no selective invalidation here, because it would require a
          # potential performance tradeoff, either interfering with bulk copy,
          # or involving more verification of changed hash entries.
          val.resetCache()
      else:
        when val is HashList:
          val.resizeHashes()
          var prevValue: E

        for i in 0 ..< val.len:
          let offset = i * elemSize
          when val is HashList:
            assign(prevValue, toSszType(v[i]))
          readSszBytes(
            input.toOpenArray(offset, offset + elemSize - 1), toSszType(v[i]))
          when val is HashList:
            if prevValue != toSszType(v[i]):
              val.clearCaches(i)

        when val is HashList:
          # Unconditionally trigger small, O(1) updates to handle when the list
          # shrinks without otherwise changing.
          val.clearCaches(0)
          val.clearCaches(max(val.len - 1, 0))

    else:
      if input.len == 0:
        # This is an empty list.
        # The default initialization of the return value is fine.
        v.setOutputSize 0
        when val is HashList:
          val.resetCache()
        return
      elif input.len < offsetSize:
        raiseMalformedSszError(T, "input of insufficient size")

      var offset = readOffset 0
      if offset mod offsetSize != 0:
        raiseMalformedSszError(T, "unaligned list element offset")

      let resultLen = offset div offsetSize
      if resultLen == 0:
        # If there are too many elements, other constraints detect problems
        # (not monotonically increasing, past end of input, or last element
        # not matching up with its nextOffset properly)
        raiseMalformedSszError(T, "incorrect encoding of zero length")

      v.setOutputSize resultLen
      when val is HashList:
        val.resizeHashes()
        var prevValue: E

      for i in 1 ..< resultLen:
        let nextOffset = readOffset(i * offsetSize)
        if nextOffset < offset:
          raiseMalformedSszError(T, "list element offsets are decreasing")
        else:
          when val is HashList:
            assign(prevValue, toSszType(v[i - 1]))
          readSszBytes(
            input.toOpenArray(offset, nextOffset - 1), toSszType(v[i - 1]))
          when val is HashList:
            if prevValue != toSszType(v[i - 1]):
              val.clearCaches(i - 1)
        offset = nextOffset

      readSszBytes(
        input.toOpenArray(offset, input.len - 1), toSszType(v[resultLen - 1]))

      when val is HashList:
        # Unconditionally trigger small, O(1) updates to handle when the list
        # shrinks without otherwise changing.
        val.clearCaches(0)
        val.clearCaches(max(val.len - 1, 0))

  elif val is BitArray:
    if sizeof(val) != input.len:
      raiseIncorrectSize(T)
    checkForForbiddenBits(T, input, val.bits)
    copyMem(addr val.bytes[0], unsafeAddr input[0], input.len)

  elif val is object|tuple:
    when isCaseObject(T):
      isUnion(type(val))
      val = initSszUnion(type(val), input)
    else:
      let inputLen = uint32 input.len
      const minimallyExpectedSize = uint32 fixedPortionSize(T)

      if inputLen < minimallyExpectedSize:
        raiseMalformedSszError(T, "input of insufficient size")

      enumInstanceSerializedFields(val, fieldName, field):
        const boundingOffsets = getFieldBoundingOffsets(T, fieldName)

        # type FieldType = type field # buggy
        # For some reason, Nim gets confused about the alias here. This could be a
        # generics caching issue caused by the use of distinct types. Such an
        # issue is very scary in general.
        # The bug can be seen with the two List[uint64, N] types that exist in
        # the spec, with different N.

        type SszType = type toSszType(declval type(field))

        when isFixedSize(SszType):
          const
            startOffset = boundingOffsets[0]
            endOffset = boundingOffsets[1]
        else:
          let
            startOffset = readOffsetUnchecked(boundingOffsets[0])
            endOffset = if boundingOffsets[1] == -1: inputLen
                        else: readOffsetUnchecked(boundingOffsets[1])

          when boundingOffsets.isFirstOffset:
            if startOffset != minimallyExpectedSize:
              raiseMalformedSszError(
                T, "object dynamic portion starts at invalid offset")

          if startOffset > endOffset:
            raiseMalformedSszError(
              T, "field offsets are not monotonically increasing")
          elif endOffset > inputLen:
            raiseMalformedSszError(
              T, "field offset points past the end of the input")
          elif startOffset < minimallyExpectedSize:
            raiseMalformedSszError(
              T, "field offset points outside bounding offsets")

        # TODO The extra type escaping here is a work-around for a Nim issue:
        when type(field) is type(SszType):
          readSszBytes(
            input.toOpenArray(int(startOffset), int(endOffset - 1)),
            field)
        else:
          field = fromSszBytes(
            type(field),
            input.toOpenArray(int(startOffset), int(endOffset - 1)))

  else:
    unsupported T

# Identity conversions for core SSZ types

template toSszType*(v: auto): auto =
  ## toSszType converts a given value into one of the primitive types supported
  ## by SSZ - to add support for a custom type (for example a `distinct` type),
  ## add an overload for `toSszType` which converts it to one of the `SszType`
  ## types, as well as a `fromSszBytes`.
  type T = type(v)
  when T is SszType:
    when T is Digest:
      v.data
    else:
      v
  else:
    unsupported T
