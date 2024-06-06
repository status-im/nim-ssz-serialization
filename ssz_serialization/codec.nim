# ssz_serialization
# Copyright (c) 2018-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

# Coding and decoding of primitive SSZ types - every "simple" type passed to
# and from the SSZ library must have a `fromSssBytes` and `toSszType` overload.

import
  std/typetraits,
  stew/[endians2, objects, results], stew/shims/macros,
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

template fromSszBytes*(T: type BitSeq, bytes: openArray[byte]): auto =
  BitSeq @bytes

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
          # TODO: `checkedEnumAssign` does not check for holes in an enum.
          # SSZ Union spec also doesn't allow this, so it should be fine, but
          # nothing stops currently defining an enum with holes and such data
          # will also be parsed and result in an object like:
          # `(selector: 2 (invalid data!))`
          if not checkedEnumAssign(selector, `input`[0]):
            raiseMalformedSszError(`type recordDef`, "union selector is out of bounds")

          var caseObj = `TInst`(`selectorFieldName`: selector)

          enumInstanceSerializedFields(caseObj, fieldName, field):
            when fieldName != `SelectorFieldNameLit`:
              readSszValue(`input`.toOpenArray(1, `input`.len - 1), field)

          caseObj

      break

  res

func initSszUnion(T: type, input: openArray[byte]): T {.raises: [SszError].} =
  initSszUnionImpl(T, input)

proc readSszValue*[T](
    input: openArray[byte], val: var T) {.raises: [SszError].} =
  mixin fromSszBytes, toSszType, readSszValue

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
  elif val is BitList:
    if input.len == 0:
      raiseMalformedSszError(T, "invalid empty value")

    # Since our BitLists have an in-memory representation that precisely
    # matches their SSZ encoding, we can deserialize them as regular Lists:
    const maxExpectedSize = (val.maxLen div 8) + 1
    type MatchingListType = List[byte, maxExpectedSize]

    when false:
      # TODO: Nim doesn't like this simple type coercion,
      #       we'll rely on `cast` for now (see below)
      # https://github.com/nim-lang/Nim/issues/22523
      readSszValue(input, MatchingListType val)
    else:
      static:
        # As a sanity check, we verify that the coercion is accepted by the compiler:
        doAssert MatchingListType(val) is MatchingListType
      readSszValue(input, cast[ptr MatchingListType](addr val)[])

    let resultBytesCount = len bytes(val)

    if bytes(val)[resultBytesCount - 1] == 0:
      raiseMalformedSszError(T, "missing termination")

    if resultBytesCount == maxExpectedSize:
      checkForForbiddenBits(T, input, val.maxLen + 1)

  elif val is HashList:
    type E = typeof toSszType(declval ElemType(typeof val))

    when isFixedSize(E):
      const elemSize = fixedPortionSize(E)
      when elemSize > 1:
        if input.len mod elemSize != 0:
          var ex = new SszSizeMismatchError
          ex.deserializedType = cstring typetraits.name(T)
          ex.actualSszSize = input.len
          ex.elementSize = elemSize
          raise ex

      val.data.setOutputSize input.len div elemSize
      when supportsBulkCopy(type E):
        if val.data.len > 0:
          copyMem addr val.data[0], unsafeAddr input[0], input.len

        # There's no selective invalidation here, because it would require a
        # potential performance tradeoff, either interfering with bulk copy,
        # or involving more verification of changed hash entries.
        val.resetCache()
      else:
        var prevValue: E
        val.resizeHashes()

        for i in 0 ..< val.len:
          let offset = i * elemSize
          assign(prevValue, val.data[i])
          readSszValue(
            input.toOpenArray(offset, offset + elemSize - 1), val.data[i])
          if prevValue != val.data[i]:
            val.clearCaches(i)

        # Unconditionally trigger small, O(1) updates to handle when the list
        # shrinks without otherwise changing.
        val.clearCaches(0)
        val.clearCaches(max(val.len - 1, 0))

    else:
      if input.len == 0:
        # This is an empty list.
        # The default initialization of the return value is fine.
        val.data.setOutputSize 0
        val.resetCache()
        return
      elif input.len < offsetSize:
        raiseMalformedSszError(T, "input of insufficient size")

      var offset = readOffset 0
      let resultLen = offset div offsetSize

      if resultLen == 0:
        # If there are too many elements, other constraints detect problems
        # (not monotonically increasing, past end of input, or last element
        # not matching up with its nextOffset properly)
        raiseMalformedSszError(T, "incorrect encoding of zero length")

      val.data.setOutputSize resultLen
      val.resizeHashes()

      var prevValue: E
      for i in 1 ..< resultLen:
        let nextOffset = readOffset(i * offsetSize)
        if nextOffset < offset:
          raiseMalformedSszError(T, "list element offsets are decreasing")
        else:
          assign(prevValue, val.data[i - 1])
          readSszValue(
            input.toOpenArray(offset, nextOffset - 1), val.data[i - 1])
          if prevValue != val.data[i - 1]:
            val.clearCaches(i - 1)
        offset = nextOffset

      readSszValue(
        input.toOpenArray(offset, input.len - 1), val.data[resultLen - 1])

      # Unconditionally trigger small, O(1) updates to handle when the list
      # shrinks without otherwise changing.
      val.clearCaches(0)
      val.clearCaches(max(val.len - 1, 0))

  elif val is HashArray:
    readSszValue(input, toSszType(val.data))
    val.resetCache()
  elif val is Digest:
    readSszValue(input, val.data)
  elif val is List|array:
    type E = typeof toSszType(declval ElemType(typeof val))

    when isFixedSize(E):
      const elemSize = fixedPortionSize(E)
      when elemSize > 1:
        if input.len mod elemSize != 0:
          var ex = new SszSizeMismatchError
          ex.deserializedType = cstring typetraits.name(T)
          ex.actualSszSize = input.len
          ex.elementSize = elemSize
          raise ex

      val.setOutputSize input.len div elemSize
      when supportsBulkCopy(type val[0]):
        if val.len > 0:
          copyMem addr val[0], unsafeAddr input[0], input.len
      else:
        for i in 0 ..< val.len:
          let offset = i * elemSize
          readSszValue(
            input.toOpenArray(offset, offset + elemSize - 1), toSszType(val[i]))

    else:
      if input.len == 0:
        # This is an empty list.
        # The default initialization of the return value is fine.
        val.setOutputSize 0
        return
      elif input.len < offsetSize:
        raiseMalformedSszError(T, "input of insufficient size")

      var offset = readOffset 0
      let resultLen = offset div offsetSize

      if resultLen == 0:
        # If there are too many elements, other constraints detect problems
        # (not monotonically increasing, past end of input, or last element
        # not matching up with its nextOffset properly)
        raiseMalformedSszError(T, "incorrect encoding of zero length")

      val.setOutputSize resultLen
      for i in 1 ..< resultLen:
        let nextOffset = readOffset(i * offsetSize)
        if nextOffset < offset:
          raiseMalformedSszError(T, "list element offsets are decreasing")
        else:
          readSszValue(
            input.toOpenArray(offset, nextOffset - 1), toSszType(val[i - 1]))
        offset = nextOffset

      readSszValue(
        input.toOpenArray(offset, input.len - 1), toSszType(val[resultLen - 1]))

  elif val is OptionalType:
    type E = ElemType(T)
    if input.len == 0:
      when val is Option:
        val = options.none(E)
      else:
        val = Opt.none(E)
    else:
      var isSome: uint8
      readSszValue(input.toOpenArray(0, 0), isSome)
      if isSome != 1:
        raiseMalformedSszError(
          T, "Unexpected isSome " & $isSome & " (expected: 1)")
      var v: E
      readSszValue(input.toOpenArray(1, input.len - 1), v)
      when val is Option:
        val = options.some(v)
      else:
        val = Opt.some(v)

  elif val is BitArray:
    if sizeof(val) != input.len:
      raiseIncorrectSize(T)
    checkForForbiddenBits(T, input, val.bits)
    copyMem(addr val.bytes[0], unsafeAddr input[0], input.len)

  elif val is object|tuple:
    when T.isStableContainer:
      static: T.ensureIsValidStableContainer()
      const N = T.getCustomPragmaVal(sszStableContainer)

      let inputLen = input.len
      # `fixedPortionSize(T)`: https://github.com/nim-lang/Nim/issues/23564
      const numPrefixBytes = BitArray[N].fixedPortionSize
      if inputLen < numPrefixBytes:
        raiseMalformedSszError(T, "Scope too small for " &
          "`{.sszStableContainer: " & $N & ".}` active fields")
      var activeFields: BitArray[N]
      readSszValue(input.toOpenArray(0, int(numPrefixBytes - 1)), activeFields)
      var offset = numPrefixBytes

      for fieldIndex in T.totalSerializedFields ..< N:
        if activeFields[fieldIndex]:
          raiseMalformedSszError(T, "Unknown field index " & $fieldIndex)

      val.reset()
      var
        fieldIndex = 0
        dynFieldOffsets: seq[int]
      val.enumInstanceSerializedFields(fieldName, field):
        if activeFields[fieldIndex]:
          template FieldType: untyped = typeof(field).T
          when FieldType.isFixedSize:
            const fieldSize = FieldType.fixedPortionSize
            if inputLen - offset < fieldSize:
              raiseMalformedSszError(T, "Scope too small for " &
                "`" & fieldName & "` of type `" & $FieldType & "`")
            field.ok FieldType
              .fromSszBytes input.toOpenArray(offset, offset + fieldSize - 1)
            offset += fieldSize
          else:
            if inputLen - offset < offsetSize:
              raiseMalformedSszError(T, "Scope too small for " &
                "`" & fieldName & "` offset")
            dynFieldOffsets.add readOffsetUnchecked(offset)
            if dynFieldOffsets[^1] > inputLen - fixedSize:
              raiseMalformedSszError(T, "Field offset past end")
            if dynFieldOffsets.len > 1 and
                dynFieldOffsets[^1] < dynFieldOffsets[^2]:
              raiseMalformedSszError(T, "Field offset not larger than previous")
            offset += offsetSize
        inc fieldIndex
      if dynFieldOffsets.len > 0:
        dynFieldOffsets.add inputLen - numPrefixBytes
        fieldIndex = 0
        var i = 0
        val.enumInstanceSerializedFields(_ {.used.}, field):
          template FieldType: untyped = typeof(field).T
          when not FieldType.isFixedSize:
            if activeFields[fieldIndex]:
              if dynFieldOffsets[i] != offset - numPrefixBytes:
                raiseMalformedSszError(T, "Field offset invalid")
              let fieldSize = dynFieldOffsets[i + 1] - dynFieldOffsets[i]
              field.ok FieldType
                .fromSszBytes input.toOpenArray(offset, offset + fieldSize - 1)
              offset += fieldSize
              inc i
          inc fieldIndex
        doAssert i == (dynFieldOffsets.len - 1)
      if offset != inputLen:
        raiseMalformedSszError(T, "Unexpected extra data after object")
    elif T.isProfile:
      const O = (func(): int =
        var o = 0
        default(T).enumerateSubFields(f):
          when typeof(toSszType(f)) is Opt:
            o += 1
        o)()

      let inputLen = uint32 input.len
      # `fixedPortionSize(T)`: https://github.com/nim-lang/Nim/issues/23564
      const minimallyExpectedSize =
        when O > 0:
          uint32 fixedPortionSize(BitArray[O])
        else:
          0'u32
      if inputLen < minimallyExpectedSize:
        raiseMalformedSszError(T, "input of insufficient size")

      let fixedSize = minimallyExpectedSize
      when O > 0:
        var activeFields: BitArray[O]
        readSszValue(input.toOpenArray(0, int(fixedSize - 1)), activeFields)

      val.reset()
      var
        optIndex = 0
        offset = fixedSize
        varSizedFieldOffsets: seq[uint32]
      enumerateSubFields(val, field):
        type F = type toSszType(field)
        let isActive =
          when F is Opt:
            doAssert optIndex < O
            activeFields[optIndex]
          else:
            true
        if isActive:
          const fieldSize =
            when F is Opt:
              type E = type toSszType(declval ElemType(F))
              when isFixedSize(E):
                Opt.some uint32 fixedPortionSize(E)
              else:
                Opt.none uint32
            else:
              when isFixedSize(F):
                Opt.some uint32 fixedPortionSize(F)
              else:
                Opt.none uint32
          if fieldSize.isSome:
            if inputLen - offset < fieldSize.unsafeGet:
              raiseMalformedSszError(T, "input of insufficient size")
            when F is Opt:
              type E = type toSszType(declval ElemType(F))
              field.ok(default(E))
              readSszValue(
                input.toOpenArray(
                  int(offset), int(offset + fieldSize.unsafeGet - 1)),
                field.unsafeGet)
            else:
              readSszValue(
                input.toOpenArray(
                  int(offset), int(offset + fieldSize.unsafeGet - 1)),
                field)
            offset += fieldSize.unsafeGet
          else:
            if inputLen - offset < offsetSize:
              raiseMalformedSszError(T, "input of insufficient size")
            varSizedFieldOffsets.add readOffsetUnchecked(int(offset))
            if varSizedFieldOffsets[^1] > inputLen - fixedSize:
              raiseMalformedSszError(T, "field offset past input end")
            if varSizedFieldOffsets.len > 1 and
                varSizedFieldOffsets[^1] < varSizedFieldOffsets[^2]:
              raiseMalformedSszError(T, "field offset not past previous one")
            offset += offsetSize
        when F is Opt:
          inc optIndex
      doAssert optIndex == O

      if varSizedFieldOffsets.len > 0:
        varSizedFieldOffsets.add inputLen - fixedSize
        optIndex = 0
        var i = 0
        enumerateSubFields(val, field):
          type F = type toSszType(field)
          const isFixedSized =
            when F is Opt:
              type E = type toSszType(declval ElemType(F))
              isFixedSize(E)
            else:
              isFixedSize(F)
          when not isFixedSized:
            let isActive =
              when F is Opt:
                doAssert optIndex < O
                activeFields[optIndex]
              else:
                true
            if isActive:
              doAssert varSizedFieldOffsets.len > i + 1
              if varSizedFieldOffsets[i] != offset - fixedSize:
                raiseMalformedSszError(T, "field offset invalid")
              let fieldSize = varSizedFieldOffsets[i + 1] - (offset - fixedSize)
              when F is Opt:
                type E = type toSszType(declval ElemType(F))
                field.ok(default(E))
                readSszValue(
                  input.toOpenArray(
                    int(offset), int(offset + fieldSize - 1)),
                  field.unsafeGet)
              else:
                readSszValue(
                  input.toOpenArray(
                    int(offset), int(offset + fieldSize - 1)),
                  field)
              offset += fieldSize
              inc i
          when F is Opt:
            inc optIndex
        doAssert i == (varSizedFieldOffsets.len - 1)
        doAssert optIndex == O
      if offset != inputLen:
        raiseMalformedSszError(T, "input has extra data")
    elif isCaseObject(T):
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
          readSszValue(
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
