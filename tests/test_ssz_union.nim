# ssz_serialization
# Copyright (c) 2021 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  unittest2,
  stew/byteutils,
  ../ssz_serialization

type
  TestCaseObjectType* = enum
    None = 0x00
    SomeFixed = 0x01
    SomeFixedObject = 0x02
    SomeVariable = 0x03
    SomeVariableObject = 0x04

  TestFixedObject* = object
    networkId: uint32
    bytes: array[2, byte]
    andThis: uint32

  TestVariableObject* = object
    networkId: uint32
    bytes: List[byte, 16]
    andThis: uint32

  Test2VariableObject* = object
    varObject: TestVariableObject
    andThat: uint32

  TestCaseObject* = object
    case selector*: TestCaseObjectType
    of None:
      discard
    of SomeFixed:
      fixedPart*: uint16
    of SomeFixedObject:
      fixedObj*: TestFixedObject
    of SomeVariable:
      variablePart*: List[byte, 16]
    of SomeVariableObject:
      variableObj*: TestVariableObject

suite "SSZ Union serialization":
  test "Union serialize different object branches":
    block: # None
      let test = TestCaseObject(selector: None)
      let encoded = SSZ.encode(test)

      check encoded.toHex() == "00"

      let decoded = SSZ.decode(encoded, TestCaseObject)

      check:
        test.selector == decoded.selector

    block:
      let test = TestCaseObject(selector: SomeFixed, fixedPart: 2'u16)
      let encoded = SSZ.encode(test)

      check encoded.toHex() == "010200"

      let decoded = SSZ.decode(encoded, TestCaseObject)

      check:
        test.selector == decoded.selector
        test.fixedPart == decoded.fixedPart

    block:
      let obj = TestFixedObject(networkId: 1, bytes: [byte 1, 2], andThis: 234)
      let test = TestCaseObject(selector: SomeFixedObject, fixedObj: obj)
      let encoded = SSZ.encode(test)

      check encoded.toHex() == "02010000000102ea000000"

      let decoded = SSZ.decode(encoded, TestCaseObject)

      check:
        test.selector == decoded.selector
        test.fixedObj == decoded.fixedObj

    block:
      let test = TestCaseObject(selector: SomeVariable,
        variablePart: List[byte, 16](@[byte 1, 2, 3, 4]))
      let encoded = SSZ.encode(test)

      check encoded.toHex() == "0301020304"

      let decoded = SSZ.decode(encoded, TestCaseObject)

      check:
        test.selector == decoded.selector
        test.variablePart == decoded.variablePart

    block:
      let obj = TestVariableObject(networkId: 1,
        bytes: List[byte, 16](@[byte 1, 2, 3, 4]), andThis: 234)
      let test = TestCaseObject(selector: SomeVariableObject, variableObj: obj)
      let encoded = SSZ.encode(test)

      check encoded.toHex() == "04010000000c000000ea00000001020304"

      let decoded = SSZ.decode(encoded, TestCaseObject)

      check:
        test.selector == decoded.selector
        test.variableObj == decoded.variableObj

  test "Union with empty list":
    let test = TestCaseObject(selector: SomeVariable,
      variablePart: List[byte, 16](@[]))
    let encoded = SSZ.encode(test)

    check encoded.toHex() == "03"

    let decoded = SSZ.decode(encoded, TestCaseObject)

    check:
      test.selector == decoded.selector
      test.variablePart == decoded.variablePart

suite "SSZ Union invalid inputs":
  test "No data":
    var encoded: seq[byte]
    expect MalformedSszError:
      discard SSZ.decode(encoded, TestCaseObject)

  test "Selector byte only, expecting value":
    let encoded = [byte 1]
    expect MalformedSszError:
      discard SSZ.decode(encoded, TestCaseObject)

  test "Invalid value, 1 byte too few":
    let encoded = [byte 1, 2]
    expect MalformedSszError:
      discard SSZ.decode(encoded, TestCaseObject)

  test "Invalid value, 1 byte too many":
    let encoded = [byte 1, 2, 3, 4]
    expect MalformedSszError:
      discard SSZ.decode(encoded, TestCaseObject)

  test "Selector byte out of range":
    let encoded = [byte 5, 2, 3]
    expect MalformedSszError:
      discard SSZ.decode(encoded, TestCaseObject)

type
  UKind {.pure.} = enum
    None
    Some

  TUnion[T] = object
    case kind*: UKind
    of UKind.None:
      discard
    of UKind.Some:
      val: T

  XYKind {.pure.} = enum
    None
    SomeX
    SomeY

  XYUnion[X, Y] = object
    case kind*: XYKind
    of XYKind.None:
      discard
    of XYKind.SomeX:
      x: X
    of XYKind.SomeY:
      y: Y

  Bytes32 = array[2, byte]
  List32 = List[byte, 32]

suite "Generic union test suite":
  test "T Union":
    let a = TUnion[Bytes32](kind: UKind.None)
    let b = TUnion[Bytes32](kind: UKind.Some, val: default(Bytes32))

    let abytes = SSZ.encode(a)
    let bbytes = SSZ.encode(b)

    let aa = SSZ.decode(abytes, typeof a)
    let bb = SSZ.decode(bbytes, typeof b)

    check aa.kind == UKind.None
    check bb.kind == UKind.Some

    let aabytes = SSZ.encode(aa)
    let bbbytes = SSZ.encode(bb)

    check aabytes == abytes
    check bbbytes == bbytes

  test "XY Union":
    let a = XYUnion[Bytes32, List32](kind: XYKind.None)
    let b = XYUnion[Bytes32, List32](kind: XYKind.SomeX, x: default(Bytes32))
    let c = XYUnion[Bytes32, List32](kind: XYKind.SomeY, y: List32(@[3.byte]))

    let aBytes = SSZ.encode(a)
    let bBytes = SSZ.encode(b)
    let cBytes = SSZ.encode(c)

    let aa = SSZ.decode(aBytes, typeof a)
    let bb = SSZ.decode(bBytes, typeof b)
    let cc = SSZ.decode(cBytes, typeof c)

    check aa.kind == XYKind.None
    check bb.kind == XYKind.SomeX
    check cc.kind == XYKind.SomeY

    let aaBytes = SSZ.encode(aa)
    let bbBytes = SSZ.encode(bb)
    let ccBytes = SSZ.encode(cc)

    check aaBytes == aBytes
    check bbBytes == bBytes
    check ccBytes == cBytes

suite "sszSize test suite":
  test "TestCaseObject None":
    let x = TestCaseObject(selector: None)
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TestCaseObject SomeFixed":
    let x = TestCaseObject(selector: SomeFixed, fixedPart: 12345'u16)
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TestCaseObject SomeFixedObject":
    let x = TestCaseObject(selector: SomeFixedObject, fixedObj:
      TestFixedObject(networkId: 123'u32, bytes: [5.byte, 6.byte], andThis: 456'u32)
    )
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TestCaseObject SomeVariable":
    let x = TestCaseObject(selector: SomeVariable,
      variablePart: List[byte, 16](@[4.byte])
    )
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TestCaseObject SomeVariableObject":
    let x = TestCaseObject(selector: SomeVariableObject, variableObj:
      TestVariableObject(
        networkId: 123'u32,
        bytes: List[byte, 16](@[5.byte, 6.byte]),
        andThis: 456'u32
      )
    )
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TUnion Bytes32 None":
    let x = TUnion[Bytes32](kind: UKind.None)
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TUnion List32 None":
    let x = TUnion[List32](kind: UKind.None)
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TUnion Bytes32 Some":
    let x = TUnion[Bytes32](kind: UKind.Some, val: [1.byte, 3.byte])
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "TUnion List32 Some":
    let x = TUnion[List32](kind: UKind.Some, val: List32(@[1.byte, 3.byte]))
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "XYUnion List32, Bytes32, None":
    let x = XYUnion[List32, Bytes32](kind: XYKind.None)
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "XYUnion List32, Bytes32, SomeX":
    let x = XYUnion[List32, Bytes32](kind: XYKind.SomeX,
      x: List32(@[1.byte, 5.byte])
    )
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "XYUnion List32, Bytes32, SomeY":
    let x = XYUnion[List32, Bytes32](kind: XYKind.SomeY,
      y: [1.byte, 5.byte]
    )
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "XYUnion Bytes32, List32, None":
    let x = XYUnion[Bytes32, List32](kind: XYKind.None)
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "XYUnion Bytes32, List32, SomeX":
    let x = XYUnion[Bytes32, List32](kind: XYKind.SomeX,
      x: [1.byte, 5.byte]
    )
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size

  test "XYUnion Bytes32, List32, SomeY":
    let x = XYUnion[Bytes32, List32](kind: XYKind.SomeY,
      y: List32(@[1.byte, 5.byte])
    )
    let size = sszSize(x)
    let bytes = SSZ.encode(x)
    check bytes.len == size
