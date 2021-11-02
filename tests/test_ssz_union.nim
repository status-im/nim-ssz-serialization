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
