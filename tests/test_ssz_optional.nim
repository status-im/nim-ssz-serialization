# ssz_serialization
# Copyright (c) 2023 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/options,
  serialization/object_serialization,
  unittest2,
  ../ssz_serialization/merkleization,
  ../ssz_serialization

proc doTest[T](name: string, value: Option[T] | Opt[T]) =
  test name:
    const isUnsupported =
      when T is OptionalType:
        false
      elif T is object:
        when T.isCaseObject():
          true
        else:
          false
      else:
        false
    when isUnsupported:
      skip()
    else:
      if value.isNone:
        check:
          SSZ.encode(value) == []
          sszSize(value) == 0
          value.hash_tree_root() == List[T, 1](@[]).hash_tree_root()
          value.hash_tree_root(1.GeneralizedIndex).get == zeroHashes[1]
          value.hash_tree_root(2.GeneralizedIndex).get == zeroHashes[0]
          value.hash_tree_root(3.GeneralizedIndex).get == zeroHashes[0]
      else:
        let
          v = value.unsafeGet
          encoded = SSZ.encode(value)
        check:
          encoded.len >= 1
          encoded[0] == 0x01
          encoded[1 ..< encoded.len] == SSZ.encode(v)
          sszSize(value) == encoded.len
          value.hash_tree_root() == List[T, 1](@[v]).hash_tree_root()
          value.hash_tree_root(1.GeneralizedIndex).get == value.hash_tree_root()
          value.hash_tree_root(2.GeneralizedIndex).get == v.hash_tree_root()
          value.hash_tree_root(3.GeneralizedIndex).get == hash_tree_root(1'u64)
      check SSZ.decode(SSZ.encode(value), typeof(value)) == value

proc testCase[T](name: string, value: Opt[T]) =
  doTest(name & " - Opt", value)

  if value.isNone:
    doTest(name & " - Option", options.none(T))
  else:
    doTest(name & " - Option", options.some(value.get))

# https://eips.ethereum.org/assets/eip-6475/tests.py
suite "SSZ Optional":
  testCase "uint8 - None",
    Opt.none(uint8)
  testCase "uint8 - Some",
    Opt.some(uint8(8))

  testCase "uint16 - None",
    Opt.none(uint16)
  testCase "uint16 - Some",
    Opt.some(uint16(16))

  testCase "uint32 - None",
    Opt.none(uint32)
  testCase "uint32 - Some",
    Opt.some(uint32(32))

  testCase "uint64 - None",
    Opt.none(uint64)
  testCase "uint64 - Some",
    Opt.some(uint64(64))

  testCase "uint128 - None",
    Opt.none(UInt128)
  testCase "uint128 - Some",
    Opt.some(u128(128))

  testCase "uint256 - None",
    Opt.none(UInt256)
  testCase "uint256 - Some",
    Opt.some(u256(256))

  testCase "boolean - None",
    Opt.none(bool)
  testCase "boolean - Some",
    Opt.some(bool(true))

  testCase "Optional - None (1)",
    Opt.none(Opt[uint64])
  testCase "Optional - None (2)",
    Opt.none(Option[uint64])
  testCase "Optional - Some(None) (1)",
    Opt.some(Opt.none(uint64))
  testCase "Optional - Some(None) (2)",
    Opt.some(options.none(uint64))
  testCase "Optional - Some(Some) (1)",
    Opt.some(Opt.some(uint64(64)))
  testCase "Optional - Some(Some) (2)",
    Opt.some(options.some(uint64(64)))

  type Foo = object
    a: uint64
    b: Opt[uint32]
    c: Option[uint16]

  testCase "Container - None",
    Opt.none(Foo)
  testCase "Container - Some (1)",
    Opt.some(Foo(a: 64))
  testCase "Container - Some (2)",
    Opt.some(Foo(a: 64, b: Opt.some(uint32(32))))
  testCase "Container - Some (3)",
    Opt.some(Foo(a: 64, b: Opt.some(uint32(32)), c: options.some(uint16(16))))

  testCase "Vector - None (1)",
    Opt.none(array[1, uint64])
  testCase "Vector - Some (1)",
    Opt.some([uint64(64)])
  testCase "Vector - None (2)",
    Opt.none(array[5, uint64])
  testCase "Vector - Some (2)",
    Opt.some([uint64(64), 64, 64, 64, 64])

  testCase "List - None (1)",
    Opt.none(List[uint64, 1])
  testCase "List - Some (1)",
    Opt.some(List[uint64, 1](@[]))
  testCase "List - Some (2)",
    Opt.some(List[uint64, 1](@[uint64(64)]))
  testCase "List - Some (3)",
    Opt.some(List[uint64, 5](@[uint64(64), 64]))
  testCase "List - None (2)",
    Opt.none(List[Opt[uint64], 9])
  testCase "List - None (3)",
    Opt.none(List[Option[uint64], 9])
  testCase "List - Some (4)",
    Opt.some(List[Opt[uint64], 9](@[
      Opt.none(uint64), Opt.some(uint64(64))]))
  testCase "List - Some (5)",
    Opt.some(List[Option[uint64], 9](@[
      options.none(uint64), options.some(uint64(64))]))
  testCase "List - Some (6)",
    Opt.some(List[Foo, 1](@[Foo(a: 64, b: Opt.some(uint32(32)))]))
  testCase "List - Some (7)",
    Opt.some(List[Opt[Foo], 1](@[Opt[Foo].some(
      Foo(a: 64, b: Opt.some(uint32(32)), c: options.some(uint16(16))))]))
  testCase "List - Some (8)",
    Opt.some(List[Option[Foo], 1](@[options.some(
      Foo(a: 64, b: Opt.some(uint32(32)), c: options.some(uint16(16))))]))

  testCase "Bitvector - None (1)",
    Opt.none(BitArray[1])
  testCase "Bitvector - Some (1)",
    Opt.some(BitArray[1](bytes: [byte(0x01)]))
  testCase "Bitvector - None (2)",
    Opt.none(BitArray[9])
  testCase "Bitvector - Some (2)",
    Opt.some(BitArray[9](bytes: [byte(0xef), 0x01]))

  testCase "Bitlist - None (1)",
    Opt.none(BitList[0])
  testCase "Bitlist - Some (1)",
    Opt.some(BitList[0](@[byte(0x01)]))
  testCase "Bitlist - None (2)",
    Opt.none(BitList[1])
  testCase "Bitlist - Some (2)",
    Opt.some(BitList[1](@[byte(0x03)]))
  testCase "Bitlist - None (3)",
    Opt.none(BitList[9])
  testCase "Bitlist - Some (3)",
    Opt.some(BitList[9](@[byte(0x03)]))

  type
    Kind {.pure.} = enum
      None
      SomeX
      SomeY

    Bar = object
      case kind: Kind
      of Kind.None:
        discard
      of Kind.SomeX:
        x: uint64
      of Kind.SomeY:
        y: uint32

  testCase "Union - None",
    Opt.none(Bar)
  testCase "Union - Some (1)",
    Opt.some(Bar(kind: Kind.None))
  testCase "Union - Some (2)",
    Opt.some(Bar(kind: Kind.SomeX, x: uint64(64)))
  testCase "Union - Some (3)",
    Opt.some(Bar(kind: Kind.SomeY, y: uint32(32)))
