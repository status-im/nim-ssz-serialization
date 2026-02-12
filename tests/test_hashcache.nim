# ssz_serialization
# Copyright (c) 2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}
{.used.}

import
  std/[random, sequtils],
  stew/byteutils,
  unittest2,
  ../ssz_serialization,
  ../ssz_serialization/merkleization

type Foo = object
  x: Digest
  y: uint64

let foo = Foo(
  x: Digest(data: array[32, byte].fromHex(
    "0x4175371111cef0d13cb836c17dba708f026f2ddbf057b91384bb78b1ba42343c")),
  y: 42)

proc checkResize[T](items: var T, counts: varargs[int]) =
  for count in counts:
    when T is HashList:
      if count + 4 > int(T.maxLen):
        continue
    for data in [
        SSZ.encode((0 ..< count).mapIt(foo)),
        SSZ.encode((0 ..< count).mapIt(foo) & (0 ..< 4).mapIt(default(Foo)))]:
      try:
        readSszBytes(data, items)
      except SszError:
        raiseAssert "Valid SSZ"
      check items.hash_tree_root() == items.data.hash_tree_root()

template runHashCacheTests[T](_: typedesc[T]): untyped =
  setup:
    randomize(42)
    var items: T

  test "Shrink to smaller cache depth":
    items.checkResize(1074, 1018)

  test "Grow to larger cache depth":
    items.checkResize(1018, 1074)

  test "Grow within same cache depth":
    items.checkResize(500, 600)

  test "Shrink within same cache depth":
    items.checkResize(600, 500)

  test "Grow from empty":
    items.checkResize(0, 100)

  test "Shrink to empty":
    items.checkResize(100, 0)

  test "Multiple resizes in sequence":
    items.checkResize(
      100, 500, 1074, 1018, 200, 2000, 50, 0, 300, 304, 309, 314)

  test "Incremental add":
    for i in 0 ..< 100:
      when items is HashList:
        check items.add(foo)
      else:
        items.add(foo)
      check items.hash_tree_root() == items.data.hash_tree_root()

  test "Incremental add across cache depth boundary":
    items.checkResize(1020)
    for i in 1020 ..< 1080:
      when items is HashList:
        check items.add(foo)
      else:
        items.add(foo)
      check items.hash_tree_root() == items.data.hash_tree_root()

  test "Incremental decrease":
    for i in countdown(1050, 0):
      items.checkResize(i)

  test "Progressive depth boundaries":
    items.checkResize(21844, 340, 20, 84, 1, 340)

  test "Random resize sequence":
    for _ in 0 ..< 50:
      let count =
        when items is HashList:
          rand(int(items.maxLen) - 4)
        else:
          rand(4000)
      items.checkResize(count)

  test "Random add/resize mix":
    for _ in 0 ..< 100:
      let canAdd =
        when items is HashList:
          items.data.len < int(items.maxLen)
        else:
          true
      if canAdd and rand(1) == 0:
        when items is HashList:
          check items.add(foo)
        else:
          items.add(foo)
        check items.hash_tree_root() == items.data.hash_tree_root()
      else:
        let count =
          when items is HashList:
            rand(int(items.maxLen) - 4)
          else:
            rand(4000)
        items.checkResize(count)

suite "HashList":
  runHashCacheTests(HashList[Foo, 8192])

suite "HashSeq":
  runHashCacheTests(HashSeq[Foo])

suite "Cache layout equivalence (for HashSeq)":
  template checkEquivalence(maxLen: static Limit) =
    test $maxLen:
      var
        ha: HashArray[maxLen, Foo]
        hl: HashList[Foo, maxLen]
      for i in 0 ..< int(maxLen):
        ha.data[i] = foo
        check hl.add(foo)
      discard ha.hash_tree_root()
      discard hl.hash_tree_root()
      check hl.hashes.len == ha.hashes.len
      for i in 1 ..< hl.hashes.len:
        check hl.hashes[i] == ha.hashes[i]

  checkEquivalence(1)
  checkEquivalence(4)
  checkEquivalence(16)
  checkEquivalence(64)
  checkEquivalence(256)
