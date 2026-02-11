# ssz_serialization
# Copyright (c) 2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}
{.used.}

import
  std/sequtils,
  stew/byteutils,
  unittest2,
  ../ssz_serialization,
  ../ssz_serialization/[merkleization, types]

type Foo = object
  x: Digest

let foo = Foo(x: Digest(data: array[32, byte].fromHex(
  "0x4175371111cef0d13cb836c17dba708f026f2ddbf057b91384bb78b1ba42343c")))

proc checkResize(items: var HashList[Foo, 8192], counts: varargs[int]) =
  for count in counts:
    try:
      readSszBytes(SSZ.encode((0 ..< count).mapIt(foo)), items)
    except SszError:
      raiseAssert "Valid SSZ"
    check items.hash_tree_root() == items.data.hash_tree_root()

suite "HashList":
  setup:
    var items: HashList[Foo, 8192]

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
    items.checkResize(100, 500, 1074, 1018, 200, 2000, 50, 0, 300)

  test "Incremental add":
    for i in 0 ..< 100:
      check:
        items.add(foo)
        items.hash_tree_root() == items.data.hash_tree_root()

  test "Incremental add across cache depth boundary":
    items.checkResize(1020)
    for i in 1020 ..< 1080:
      check:
        items.add(foo)
        items.hash_tree_root() == items.data.hash_tree_root()

  test "Incremental decrease":
    for i in countdown(1050, 0):
      items.checkResize(i)
