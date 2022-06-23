# ssz_serialization
# Copyright (c) 2021 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/[sequtils, tables],
  unittest2,
  stew/[endians2, results],
  ../ssz_serialization/merkleization

func d(x: openArray[byte]): Digest =
  result.data[0 ..< x.len] = x

func d(x: openArray[UintN]): Digest =
  for i, v in x:
    result.data[i * sizeof(v) ..< (i + 1) * sizeof(v)] = toBytesLE(v)

func d(x: UintN): Digest =
  d([x])

func d(a, b: Digest): Digest =
  computeDigest:
    h.update a.data
    h.update b.data

type
  E = object
    x: bool
    y: bool
  X = object
    a: bool
    b: uint8
    c: uint16
    d: uint32
    e: uint64
    f: Uint128
    g: Uint256
    h: BitArray[40]
    i: BitArray[333]
    j: BitList[40]
    k: BitList[333]
    l: BitList[333]
    m: BitList[333]
    n: BitList[333]
    o: array[2, bool]
    p: array[6, uint64]
    q: array[2, E]
    r: List[E, 2]
    s: List[E, 2]
    t: SingleMemberUnion[E]
    u: E
    v: tuple[a, b: bool]
    w: tuple[a, b: E, c: bool]
    x: HashArray[2, E]
    y: HashList[E, 2]
    z: HashList[E, 2]
let
  x = X(
    a: true,
    b: 0x08'u8,
    c: 0x1616'u16,
    d: 0x32323232'u32,
    e: 0x6464646464646464'u64,
    f: 0x01281281281281281281281281281280.u128,
    g: 0x02562562562562562562562562562562562562562560.u256,
    h: BitArray[40](bytes: [
      0b01010101'u8, 0b10101010'u8, 0b11111111'u8,
      0b10101010'u8, 0b01010101'u8]),
    i: BitArray[333](bytes: [
      0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
      32, 33, 34, 35, 36, 37, 38, 39, 40, 0b11111]),
    j: BitList[40](@[
      0b01010101'u8, 0b10101010'u8, 0b11111111'u8,
      0b10101010'u8, 0b01010101'u8, 0b1'u8]),
    k: BitList[333](@[
      0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
      32, 33, 34, 35, 36, 37, 38, 39, 40, 0b111111]),
    l: BitList[333](@[
      0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0xFF]),
    m: BitList[333](@[
      0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
      0x01]),
    n: BitList[333](@[0x01'u8]),
    o: [false, true],
    p: [1'u64, 2, 3, 4, 5, 6],
    q: [E(x: false, y: true), E(x: true, y: false)],
    r: List[E, 2](@[E(x: false, y: true), E(x: true, y: false)]),
    s: List[E, 2](@[]),
    t: SingleMemberUnion[E](selector: 0, value: E(x: false, y: true)),
    u: E(x: false, y: true),
    v: (a: false, b: true),
    w: (a: E(x: false, y: true), b: E(x: true, y: false), c: true),
    x: HashArray[2, E](data: array[2, E](
      [E(x: false, y: true), E(x: true, y: false)])),
    y: HashList[E, 2].init(
      @[E(x: false, y: true), E(x: true, y: false)]),
    z: HashList[E, 2].init(@[]))
  roots = block:
    var res = {
      # a
      32: d(1'u8),

      # b
      33: d(0x08'u8),

      # c
      34: d(0x1616'u16),

      # d
      35: d(0x32323232'u32),

      # e
      36: d(0x6464646464646464'u64),

      # f
      37: d(0x01281281281281281281281281281280.u128),

      # g
      38: d(0x02562562562562562562562562562562562562562560.u256),

      # h
      39: d(0b01010101_10101010_11111111_10101010_01010101'u64),

      # i
      80: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
      81: d([32'u8, 33, 34, 35, 36, 37, 38, 39, 40, 0b11111]),

      # j
      82: d(0b01010101_10101010_11111111_10101010_01010101'u64),
      83: d(40'u64),

      # k
      168: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
      169: d([32'u8, 33, 34, 35, 36, 37, 38, 39, 40, 0b11111]),
      85: d(333'u64),

      # l
      172: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0x7F]),
      173: d(0.u256),
      87: d(255'u64),

      # m
      176: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
      177: d(0.u256),
      89: d(256'u64),

      # n
      180: d(0.u256),
      181: d(0.u256),
      91: d(0'u64),

      # o
      46: d([0'u8, 1]),

      # p
      94: d([1'u64, 2, 3, 4]),
      95: d([5'u64, 6]),

      # q
      192: d(0'u8),
      193: d(1'u8),
      194: d(1'u8),
      195: d(0'u8),

      # r
      392: d(0'u8),
      393: d(1'u8),
      394: d(1'u8),
      395: d(0'u8),
      99: d(2'u64),

      # s
      200: d(0.u256),
      201: d(0.u256),
      101: d(0'u64),

      # t
      204: d(0'u8),
      205: d(1'u8),
      103: d(0'u8),

      # u
      104: d(0'u8),
      105: d(1'u8),

      # v
      106: d(0'u8),
      107: d(1'u8),

      # w
      432: d(0'u8),
      433: d(1'u8),
      434: d(1'u8),
      435: d(0'u8),
      218: d(1'u8),
      219: d(0.u256),

      # x
      220: d(0'u8),
      221: d(1'u8),
      222: d(1'u8),
      223: d(0'u8),

      # y
      448: d(0'u8),
      449: d(1'u8),
      450: d(1'u8),
      451: d(0'u8),
      113: d(2'u64),

      # z
      228: d(0.u256),
      229: d(0.u256),
      115: d(0'u64)
    }.toOrderedTable
    for i in 58 ..< 64:
      res[i] = d(0.u256)
    for i in [
        40, 41, 84, 42, 86, 43, 88, 44, 90, 45, 47, 96, 97, 48,
        196, 197, 98, 49, 100, 50, 102, 51, 52, 53, 216, 217, 108, 109, 54,
        110, 111, 55, 224, 225, 112, 56, 114, 57]:
      res[i] = d(res.getOrDefault(2 * i + 0), res.getOrDefault(2 * i + 1))
    for i in countdown(31, 1):
      res[i] = d(res.getOrDefault(2 * i + 0), res.getOrDefault(2 * i + 1))
    res

suite "Merkleization types":
  test "All generalized indices with content":
    for i, r in roots:
      checkpoint $i
      var root {.noinit.}: array[1, Digest]
      hash_tree_root(x, [i.GeneralizedIndex], root).get
      check:
        root == [r]
        hash_tree_root(x, [i.GeneralizedIndex]).get == [r]
        hash_tree_root(x, i.GeneralizedIndex).get == r

  test "All members of root object":
    var i = 32
    enumInstanceSerializedFields(x, _ {.used.}, field):
      checkpoint $i
      let r = roots.getOrDefault(i)
      var root {.noinit.}: array[1, Digest]
      hash_tree_root(x, [i.GeneralizedIndex], root).get
      check:
        root == [r]
        hash_tree_root(x, [i.GeneralizedIndex]).get == [r]
        hash_tree_root(x, i.GeneralizedIndex).get == r
        hash_tree_root(field) == r
      inc i

  test "Generalized index 1 (static)":
    const i = 1
    let r = roots.getOrDefault(i)
    var root {.noinit.}: array[1, Digest]
    hash_tree_root(x, [i.GeneralizedIndex], root).get
    check:
      root == [r]
      hash_tree_root(x, [i.GeneralizedIndex]).get == [r]
      hash_tree_root(x, i.GeneralizedIndex).get == r
      hash_tree_root(x) == r

  test "Generalized index 2 (static)":
    const i = 2
    let r = roots.getOrDefault(i)
    var root {.noinit.}: array[1, Digest]
    hash_tree_root(x, [i.GeneralizedIndex], root).get
    check:
      root == [r]
      hash_tree_root(x, [i.GeneralizedIndex]).get == [r]
      hash_tree_root(x, i.GeneralizedIndex).get == r

  test "Unknown generalized indices (errors)":
    for i in 0 ..< 1024:
      if roots.hasKey(i): continue
      checkpoint $i
      var root {.noinit.}: array[1, Digest]
      check:
        hash_tree_root(x, [i.GeneralizedIndex], root).isErr
        hash_tree_root(x, [i.GeneralizedIndex]).isErr
        hash_tree_root(x, i.GeneralizedIndex).isErr

  test "Generalized index 999 (error - static)":
    const i = 999
    var root {.noinit.}: array[1, Digest]
    check:
      hash_tree_root(x, [i.GeneralizedIndex], root).isErr
      hash_tree_root(x, [i.GeneralizedIndex]).isErr
      hash_tree_root(x, i.GeneralizedIndex).isErr

  test "Generalized index 0 (error)":
    let i = 0
    var root {.noinit.}: array[1, Digest]
    check:
      hash_tree_root(x, [i.GeneralizedIndex], root).isErr
      hash_tree_root(x, [i.GeneralizedIndex]).isErr
      hash_tree_root(x, i.GeneralizedIndex).isErr

  test "Generalized index 0 (error - static)":
    const i = 0
    var root {.noinit.}: array[1, Digest]
    check:
      hash_tree_root(x, [i.GeneralizedIndex], root).isErr
      hash_tree_root(x, [i.GeneralizedIndex]).isErr
      hash_tree_root(x, i.GeneralizedIndex).isErr

  test "Generalized index max (error)":
    let i = GeneralizedIndex.high
    var root {.noinit.}: array[1, Digest]
    check:
      hash_tree_root(x, [i], root).isErr
      hash_tree_root(x, [i]).isErr
      hash_tree_root(x, i).isErr

  test "Generalized index max (error - static)":
    const i = GeneralizedIndex.high
    var root {.noinit.}: array[1, Digest]
    check:
      hash_tree_root(x, [i], root).isErr
      hash_tree_root(x, [i]).isErr
      hash_tree_root(x, i).isErr

  test "Multiproof":
    let
      i = [32.GeneralizedIndex, 85, 80, 46, 103, 395, 219, 218, 435, 100]
      r = i.mapIt(roots.getOrDefault(it.int))
    var roots {.noinit.}: array[i.len, Digest]
    hash_tree_root(x, i, roots).get
    check:
      roots == r
      hash_tree_root(x, i).get == roots

  test "Multiproof (static)":
    const i = [32.GeneralizedIndex, 85, 80, 46, 103, 395, 219, 218, 435, 100]
    let r = i.mapIt(roots.getOrDefault(it.int))
    var roots {.noinit.}: array[i.len, Digest]
    hash_tree_root(x, i, roots).get
    check:
      roots == r
      hash_tree_root(x, i).get == roots

  test "Multiproof (empty)":
    let
      i: array[0, GeneralizedIndex] = []
      r: array[0, Digest] = []
    var roots {.noinit.}: array[i.len, Digest]
    hash_tree_root(x, i, roots).get
    check:
      roots == r
      hash_tree_root(x, i).get == roots

  test "Multiproof (empty - static)":
    const i: array[0, GeneralizedIndex] = []
    let r: array[0, Digest] = []
    var roots {.noinit.}: array[i.len, Digest]
    hash_tree_root(x, i, roots).get
    check:
      roots == r
      hash_tree_root(x, i).get == roots

  test "Multiproof (error)":
    let i = [32.GeneralizedIndex, 85, 80, 46, 103, 395, 219, 218, 435, 999]
    var roots {.noinit.}: array[i.len, Digest]
    check:
      hash_tree_root(x, i, roots).isErr
      hash_tree_root(x, i).isErr

  test "Multiproof (error - static)":
    const i = [32.GeneralizedIndex, 85, 80, 46, 103, 395, 219, 218, 435, 999]
    var roots {.noinit.}: array[i.len, Digest]
    check:
      hash_tree_root(x, i, roots).isErr
      hash_tree_root(x, i).isErr

  test "Multiproof (invalid indices)":
    let i = [1.GeneralizedIndex, 2, 3]
    var roots {.noinit.}: array[i.len, Digest]
    check:
      hash_tree_root(x, i, roots).isErr
      hash_tree_root(x, i).isErr

  test "Multiproof (invalid indices - static)":
    const i = [1.GeneralizedIndex, 2, 3]
    var roots {.noinit.}: array[i.len, Digest]
    check:
      hash_tree_root(x, i, roots).isErr
      hash_tree_root(x, i).isErr
