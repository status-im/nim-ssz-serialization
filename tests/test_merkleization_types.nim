# ssz_serialization
# Copyright (c) 2021-2023 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/[random, tables],
  results,
  unittest2,
  stew/endians2,
  ../ssz_serialization/merkleization

from std/sequtils import mapIt

func d(x: openArray[byte]): Digest =
  result.data[0 ..< x.len] = x

func d(x: openArray[UintN]): Digest =
  for i, v in x:
    result.data[i * sizeof(v) ..< (i + 1) * sizeof(v)] = toBytesLE(v)

func d(x: UintN): Digest =
  d([x])

func d(a, b: Digest): Digest =
  digest(a.data, b.data)

type
  SingleFieldTestStruct = object
    a: byte
  SmallTestStruct = object
    a: uint16
    b: uint16
  VarTestStruct = object
    a: uint16
    b: List[uint16, 1024]
    c: uint8
  ProgressiveSingleFieldContainerTestStruct
      {.sszActiveFields: [1].} = object
    a: uint8
  ProgressiveSingleListContainerTestStruct
      {.sszActiveFields: [0, 0, 0, 0, 1].} = object
    c: BitSeq
  ProgressiveVarTestStruct
      {.sszActiveFields: [1, 0, 1, 0, 1].} = object
    a: uint8
    b: List[uint16, 123]
    c: BitSeq
  ProgressiveComplexTestStruct
      {.sszActiveFields: [
        1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1
      ].} = object
    a: uint8
    b: List[uint16, 123]
    c: BitSeq
    d: seq[uint64]
    e: seq[SmallTestStruct]
    f: seq[seq[VarTestStruct]]
    g: List[ProgressiveSingleFieldContainerTestStruct, 10]
    h: seq[ProgressiveVarTestStruct]
  E = object
    x: bool
    y: bool
  X = object
    a: bool
    b: uint8
    c: uint16
    d: uint32
    e: uint64
    f: UInt128
    g: UInt256
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
    t: List[E, 2]
    u: E
    v: tuple[a, b: bool]
    w: tuple[a, b: E, c: bool]
    x: HashArray[2, E]
    y: HashList[E, 2]
    z: HashList[E, 2]
    aa: HashArray[2, uint64]
    ab: HashList[uint64, 2]
    ac: HashList[uint64, 2]
    ad: HashArray[1, E]
    ae: HashList[E, 1]
    af: HashList[E, 1]
    ag: seq[uint16]
    ah: seq[uint16]
    ai: seq[uint16]
    aj: seq[uint16]
    ak: seq[uint16]
    al: seq[SingleFieldTestStruct]
    am: seq[SingleFieldTestStruct]
    an: seq[SingleFieldTestStruct]
    ao: seq[SingleFieldTestStruct]
    ap: BitSeq
    aq: BitSeq
    ar: BitSeq
    `as`: BitSeq
    at: BitSeq
    au: BitSeq
    av: BitArray[256]
    aw: BitList[256]
    ax: BitSeq
    ay: BitArray[257]
    az: BitList[257]
    ba: BitSeq
    bb: BitSeq
    bc: BitSeq
    bd: BitSeq
    be: ProgressiveSingleFieldContainerTestStruct
    bf: ProgressiveSingleListContainerTestStruct
    bg: ProgressiveVarTestStruct
    bh: ProgressiveVarTestStruct
    bi: ProgressiveVarTestStruct
    bj: ProgressiveComplexTestStruct
let
  x = X(
    a: true,
    b: 0x08'u8,
    c: 0x1616'u16,
    d: 0x32323232'u32,
    e: 0x6464646464646464'u64,
    f: 0x01281281281281281281281281281280'u128,
    g: 0x02562562562562562562562562562562562562562560'u256,
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
    t: List[E, 2](@[]),
    u: E(x: false, y: true),
    v: (a: false, b: true),
    w: (a: E(x: false, y: true), b: E(x: true, y: false), c: true),
    x: HashArray[2, E](data: [E(x: false, y: true), E(x: true, y: false)]),
    y: HashList[E, 2].init(
      @[E(x: false, y: true), E(x: true, y: false)]),
    z: HashList[E, 2].init(@[]),
    aa: HashArray[2, uint64](data: [1'u64, 2]),
    ab: HashList[uint64, 2].init(@[1'u64, 2]),
    ac: HashList[uint64, 2].init(@[]),
    ad: HashArray[1, E](data: [E(x: true, y: false)]),
    ae: HashList[E, 1].init(@[E(x: true, y: false)]),
    af: HashList[E, 1].init(@[]),
    ag: @[],
    ah: @[0x0100, 0x0101],
    ai: @[
      0x0100, 0x0101, 0x0102, 0x0103, 0x0104, 0x0105, 0x0106, 0x0107,
      0x0108, 0x0109, 0x010a, 0x010b, 0x010c, 0x010d, 0x010e, 0x010f,
      0x0200],
    aj: @[
      0x0100, 0x0101, 0x0102, 0x0103, 0x0104, 0x0105, 0x0106, 0x0107,
      0x0108, 0x0109, 0x010a, 0x010b, 0x010c, 0x010d, 0x010e, 0x010f,
      0x0200, 0x0201, 0x0202, 0x0203, 0x0204, 0x0205, 0x0206, 0x0207,
      0x0208, 0x0209, 0x020a, 0x020b, 0x020c, 0x020d, 0x020e, 0x020f,
      0x0210, 0x0211, 0x0212, 0x0213, 0x0214, 0x0215, 0x0216, 0x0217,
      0x0218, 0x0219, 0x021a, 0x021b, 0x021c, 0x021d, 0x021e, 0x021f,
      0x0220, 0x0221, 0x0222, 0x0223, 0x0224, 0x0225, 0x0226, 0x0227,
      0x0228, 0x0229, 0x022a, 0x022b, 0x022c, 0x022d, 0x022e, 0x022f,
      0x0230, 0x0231, 0x0232, 0x0233, 0x0234, 0x0235, 0x0236, 0x0237,
      0x0238, 0x0239, 0x023a, 0x023b, 0x023c, 0x023d, 0x023e, 0x023f],
    ak: @[
      0x0100, 0x0101, 0x0102, 0x0103, 0x0104, 0x0105, 0x0106, 0x0107,
      0x0108, 0x0109, 0x010a, 0x010b, 0x010c, 0x010d, 0x010e, 0x010f,
      0x0200, 0x0201, 0x0202, 0x0203, 0x0204, 0x0205, 0x0206, 0x0207,
      0x0208, 0x0209, 0x020a, 0x020b, 0x020c, 0x020d, 0x020e, 0x020f,
      0x0210, 0x0211, 0x0212, 0x0213, 0x0214, 0x0215, 0x0216, 0x0217,
      0x0218, 0x0219, 0x021a, 0x021b, 0x021c, 0x021d, 0x021e, 0x021f,
      0x0220, 0x0221, 0x0222, 0x0223, 0x0224, 0x0225, 0x0226, 0x0227,
      0x0228, 0x0229, 0x022a, 0x022b, 0x022c, 0x022d, 0x022e, 0x022f,
      0x0230, 0x0231, 0x0232, 0x0233, 0x0234, 0x0235, 0x0236, 0x0237,
      0x0238, 0x0239, 0x023a, 0x023b, 0x023c, 0x023d, 0x023e, 0x023f,
      0x0300],
    al: @[],
    am: @[SingleFieldTestStruct(a: 1)],
    an: @[SingleFieldTestStruct(a: 1), SingleFieldTestStruct(a: 2)],
    ao: @[
      SingleFieldTestStruct(a: 1), SingleFieldTestStruct(a: 2),
      SingleFieldTestStruct(a: 3), SingleFieldTestStruct(a: 4),
      SingleFieldTestStruct(a: 5)],
    ap: BitSeq(@[0x01'u8]),
    aq: BitSeq(@[0x2b'u8, 0x01]),
    ar: BitSeq(@[0x1a'u8]),
    `as`: BitSeq(@[0x0a'u8]),
    at: BitSeq(@[0xc5'u8, 0x06]),
    au: BitSeq(@[0xc5'u8, 0xc2, 0x01]),
    av: BitArray[256](bytes: [
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]),
    aw: BitList[256](@[
      0xff'u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x01]),
    ax: BitSeq(@[
      0xff'u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x01]),
    ay: BitArray[257](bytes: [
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x01]),
    az: BitList[257](@[
      0xff'u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x03]),
    ba: BitSeq(@[
      0xff'u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x03]),
    bb: BitSeq(@[0x03'u8]),
    bc: BitSeq(@[
      0xff'u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x01]),
    bd: BitSeq(@[
      0xff'u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0x03]),
    be: ProgressiveSingleFieldContainerTestStruct(a: 0xab),
    bf: ProgressiveSingleListContainerTestStruct(c: BitSeq(@[0x29'u8])),
    bg: ProgressiveVarTestStruct(a: 0xab),
    bh: ProgressiveVarTestStruct(
      a: 0xab, b: List[uint16, 123](@[]), c: BitSeq(@[0x01'u8])),
    bi: ProgressiveVarTestStruct(
      a: 0xab,
      b: List[uint16, 123](@[0x1122'u16, 0x3344]),
      c: BitSeq(@[0x29'u8])),
    bj: ProgressiveComplexTestStruct(
      a: 0xab,
      b: List[uint16, 123](@[0x1122'u16, 0x3344]),
      c: BitSeq(@[0x29'u8]),
      d: @[0x4242424242424242'u64, 0x3333333333333333'u64],
      e: @[
        SmallTestStruct(a: 0x4567, b: 0x0123),
        SmallTestStruct(a: 0x89ab, b: 0xcdef),
      ],
      f: @[
        @[
          VarTestStruct(
            a: 0x123, b: List[uint16, 1024](@[1'u16, 2, 3]), c: 0x12),
          VarTestStruct(
            a: 0x456, b: List[uint16, 1024](@[4'u16, 5, 6]), c: 0x45),
          VarTestStruct(
            a: 0x789, b: List[uint16, 1024](@[7'u16, 8, 9]), c: 0x78),
        ]
      ],
      g: List[ProgressiveSingleFieldContainerTestStruct, 10](@[
        ProgressiveSingleFieldContainerTestStruct(),
        ProgressiveSingleFieldContainerTestStruct(a: 0x00),
        ProgressiveSingleFieldContainerTestStruct(a: 0x42),
      ]),
      h: @[
        ProgressiveVarTestStruct(
          a: 0xab,
          b: List[uint16, 123](@[0x1122'u16, 0x3344]),
          c: BitSeq(@[0x29'u8])),
      ]))
  roots = block:
    var res = {
      # a
      64: d(1'u8),

      # b
      65: d(0x08'u8),

      # c
      66: d(0x1616'u16),

      # d
      67: d(0x32323232'u32),

      # e
      68: d(0x6464646464646464'u64),

      # f
      69: d(0x01281281281281281281281281281280'u128),

      # g
      70: d(0x02562562562562562562562562562562562562562560'u256),

      # h
      71: d(0b01010101_10101010_11111111_10101010_01010101'u64),

      # i
      144: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
      145: d([32'u8, 33, 34, 35, 36, 37, 38, 39, 40, 0b11111]),

      # j
      146: d(0b01010101_10101010_11111111_10101010_01010101'u64),
      147: d(40'u64),

      # k
      296: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
      297: d([32'u8, 33, 34, 35, 36, 37, 38, 39, 40, 0b11111]),
      149: d(333'u64),

      # l
      300: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0x7F]),
      301: d(0'u256),
      151: d(255'u64),

      # m
      304: d([0'u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]),
      305: d(0'u256),
      153: d(256'u64),

      # n
      308: d(0'u256),
      309: d(0'u256),
      155: d(0'u64),

      # o
      78: d([0'u8, 1]),

      # p
      158: d([1'u64, 2, 3, 4]),
      159: d([5'u64, 6]),

      # q
      320: d(0'u8),
      321: d(1'u8),
      322: d(1'u8),
      323: d(0'u8),

      # r
      648: d(0'u8),
      649: d(1'u8),
      650: d(1'u8),
      651: d(0'u8),
      163: d(2'u64),

      # s
      328: d(0'u256),
      329: d(0'u256),
      165: d(0'u64),

      # t
      332: d(0'u256),
      333: d(0'u256),
      167: d(0'u64),

      # u
      168: d(0'u8),
      169: d(1'u8),

      # v
      170: d(0'u8),
      171: d(1'u8),

      # w
      688: d(0'u8),
      689: d(1'u8),
      690: d(1'u8),
      691: d(0'u8),
      346: d(1'u8),
      347: d(0'u256),

      # x
      348: d(0'u8),
      349: d(1'u8),
      350: d(1'u8),
      351: d(0'u8),

      # y
      704: d(0'u8),
      705: d(1'u8),
      706: d(1'u8),
      707: d(0'u8),
      177: d(2'u64),

      # z
      356: d(0'u256),
      357: d(0'u256),
      179: d(0'u64),

      # aa
      90: d([1'u8, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]),

      # ab
      182: d([1'u8, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]),
      183: d(2'u64),

      # ac
      184: d([]),
      185: d(0'u64),

      # ad
      186: d(1'u8),
      187: d(0'u8),

      # ae
      376: d(1'u8),
      377: d(0'u8),
      189: d(1'u64),

      # af
      190: d(0'u256),
      191: d(0'u64),

      # ag
      192: d([]),
      193: d(0'u64),

      # ah
      388: d([]),
      389: d([0x0100'u16, 0x0101]),
      195: d(2'u64),

      # ai
      784: d([]),
      3140: d([0x0200'u16]),
      3141: d([]),
      3142: d([]),
      3143: d([]),
      393: d([
        0x0100'u16, 0x0101, 0x0102, 0x0103, 0x0104, 0x0105, 0x0106, 0x0107,
        0x0108, 0x0109, 0x010a, 0x010b, 0x010c, 0x010d, 0x010e, 0x010f]),
      197: d(0x11'u64),

      # aj
      792: d([]),
      3172: d([
        0x0200'u16, 0x0201, 0x0202, 0x0203, 0x0204, 0x0205, 0x0206, 0x0207,
        0x0208, 0x0209, 0x020a, 0x020b, 0x020c, 0x020d, 0x020e, 0x020f]),
      3173: d([
        0x0210'u16, 0x0211, 0x0212, 0x0213, 0x0214, 0x0215, 0x0216, 0x0217,
        0x0218, 0x0219, 0x021a, 0x021b, 0x021c, 0x021d, 0x021e, 0x021f]),
      3174: d([
        0x0220'u16, 0x0221, 0x0222, 0x0223, 0x0224, 0x0225, 0x0226, 0x0227,
        0x0228, 0x0229, 0x022a, 0x022b, 0x022c, 0x022d, 0x022e, 0x022f]),
      3175: d([
        0x0230'u16, 0x0231, 0x0232, 0x0233, 0x0234, 0x0235, 0x0236, 0x0237,
        0x0238, 0x0239, 0x023a, 0x023b, 0x023c, 0x023d, 0x023e, 0x023f]),
      397: d([
        0x0100'u16, 0x0101, 0x0102, 0x0103, 0x0104, 0x0105, 0x0106, 0x0107,
        0x0108, 0x0109, 0x010a, 0x010b, 0x010c, 0x010d, 0x010e, 0x010f]),
      199: d(0x50'u64),

      # ak
      1600: d([]),
      25616: d([0x0300'u16]),
      25617: d([]),
      25618: d([]),
      25619: d([]),
      25620: d([]),
      25621: d([]),
      25622: d([]),
      25623: d([]),
      25624: d([]),
      25625: d([]),
      25626: d([]),
      25627: d([]),
      25628: d([]),
      25629: d([]),
      25630: d([]),
      25631: d([]),
      3204: d([
        0x0200'u16, 0x0201, 0x0202, 0x0203, 0x0204, 0x0205, 0x0206, 0x0207,
        0x0208, 0x0209, 0x020a, 0x020b, 0x020c, 0x020d, 0x020e, 0x020f]),
      3205: d([
        0x0210'u16, 0x0211, 0x0212, 0x0213, 0x0214, 0x0215, 0x0216, 0x0217,
        0x0218, 0x0219, 0x021a, 0x021b, 0x021c, 0x021d, 0x021e, 0x021f]),
      3206: d([
        0x0220'u16, 0x0221, 0x0222, 0x0223, 0x0224, 0x0225, 0x0226, 0x0227,
        0x0228, 0x0229, 0x022a, 0x022b, 0x022c, 0x022d, 0x022e, 0x022f]),
      3207: d([
        0x0230'u16, 0x0231, 0x0232, 0x0233, 0x0234, 0x0235, 0x0236, 0x0237,
        0x0238, 0x0239, 0x023a, 0x023b, 0x023c, 0x023d, 0x023e, 0x023f]),
      401: d([
        0x0100'u16, 0x0101, 0x0102, 0x0103, 0x0104, 0x0105, 0x0106, 0x0107,
        0x0108, 0x0109, 0x010a, 0x010b, 0x010c, 0x010d, 0x010e, 0x010f]),
      201: d(0x51'u64),

      # al
      202: d([]),
      203: d(0'u64),

      # am
      408: d([]),
      409: d(1'u8),
      205: d(1'u64),

      # an
      824: d([]),
      3300: d(2'u8),
      3301: d([]),
      3302: d([]),
      3303: d([]),
      413: d(1'u8),
      207: d(2'u64),

      # ao
      832: d([]),
      3332: d(2'u8),
      3333: d(3'u8),
      3334: d(4'u8),
      3335: d(5'u8),
      417: d(1'u8),
      209: d(5'u64),

      # ap
      210: d([]),
      211: d(0'u64),

      # aq
      424: d([]),
      425: d(0x2b'u256),
      213: d(8'u64),

      # ar
      428: d([]),
      429: d(0x0a'u256),
      215: d(4'u64),

      # as
      432: d([]),
      433: d(0x02'u256),
      217: d(3'u64),

      # at
      436: d([]),
      437: d(0x02c5'u256),
      219: d(0x0a'u64),

      # au
      440: d([]),
      441: d(0xc2c5'u256),
      221: d(0x10'u64),

      # av
      111: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),

      # aw
      224: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      225: d(0x0100'u64),

      # ax
      452: d([]),
      453: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      227: d(0x0100'u64),

      # ay
      228: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      229: d(0x01'u64),

      # az
      460: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      461: d(0x01'u256),
      231: d(0x0101'u64),

      # ba
      928: d([]),
      3716: d(0x01'u256),
      3717: d([]),
      3718: d([]),
      3719: d([]),
      465: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      233: d(0x0101'u64),

      # bb
      468: d([]),
      469: d(0x01'u256),
      235: d(0x01'u64),

      # bc
      944: d([]),
      3780: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      3781: d([]),
      3782: d([]),
      3783: d([]),
      473: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      237: d(0x0200'u64),

      # bd
      952: d([]),
      3812: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      3813: d(0x01'u256),
      3814: d([]),
      3815: d([]),
      477: d(
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff'u256
      ),
      239: d(0x0201'u64),

      # be
      480: d([]),
      481: d(0xab'u8),
      241: d(0x01'u256),

      # bf
      968: d([]),
      3876: d([]),
      3877: d([]),
      3878: d([]),
      15516: d([]),
      15517: d(0x09'u256),
      7759: d(0x05'u64),
      485: d([]),
      243: d(0x10'u256),

      # bg
      976: d([]),
      3908: d([]),
      62544: d([]),
      62545: d([]),
      62546: d([]),
      62547: d([]),
      62548: d([]),
      62549: d([]),
      62550: d([]),
      62551: d([]),
      7819: d(0x00'u64),
      3910: d([]),
      7822: d([]),
      7823: d(0x00'u64),
      489: d(0xab'u8),
      245: d(0x15'u256),

      # bh
      984: d([]),
      3940: d([]),
      63056: d([]),
      63057: d([]),
      63058: d([]),
      63059: d([]),
      63060: d([]),
      63061: d([]),
      63062: d([]),
      63063: d([]),
      7883: d(0x00'u64),
      3942: d([]),
      7886: d([]),
      7887: d(0x00'u64),
      493: d(0xab'u8),
      247: d(0x15'u256),

      # bi
      992: d([]),
      3972: d([]),
      63568: d([0x1122'u16, 0x3344]),
      63569: d([]),
      63570: d([]),
      63571: d([]),
      63572: d([]),
      63573: d([]),
      63574: d([]),
      63575: d([]),
      7947: d(0x02'u64),
      3974: d([]),
      15900: d([]),
      15901: d(0x09'u256),
      7951: d(0x05'u64),
      497: d(0xab'u8),
      249: d(0x15'u256),

      # bj
      4000: d([]),
      1024256: d([]),
      8194056: d([]),
      32776228: d([]),
      524419664: d([0x1122'u16, 0x3344]),
      524419665: d([]),
      524419666: d([]),
      524419667: d([]),
      524419668: d([]),
      524419669: d([]),
      524419670: d([]),
      524419671: d([]),
      65552459: d(0x02'u64),
      32776230: d([]),
      131104924: d([]),
      131104925: d(0x09'u256),
      65552463: d(0x05'u64),
      4097029: d(0xab'u8),
      2048515: d(0x15'u256),
      512129: d(0x01'u64),
      256065: d([]),
      256066: d([]),
      256067: d([]),
      256068: d([]),
      256069: d([]),
      256070: d([]),
      256071: d([]),
      256072: d([]),
      256073: d([]),
      256074: d([]),
      256075: d([]),
      256076: d([]),
      256077: d([]),
      256078: d([]),
      256079: d([]),
      256080: d([]),
      256081: d([]),
      256082: d([]),
      256083: d([]),
      256084: d([]),
      256085: d([]),
      256086: d([]),
      256087: d([]),
      256088: d([]),
      256089: d([]),
      256090: d([]),
      256091: d([]),
      256092: d([]),
      256093: d([]),
      256094: d([]),
      256095: d([]),
      256096: d([]),
      256097: d([]),
      256098: d([]),
      256099: d([]),
      256100: d([]),
      256101: d([]),
      256102: d([]),
      256103: d([]),
      256104: d([]),
      256105: d([]),
      256106: d([]),
      256107: d([]),
      256108: d([]),
      256109: d([]),
      256110: d([]),
      256111: d([]),
      256112: d([]),
      256113: d([]),
      256114: d([]),
      256115: d([]),
      256116: d([]),
      256117: d([]),
      256118: d([]),
      256119: d([]),
      256120: d([]),
      256121: d([]),
      256122: d([]),
      256123: d([]),
      256124: d([]),
      256125: d([]),
      256126: d([]),
      256127: d([]),
      32016: d([]),
      32017: d([]),
      32018: d([]),
      128076: d([]),
      128077: d([0x4242424242424242'u64, 0x3333333333333333'u64]),
      64039: d(0x02'u64),
      32020: d([]),
      32021: d([]),
      32022: d([]),
      256184: d([]),
      2049480: d(0x89ab'u16),
      2049481: d(0xcdef'u16),
      1024741: d([]),
      1024742: d([]),
      1024743: d([]),
      256186: d(0x4567'u16),
      256187: d(0x0123'u16),
      64047: d(0x02'u64),
      128096: d([]),
      1024776: d([]),
      16396432: d(0x0456'u16),
      2098743424: d([0x0004'u16, 0x0005, 0x0006]),
      2098743425: d([]),
      2098743426: d([]),
      2098743427: d([]),
      2098743428: d([]),
      2098743429: d([]),
      2098743430: d([]),
      2098743431: d([]),
      2098743432: d([]),
      2098743433: d([]),
      2098743434: d([]),
      2098743435: d([]),
      2098743436: d([]),
      2098743437: d([]),
      2098743438: d([]),
      2098743439: d([]),
      2098743440: d([]),
      2098743441: d([]),
      2098743442: d([]),
      2098743443: d([]),
      2098743444: d([]),
      2098743445: d([]),
      2098743446: d([]),
      2098743447: d([]),
      2098743448: d([]),
      2098743449: d([]),
      2098743450: d([]),
      2098743451: d([]),
      2098743452: d([]),
      2098743453: d([]),
      2098743454: d([]),
      2098743455: d([]),
      2098743456: d([]),
      2098743457: d([]),
      2098743458: d([]),
      2098743459: d([]),
      2098743460: d([]),
      2098743461: d([]),
      2098743462: d([]),
      2098743463: d([]),
      2098743464: d([]),
      2098743465: d([]),
      2098743466: d([]),
      2098743467: d([]),
      2098743468: d([]),
      2098743469: d([]),
      2098743470: d([]),
      2098743471: d([]),
      2098743472: d([]),
      2098743473: d([]),
      2098743474: d([]),
      2098743475: d([]),
      2098743476: d([]),
      2098743477: d([]),
      2098743478: d([]),
      2098743479: d([]),
      2098743480: d([]),
      2098743481: d([]),
      2098743482: d([]),
      2098743483: d([]),
      2098743484: d([]),
      2098743485: d([]),
      2098743486: d([]),
      2098743487: d([]),
      32792867: d(0x03'u64),
      16396434: d(0x45'u8),
      16396435: d([]),
      16396436: d(0x0789'u16),
      2098743936: d([0x0007'u16, 0x0008, 0x0009]),
      2098743937: d([]),
      2098743938: d([]),
      2098743939: d([]),
      2098743940: d([]),
      2098743941: d([]),
      2098743942: d([]),
      2098743943: d([]),
      2098743944: d([]),
      2098743945: d([]),
      2098743946: d([]),
      2098743947: d([]),
      2098743948: d([]),
      2098743949: d([]),
      2098743950: d([]),
      2098743951: d([]),
      2098743952: d([]),
      2098743953: d([]),
      2098743954: d([]),
      2098743955: d([]),
      2098743956: d([]),
      2098743957: d([]),
      2098743958: d([]),
      2098743959: d([]),
      2098743960: d([]),
      2098743961: d([]),
      2098743962: d([]),
      2098743963: d([]),
      2098743964: d([]),
      2098743965: d([]),
      2098743966: d([]),
      2098743967: d([]),
      2098743968: d([]),
      2098743969: d([]),
      2098743970: d([]),
      2098743971: d([]),
      2098743972: d([]),
      2098743973: d([]),
      2098743974: d([]),
      2098743975: d([]),
      2098743976: d([]),
      2098743977: d([]),
      2098743978: d([]),
      2098743979: d([]),
      2098743980: d([]),
      2098743981: d([]),
      2098743982: d([]),
      2098743983: d([]),
      2098743984: d([]),
      2098743985: d([]),
      2098743986: d([]),
      2098743987: d([]),
      2098743988: d([]),
      2098743989: d([]),
      2098743990: d([]),
      2098743991: d([]),
      2098743992: d([]),
      2098743993: d([]),
      2098743994: d([]),
      2098743995: d([]),
      2098743996: d([]),
      2098743997: d([]),
      2098743998: d([]),
      2098743999: d([]),
      32792875: d(0x03'u64),
      16396438: d(0x78'u8),
      16396439: d([]),
      4099110: d([]),
      4099111: d([]),
      2049556: d(0x0123'u16),
      262343296: d([0x0001'u16, 0x0002, 0x0003]),
      262343297: d([]),
      262343298: d([]),
      262343299: d([]),
      262343300: d([]),
      262343301: d([]),
      262343302: d([]),
      262343303: d([]),
      262343304: d([]),
      262343305: d([]),
      262343306: d([]),
      262343307: d([]),
      262343308: d([]),
      262343309: d([]),
      262343310: d([]),
      262343311: d([]),
      262343312: d([]),
      262343313: d([]),
      262343314: d([]),
      262343315: d([]),
      262343316: d([]),
      262343317: d([]),
      262343318: d([]),
      262343319: d([]),
      262343320: d([]),
      262343321: d([]),
      262343322: d([]),
      262343323: d([]),
      262343324: d([]),
      262343325: d([]),
      262343326: d([]),
      262343327: d([]),
      262343328: d([]),
      262343329: d([]),
      262343330: d([]),
      262343331: d([]),
      262343332: d([]),
      262343333: d([]),
      262343334: d([]),
      262343335: d([]),
      262343336: d([]),
      262343337: d([]),
      262343338: d([]),
      262343339: d([]),
      262343340: d([]),
      262343341: d([]),
      262343342: d([]),
      262343343: d([]),
      262343344: d([]),
      262343345: d([]),
      262343346: d([]),
      262343347: d([]),
      262343348: d([]),
      262343349: d([]),
      262343350: d([]),
      262343351: d([]),
      262343352: d([]),
      262343353: d([]),
      262343354: d([]),
      262343355: d([]),
      262343356: d([]),
      262343357: d([]),
      262343358: d([]),
      262343359: d([]),
      4099115: d(0x03'u64),
      2049558: d(0x12'u8),
      2049559: d([]),
      256195: d(0x03'u64),
      64049: d(0x01'u64),
      32025: d([]),
      32026: d([]),
      32027: d([]),
      32028: d([]),
      32029: d([]),
      32030: d([]),
      4099968: d([]),
      4099969: d(0x00'u8),
      2049985: d(0x01'u256),
      4099972: d([]),
      4099973: d(0x00'u8),
      2049987: d(0x01'u256),
      4099976: d([]),
      4099977: d(0x42'u8),
      2049989: d(0x01'u256),
      1024995: d([]),
      1024996: d([]),
      1024997: d([]),
      1024998: d([]),
      1024999: d([]),
      1025000: d([]),
      1025001: d([]),
      1025002: d([]),
      1025003: d([]),
      1025004: d([]),
      1025005: d([]),
      1025006: d([]),
      1025007: d([]),
      64063: d(0x03'u64),
      4004: d([]),
      64080: d([0x1122'u16, 0x3344]),
      64081: d([]),
      64082: d([]),
      64083: d([]),
      64084: d([]),
      64085: d([]),
      64086: d([]),
      64087: d([]),
      8011: d(0x02'u64),
      4006: d([]),
      16028: d([]),
      16029: d(0x09'u256),
      8015: d(0x05'u64),
      501: d(0xab'u8),
      251: d(0x303115'u256),
    }.toOrderedTable
    for i in [
        72, 73, 148, 74, 150, 75, 152, 76, 154, 77, 79, 160, 161, 80,
        324, 325, 162, 81, 164, 82, 166, 83, 84, 85, 344, 345, 172, 173, 86,
        174, 175, 87, 352, 353, 176, 88, 178, 89, 91, 92, 93, 188, 94, 95,
        96, 194, 97, 1570, 1571, 785, 392, 196, 98,
        1586, 1587, 793, 396, 198, 99,
        12808, 12809, 12810, 12811, 12812, 12813, 12814, 12815,
        6404, 6405, 6406, 6407, 3202, 3203, 1601, 800,
        1602, 1603, 801, 400, 200, 100,
        101, 204, 102, 1650, 1651, 825, 412, 206, 103,
        1666, 1667, 833, 416, 208, 104,
        105, 212, 106, 214, 107, 216, 108, 218, 109, 220, 110,
        112, 226, 113, 114, 230, 115, 1858, 1859, 929, 464, 232, 116, 234, 117,
        1890, 1891, 945, 472, 236, 118, 1906, 1907, 953, 476, 238, 119,
        240, 120,
        7758, 3879, 1938, 1939, 969, 484, 242, 121,
        31272, 31273, 31274, 31275, 15636, 15637, 7818, 3909, 3911,
        1954, 1955, 977, 488, 244, 122,
        31528, 31529, 31530, 31531, 15764, 15765, 7882, 3941, 3943,
        1970, 1971, 985, 492, 246, 123,
        31784, 31785, 31786, 31787, 15892, 15893, 7946, 3973, 7950, 3975,
        1986, 1987, 993, 496, 248, 124,
        262209832, 262209833, 262209834, 262209835, 131104916, 131104917,
        65552458, 32776229, 65552462, 32776231, 16388114, 16388115, 8194057,
        4097028, 2048514, 1024257, 512128, 256064,
        128032, 128033, 128034, 128035, 128036, 128037, 128038, 128039,
        128040, 128041, 128042, 128043, 128044, 128045, 128046, 128047,
        128048, 128049, 128050, 128051, 128052, 128053, 128054, 128055,
        128056, 128057, 128058, 128059, 128060, 128061, 128062, 128063,
        64016, 64017, 64018, 64019, 64020, 64021, 64022, 64023,
        64024, 64025, 64026, 64027, 64028, 64029, 64030, 64031,
        32008, 32009, 32010, 32011, 32012, 32013, 32014, 32015,
        16004, 16005, 16006, 16007, 8002, 8003, 4001, 2000,
        64038, 32019,
        1024740, 512370, 512371, 256185, 128092, 128093, 64046, 32023,
        1049371712, 1049371713, 1049371714, 1049371715,
        1049371716, 1049371717, 1049371718, 1049371719,
        1049371720, 1049371721, 1049371722, 1049371723,
        1049371724, 1049371725, 1049371726, 1049371727,
        1049371728, 1049371729, 1049371730, 1049371731,
        1049371732, 1049371733, 1049371734, 1049371735,
        1049371736, 1049371737, 1049371738, 1049371739,
        1049371740, 1049371741, 1049371742, 1049371743,
        524685856, 524685857, 524685858, 524685859,
        524685860, 524685861, 524685862, 524685863,
        524685864, 524685865, 524685866, 524685867,
        524685868, 524685869, 524685870, 524685871,
        262342928, 262342929, 262342930, 262342931,
        262342932, 262342933, 262342934, 262342935,
        131171464, 131171465, 131171466, 131171467,
        65585732, 65585733, 32792866, 16396433, 8198216, 8198217, 4099108,
        1049371968, 1049371969, 1049371970, 1049371971,
        1049371972, 1049371973, 1049371974, 1049371975,
        1049371976, 1049371977, 1049371978, 1049371979,
        1049371980, 1049371981, 1049371982, 1049371983,
        1049371984, 1049371985, 1049371986, 1049371987,
        1049371988, 1049371989, 1049371990, 1049371991,
        1049371992, 1049371993, 1049371994, 1049371995,
        1049371996, 1049371997, 1049371998, 1049371999,
        524685984, 524685985, 524685986, 524685987,
        524685988, 524685989, 524685990, 524685991,
        524685992, 524685993, 524685994, 524685995,
        524685996, 524685997, 524685998, 524685999,
        262342992, 262342993, 262342994, 262342995,
        262342996, 262342997, 262342998, 262342999,
        131171496, 131171497, 131171498, 131171499,
        65585748, 65585749, 32792874, 16396437, 8198218, 8198219, 4099109,
        2049554, 2049555, 1024777, 512388,
        131171648, 131171649, 131171650, 131171651,
        131171652, 131171653, 131171654, 131171655,
        131171656, 131171657, 131171658, 131171659,
        131171660, 131171661, 131171662, 131171663,
        131171664, 131171665, 131171666, 131171667,
        131171668, 131171669, 131171670, 131171671,
        131171672, 131171673, 131171674, 131171675,
        131171676, 131171677, 131171678, 131171679,
        65585824, 65585825, 65585826, 65585827,
        65585828, 65585829, 65585830, 65585831,
        65585832, 65585833, 65585834, 65585835,
        65585836, 65585837, 65585838, 65585839,
        32792912, 32792913, 32792914, 32792915,
        32792916, 32792917, 32792918, 32792919,
        16396456, 16396457, 16396458, 16396459,
        8198228, 8198229, 4099114, 2049557, 1024778, 1024779, 512389,
        256194, 128097, 64048, 32024,
        2049984, 1024992, 2049986, 1024993, 2049988, 1024994,
        512496, 512497, 512498, 512499, 512500, 512501, 512502, 512503,
        256248, 256249, 256250, 256251, 128124, 128125, 64062, 32031,
        16008, 16009, 16010, 16011, 16012, 16013, 16014, 16015,
        8004, 8005, 8006, 8007, 4002, 4003, 2001, 1000,
        32040, 32041, 32042, 32043, 16020, 16021, 8010, 4005,
        8014, 4007, 2002, 2003, 1001,
        500, 250, 125]:
      res[i] = d(res.getOrDefault(2 * i + 0), res.getOrDefault(2 * i + 1))
    for i in 126 ..< 128:
      res[i] = d([])
    for i in countdown(63, 1):
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
    var i = 64
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
    proc doTest(i: uint64) =
      if i <= int.high.uint64 and roots.hasKey(i.int):
        return

      checkpoint $i
      var root {.noinit.}: array[1, Digest]
      check:
        hash_tree_root(x, [i.GeneralizedIndex], root).isErr
        hash_tree_root(x, [i.GeneralizedIndex]).isErr
        hash_tree_root(x, i.GeneralizedIndex).isErr

    for i in 0'u64 ..< 1'u64 shl 20:
      doTest i

    randomize()
    const numRandomTests = 1 shl 20
    for _ in 0 ..< numRandomTests:
      let i = rand(1'u64 shl 20 ..< 1'u64 shl 31)
      doTest i

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
      i = [64.GeneralizedIndex, 149, 144, 78, 167, 651, 347, 346, 691, 164]
      r = i.mapIt(roots.getOrDefault(it.int))
    var roots {.noinit.}: array[i.len, Digest]
    hash_tree_root(x, i, roots).get
    check:
      roots == r
      hash_tree_root(x, i).get == roots

  test "Multiproof (static)":
    const i = [64.GeneralizedIndex, 149, 144, 78, 167, 651, 347, 346, 691, 164]
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
