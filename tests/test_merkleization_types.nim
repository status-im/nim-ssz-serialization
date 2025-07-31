# ssz_serialization
# Copyright (c) 2021-2023 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/tables,
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
      0x03]))
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
        1890, 1891, 945, 472, 236, 118, 1906, 1907, 953, 476, 238, 119]:
      res[i] = d(res.getOrDefault(2 * i + 0), res.getOrDefault(2 * i + 1))
    for i in 120 ..< 128:
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
    for i in 0 ..< 32768:
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
