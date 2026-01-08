# ssz_serialization
# Copyright (c) 2018-2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/typetraits,
  unittest2, stew/byteutils,
  ../ssz_serialization,
  ../ssz_serialization/[merkleization, navigator, dynamic_navigator]

from nimcrypto/utils import fromHex

# TODO: Move to types?
func `$`*(x: Digest): string =
  x.data.toHex()

type
  SomeEnum = enum
    A, B, C

  Simple = object
    flag: bool
    ignored {.dontSerialize.}: string
    data: array[256, bool]
    data2: HashArray[256, bool]

  NonFixed = object
    data: HashList[uint64, 1024]

  DistinctInt = distinct uint64

  Nested = object
    simple: Simple

template toSszType*(v: DistinctInt): auto = uint64(v)

template fromSszBytes*(T: type DistinctInt, bytes: openArray[byte]): T =
  T fromSszBytes(uint64, bytes)

func `==`(a, b: DistinctInt): bool =
  distinctBase(a) == distinctBase(b)

template reject(stmt) =
  doAssert(not compiles(stmt))

static:
  doAssert isFixedSize(bool) == true
  doAssert isFixedSize(uint64) == true
  doAssert isFixedSize(DistinctInt) == true

  doAssert fixedPortionSize(array[10, bool]) == 10
  doAssert fixedPortionSize(array[SomeEnum, uint64]) == 24
  doAssert fixedPortionSize(array[SomeEnum, DistinctInt]) == 24
  doAssert fixedPortionSize(array[3..5, List[byte, 256]]) == 12

  doAssert minSize(array[10, bool]) == 10
  doAssert minSize(array[SomeEnum, uint64]) == 24
  doAssert minSize(array[SomeEnum, DistinctInt]) == 24
  doAssert minSize(array[3..5, List[byte, 256]]) == 3 * 4

  doAssert maxSize(array[10, bool]) == 10
  doAssert maxSize(array[SomeEnum, uint64]) == 24
  doAssert maxSize(array[SomeEnum, DistinctInt]) == 24
  doAssert maxSize(array[3..5, List[byte, 256]]) == 3 * (4 + 256)

  doAssert isFixedSize(array[20, bool]) == true
  doAssert isFixedSize(Simple) == true
  doAssert isFixedSize(List[bool, 128]) == false

  doAssert minSize(array[20, bool]) == 20
  doAssert minSize(Simple) == 1 + 256 + 256
  doAssert minSize(List[bool, 128]) == 0

  doAssert maxSize(array[20, bool]) == 20
  doAssert maxSize(Simple) == 1 + 256 + 256
  doAssert maxSize(List[bool, 128]) == 128

  doAssert isFixedSize(NonFixed) == false

  doAssert minSize(NonFixed) == 4

  doAssert maxSize(NonFixed) == 4 + 1024 * 8

  doAssert minSize(array[20, BitList[24]]) == 20 * (4 + 1)
  doAssert minSize(HashList[BitList[24], 20]) == 0
  doAssert minSize(HashList[NonFixed, 20]) == 0

  doAssert maxSize(array[20, BitList[24]]) == 20 * (4 + 4)
  doAssert maxSize(HashList[BitList[24], 20]) == 20 * (4 + 4)
  doAssert maxSize(HashList[NonFixed, 20]) == 20 * (4 + (4 + 1024 * 8))

  reject fixedPortionSize(int)
  reject minSize(int)
  reject maxSize(int)

type
  ObjWithFields = object
    f0: uint8
    f1: uint32
    f2: array[20, byte]
    f3: Digest

static:
  doAssert fixedPortionSize(ObjWithFields) ==
    1 + 4 + sizeof(array[20, byte]) + (256 div 8)

type
  Foo = object
    bar: Bar

  BarList = List[uint64, 128]

  Bar = object
    b: BarList
    baz: Baz

  Baz = object
    i: uint64

func toDigest[N: static int](x: array[N, byte]): Digest =
  result.data[0 .. N-1] = x

proc readSszBytes*(
    data: openArray[byte], val: var Simple) {.raises: [SszError].} =
  readSszValue(data, val)
  val.ignored = "overloaded"

suite "SSZ navigator":
  test "simple object fields":
    var foo = Foo(bar: Bar(b: BarList @[1'u64, 2, 3], baz: Baz(i: 10'u64)))
    let encoded = SSZ.encode(foo)

    check SSZ.decode(encoded, Foo) == foo

    let mountedFoo = sszMount(encoded, Foo)
    check mountedFoo.bar.b[] == BarList @[1'u64, 2, 3]

    let mountedBar = mountedFoo.bar
    check mountedBar.baz.i == 10'u64

  test "lists with max size":
    let a = [byte 0x01, 0x02, 0x03].toDigest
    let b = [byte 0x04, 0x05, 0x06].toDigest
    let c = [byte 0x07, 0x08, 0x09].toDigest

    var xx: List[uint64, 16]
    check:
      not xx.setLen(17)
      xx.setLen(16)

    var leaves = HashList[Digest, 1'i64 shl 3]()
    check:
      leaves.add a
      leaves.add b
      leaves.add c
    let root = hash_tree_root(leaves)
    check $root == "5248085b588fab1dd1e03f3cd62201602b12e6560665935964f46e805977e8c5"

    while leaves.len < 1 shl 3:
      check:
        leaves.add c
        hash_tree_root(leaves) == hash_tree_root(leaves.data)

    leaves = default(type leaves)

    while leaves.len < (1 shl 3) - 1:
      check:
        leaves.add c
        leaves.add c
        hash_tree_root(leaves) == hash_tree_root(leaves.data)

    leaves = default(type leaves)

    while leaves.len < (1 shl 3) - 2:
      check:
        leaves.add c
        leaves.add c
        leaves.add c
        hash_tree_root(leaves) == hash_tree_root(leaves.data)

    for i in 0 ..< leaves.data.len - 2:
      leaves[i] = a
      leaves[i + 1] = b
      leaves[i + 2] = c
      check hash_tree_root(leaves) == hash_tree_root(leaves.data)

    var leaves2 = HashList[Digest, 1'i64 shl 48]() # Large number!
    check:
      leaves2.add a
      leaves2.add b
      leaves2.add c
      hash_tree_root(leaves2) == hash_tree_root(leaves2.data)

    var leaves3 = HashList[Digest, 7]() # Non-power-of-2
    check:
      hash_tree_root(leaves3) == hash_tree_root(leaves3.data)
      leaves3.add a
      leaves3.add b
      leaves3.add c
      hash_tree_root(leaves3) == hash_tree_root(leaves3.data)

    # cache invalidation on modification
    leaves3.mitem(0) = b
    check:
      leaves3.data[0] == b
      hash_tree_root(leaves3) == hash_tree_root(leaves3.data)

  template doBasicTypeTest(listImpl: untyped, maxLen: int) =
    template checkType(typ: untyped): untyped =
      var leaves: typ.listImpl
      while leaves.len < maxLen:
        checkpoint $typ & " - " & $leaves.len
        when leaves is HashSeq:
          leaves.add leaves.len.typ
        else:
          check leaves.add leaves.len.typ
        check hash_tree_root(leaves) == hash_tree_root(leaves.data)

    checkType uint64
    checkType DistinctInt

  test "basictype - HashList":
    template listImpl[T](t: typedesc[T]): auto =
      HashList[T, 1'i64 shl 3]

    doBasicTypeTest listImpl, 1'i64 shl 3

  test "basictype - HashSeq":
    template listImpl[T](t: typedesc[T]): auto =
      HashSeq[T]

    doBasicTypeTest listImpl, 1000

suite "SSZ dynamic navigator":
  test "navigating fields":
    var fooOrig = Foo(bar: Bar(b: BarList @[1'u64, 2, 3], baz: Baz(i: 10'u64)))
    let fooEncoded = SSZ.encode(fooOrig)

    var navFoo = DynamicSszNavigator.init(fooEncoded, Foo)

    var navBar = navFoo.navigate("bar")
    check navBar.toJson(pretty = false) == """{"b":[1,2,3],"baz":{"i":10}}"""

    var navB = navBar.navigate("b")
    check navB.toJson(pretty = false) == "[1,2,3]"

    var navBaz = navBar.navigate("baz")
    var navI = navBaz.navigate("i")
    check navI.toJson == "10"

    expect KeyError:
      discard navBar.navigate("biz")

type
  Obj = object
    arr: array[8, Digest]

    li: List[Digest, 8]

  HashObj = object
    arr: HashArray[8, Digest]

    li: HashList[Digest, 8]

suite "hash":
  test "HashArray":
    var
      o = Obj()
      ho = HashObj()

    template mitem(v: array, idx: auto): auto = v[idx]
    template both(body) =
      block:
        template it: auto {.inject.} = o
        body
      block:
        template it: auto {.inject.} = ho
        body

      let htro = hash_tree_root(o)
      let htrho = hash_tree_root(ho)

      check:
        o.arr == ho.arr.data
        o.li == ho.li.data
        htro == htrho

    both: it.arr.mitem(0).data[0] = byte 1

    both: check: it.li.add Digest()

    template checkType(typ: untyped): untyped =
      var y: HashArray[32, typ]
      check: hash_tree_root(y) == hash_tree_root(y.data)
      for i in 0..<y.len:
        y[i] = 42.typ
        check: hash_tree_root(y) == hash_tree_root(y.data)

    checkType uint64
    checkType DistinctInt

  template doFixedTest(listImpl: untyped) =
    template checkType(typ: untyped): untyped =
      type MyList = typ.listImpl
      var
        small, large: MyList

      let
        emptyBytes = SSZ.encode(small)
        emptyRoot = hash_tree_root(small)

      when MyList is HashSeq:
        small.add(10.typ)
      else:
        check small.add(10.typ)

      for i in 0..<100:
        when MyList is HashSeq:
          large.add(i.typ)
        else:
          check large.add(i.typ)

      let
        sroot = hash_tree_root(small)
        lroot = hash_tree_root(large)

      check:
        sroot == hash_tree_root(small.data)
        lroot == hash_tree_root(large.data)

      var
        sbytes = SSZ.encode(small)
        lbytes = SSZ.encode(large)
        sloaded = SSZ.decode(sbytes, MyList)
        lloaded = SSZ.decode(lbytes, MyList)

      check:
        sroot == hash_tree_root(sloaded)
        lroot == hash_tree_root(lloaded)

      # Here we smoke test that the cache is reset correctly even when reading
      # into an existing instance - the instances are size-swapped so the reader
      # will have some more work to do
      readSszValue(sbytes, lloaded)
      readSszValue(lbytes, sloaded)

      check:
        lroot == hash_tree_root(sloaded)
        sroot == hash_tree_root(lloaded)

      readSszValue(emptyBytes, sloaded)
      check:
        emptyRoot == hash_tree_root(sloaded)

    checkType uint64
    checkType DistinctInt

  test "HashList fixed":
    template listImpl[T](t: typedesc[T]): auto =
      HashList[T, 1024]

    doFixedTest listImpl

  test "HashSeq fixed":
    template listImpl[T](t: typedesc[T]): auto =
      HashSeq[T]

    doFixedTest listImpl

  template doVariableTest[MyList](t: typedesc[MyList]) =
    var
      small, large: MyList

    let
      emptyBytes = SSZ.encode(small)
      emptyRoot = hash_tree_root(small)

    when MyList is HashSeq:
      small.add(NonFixed())
    else:
      check small.add(NonFixed())

    for i in 0..<100:
      when MyList is HashSeq:
        large.add(NonFixed())
      else:
        check large.add(NonFixed())

    let
      sroot = hash_tree_root(small)
      lroot = hash_tree_root(large)

    check:
      sroot == hash_tree_root(small.data)
      lroot == hash_tree_root(large.data)

    var
      sbytes = SSZ.encode(small)
      lbytes = SSZ.encode(large)
      sloaded = SSZ.decode(sbytes, MyList)
      lloaded = SSZ.decode(lbytes, MyList)

    check:
      sroot == hash_tree_root(sloaded)
      lroot == hash_tree_root(lloaded)

    # Here we smoke test that the cache is reset correctly even when reading
    # into an existing instance - the instances are size-swapped so the reader
    # will have some more work to do
    readSszValue(sbytes, lloaded)
    readSszValue(lbytes, sloaded)

    check:
      lroot == hash_tree_root(sloaded)
      sroot == hash_tree_root(lloaded)

    readSszValue(emptyBytes, sloaded)
    check:
      emptyRoot == hash_tree_root(sloaded)

    template checkReject(encoded: string): untyped =
      checkpoint encoded
      expect(SszError):
        var x: HashSeq[List[uint64, 1024]]
        readSszBytes(utils.fromHex(encoded), x)
      expect(SszError):
        var x: HashList[List[uint64, 1024], 1024]
        readSszBytes(utils.fromHex(encoded), x)
      expect(SszError):
        var x: List[List[uint64, 1024], 1024]
        readSszBytes(utils.fromHex(encoded), x)

    # < `offsetSize`
    checkReject "00"
    checkReject "0000"
    checkReject "000000"

    # Invalid offsets (too small)
    checkReject "00000000"
    checkReject "01000000"
    checkReject "02000000"
    checkReject "03000000"

    # Invalid offsets (too large)
    checkReject "05000000"
    checkReject "06000000"
    checkReject "07000000"
    checkReject "08000000"
    checkReject "09000000"

    # Invalid offsets (too small) with extra data
    checkReject "0000000000"
    checkReject "0100000000"
    checkReject "0200000000"
    checkReject "0300000000"

    # Valid offset with extra data
    checkReject "0400000000"

    # Invalid offsets (too large) with extra data
    checkReject "0500000000"
    checkReject "0600000000"
    checkReject "0700000000"
    checkReject "0800000000"
    checkReject "0900000000"

    # Invalid second offsets
    checkReject "0800000000000000"
    checkReject "0800000004000000"
    checkReject "0800000007000000"
    checkReject "0800000009000000"

    # Invalid second offsets with extra data
    checkReject "090000000900000000"
    checkReject "0900000009000000FF"
    checkReject "0A0000000A0000000000"
    checkReject "0A0000000A000000FFFF"
    checkReject "0B0000000B000000000000"
    checkReject "0B0000000B000000FFFFFF"

  test "HashList variable":
    doVariableTest HashList[NonFixed, 1024]

  test "HashSeq variable":
    doVariableTest HashSeq[NonFixed]

suite "underlong values":
  template testit(t: auto) =
    test "Underlong SSZ.decode: " & type(t).name():
      let encoded = SSZ.encode(t)
      expect(SszError):
        discard SSZ.decode(encoded[0..^2], type t)

    test "Underlong readSszBytes: " & type(t).name():
      let encoded = SSZ.encode(t)
      var t2: type t
      expect(SszError):
        readSszBytes(encoded[0..^2], t2)

    test "Overlong SSZ.decode: " & type(t).name():
      type S = typeof toSszType(t)
      when S isnot BasicType | BitArray | array | HashArray | BitList | Simple:
        let encoded = SSZ.encode(t)
        expect(SszError):
          discard SSZ.decode(encoded & @[32'u8], type t)
      else:
        skip # TODO Difference between decode and readSszBytes needs revisiting

    test "Overlong readSszBytes: " & type(t).name():
      type S = typeof toSszType(t)
      when S isnot BitList | Simple:
        let encoded = SSZ.encode(t)
        var t2: type t
        expect(SszError):
          readSszBytes(encoded & @[32'u8], t2)
      else:
        skip # TODO Difference between decode and readSszBytes needs revisiting

  # All SszType types
  testit(default(bool))
  testit(default(uint8))
  testit(default(uint16))
  testit(default(uint32))
  testit(default(uint64))
  testit(default(UInt128))
  testit(default(UInt256))
  testit(default(DistinctInt))
  testit(default(array[32, uint8]))
  testit(default(HashArray[32, uint8]))
  testit(List[uint64, 32].init(@[42'u64]))
  testit(List[DistinctInt, 32].init(@[42.DistinctInt]))
  testit(HashList[uint64, 32].init(@[42'u64]))
  testit(HashList[DistinctInt, 32].init(@[42.DistinctInt]))
  testit(@[42'u64])
  testit(HashSeq[uint64].init(@[42'u64]))
  testit(@[42.DistinctInt])
  testit(HashSeq[DistinctInt].init(@[42.DistinctInt]))
  testit(default(BitArray[32]))
  testit(BitList[32].init(10))
  testit(default(Simple))
  # TODO testit((32'u8, )) fails with a semcheck bug

suite "Distinct":
  test "HashArray":
    let
      a = default(HashArray[32, uint64])
      b = default(HashArray[32, DistinctInt])
    check sizeof(a) == sizeof(b)

  test "Digest":
    type
      MockDigest = object
        data: array[32*8, byte]

    var
      x: Digest
      y: MockDigest
      xx: Digest
      yy: MockDigest

    let
      encodedX = SSZ.encode(x)
      encodedY = SSZ.encode(y)

    check encodedX != encodedY

    readSszBytes(encodedX, xx)
    readSszBytes(encodedY, yy)

    check xx == x
    check yy == y

  test "Object with distinct field":
    type
      ObjectWithDistinctField = object
        color: DistinctInt

    let
      obj = ObjectWithDistinctField(color: DistinctInt 123)
      encodedObj = SSZ.encode(obj)

    var xx: ObjectWithDistinctField
    readSszBytes(encodedObj, xx)

    check xx == obj

  test "readSszBytes overload works in nested objects":
    check:
      SSZ.decode(SSZ.encode(Simple()), Simple).ignored != ""
      SSZ.decode(SSZ.encode(Nested()), Nested).simple.ignored != ""
