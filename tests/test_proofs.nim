# ssz_serialization
# Copyright (c) 2018-2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/[macros, sequtils],
  stew/[bitops2, staticfor],
  serialization/case_objects,
  unittest2,
  ../ssz_serialization/proofs

suite "Merkle proofs":
  test "concat_generalized_indices":
    template checkConcat(indices_int: openArray[int], expected: int) =
      check concat_generalized_indices(
        indices_int.mapIt(it.GeneralizedIndex)) == expected.GeneralizedIndex

    checkConcat(newSeq[int](), 0b1)

    checkConcat([0b1, 0b1], 0b1)
    checkConcat([0b1, 0b1_0], 0b1_0)
    checkConcat([0b1, 0b1_1], 0b1_1)
    checkConcat([0b1, 0b1_111], 0b1_111)

    checkConcat([0b1_0, 0b1_1], 0b1_0_1)
    checkConcat([0b1_1, 0b1_0], 0b1_1_0)
    checkConcat([0b1_00, 0b1_1], 0b1_00_1)
    checkConcat([0b1_000, 0b1_01], 0b1_000_01)

    checkConcat([0b1_0, 0b1_0, 0b1_1], 0b1_0_0_1)
    checkConcat([0b1, 0b1_00, 0b1_1], 0b1_00_1)

    checkConcat([0b1_01010], 0b1_01010)

  test "get_branch_indices":
    check:
      toSeq(get_branch_indices(1.GeneralizedIndex)) == []
      toSeq(get_branch_indices(0b101010.GeneralizedIndex)) ==
        [
          0b101011.GeneralizedIndex,
          0b10100.GeneralizedIndex,
          0b1011.GeneralizedIndex,
          0b100.GeneralizedIndex,
          0b11.GeneralizedIndex
        ]

  test "get_path_indices":
    check:
      toSeq(get_path_indices(1.GeneralizedIndex)) == []
      toSeq(get_path_indices(0b101010.GeneralizedIndex)) ==
        [
          0b101010.GeneralizedIndex,
          0b10101.GeneralizedIndex,
          0b1010.GeneralizedIndex,
          0b101.GeneralizedIndex,
          0b10.GeneralizedIndex
        ]

  test "get_helper_indices":
    check:
      get_helper_indices(
        [
          8.GeneralizedIndex,
          9.GeneralizedIndex,
          14.GeneralizedIndex]) ==
        [
          15.GeneralizedIndex,
          6.GeneralizedIndex,
          5.GeneralizedIndex
        ]

  test "verify_merkle_multiproof":
    var allLeaves: array[8, Digest]
    for i in 0 ..< allLeaves.len:
      allLeaves[i] = digest([i.byte])

    type Foo = object
      a: Digest
      b: Digest
      c: Digest
      d: Digest
      e: Digest
      f: Digest
      g: Digest
      h: Digest

    let foo = Foo(
      a: allLeaves[0],
      b: allLeaves[1],
      c: allLeaves[2],
      d: allLeaves[3],
      e: allLeaves[4],
      f: allLeaves[5],
      g: allLeaves[6],
      h: allLeaves[7])

    var nodes: array[16, Digest]
    for i in 0 ..< allLeaves.len:
      nodes[i + 8] = allLeaves[i]
    for i in countdown(7, 1):
      nodes[i] = digest(nodes[2 * i + 0].data, nodes[2 * i + 1].data)

    staticFor index_int, 1 .. 15:
      const index = index_int.GeneralizedIndex
      checkpoint "Verifying " & $index & " --- static"
      check:
        nodes[index_int] == foo.hash_tree_root(index).get
        nodes[index_int] == allLeaves.hash_tree_root(index).get

    for index_int in 1 .. 15:
      let index = index_int.GeneralizedIndex
      checkpoint "Verifying " & $index & " --- dynamic"
      check:
        nodes[index_int] == foo.hash_tree_root(index).get
        nodes[index_int] == allLeaves.hash_tree_root(index).get

    proc verify(indices_int: openArray[int]) =
      let
        indices = indices_int.mapIt(it.GeneralizedIndex)
        helper_indices = get_helper_indices(indices)
        leaves = indices.mapIt(nodes[it])
        proof = helper_indices.mapIt(nodes[it])
        root = nodes[1]
      checkpoint "Verifying " & $indices & "---" & $helper_indices
      check:
        proof == foo.build_proof(indices).get
        proof == allLeaves.build_proof(indices).get
        verify_merkle_multiproof(leaves, proof, indices, root)

    verify([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])

    for a in 1 .. 15:
      verify([a])
      for b in 1 .. 15:
        verify([a, b])
        for c in 1 .. 15:
          verify([a, b, c])
          for d in 8 .. 15:
            verify([a, b, c, d])
            for e in 1 .. 7:
              verify([a, b, c, d, e])

  test "is_valid_merkle_branch":
    type TestCase = object
      root: string
      proof: seq[string]
      leaf: string
      index: uint64
      valid: bool

    let testCases = @[
      TestCase(
        root:
          "2a23ef2b7a7221eaac2ffb3842a506a981c009ca6c2fcbf20adbc595e56f1a93",
        proof: @[
          "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
          "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
        ],
        leaf:
          "0100000000000000000000000000000000000000000000000000000000000000",
        index: 4,
        valid: true
      ),
      TestCase(
        root:
          "2a23ef2b7a7221eaac2ffb3842a506a981c009ca6c2fcbf20adbc595e56f1a93",
        proof: @[
          "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
          "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
        ],
        leaf:
          "0100000000000000000000000000000000000000000000000000000000000000",
        index: 6,
        valid: false
      ),
      TestCase(
        root:
          "2a23ef2b7a7221eaac2ffb3842a506a981c009ca6c2fcbf20adbc595e56f1a93",
        proof: @[
          "0100000000000000000000000000000000000000000000000000000000000000",
          "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
        ],
        leaf:
          "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        index: 5,
        valid: true
      ),
      TestCase(
        root:
          "f1824b0084956084591ff4c91c11bcc94a40be82da280e5171932b967dd146e9",
        proof: @[
          "35210d64853aee79d03f30cf0f29c1398706cbbcacaf05ab9524f00070aec91e",
          "f38a181470ef1eee90a29f0af0a9dba6b7e5d48af3c93c29b4f91fa11b777582"
        ],
        leaf:
          "0100000000000000000000000000000000000000000000000000000000000000",
        index: 7,
        valid: true
      ),
      TestCase(
        root:
          "f1824b0084956084591ff4c91c11bcc94a40be82da280e5171932b967dd146e9",
        proof: @[
          "0000000000000000000000000000000000000000000000000000000000000000",
          "0000000000000000000000000000000000000000000000000000000000000000",
          "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b",
          "0100000000000000000000000000000000000000000000000000000000000000",
          "f38a181470ef1eee90a29f0af0a9dba6b7e5d48af3c93c29b4f91fa11b777582"
        ],
        leaf:
          "6001000000000000000000000000000000000000000000000000000000000000",
        index: 49,
        valid: true
      )
    ]

    for testCase in testCases:
      let
        root = Digest.fromHex(testCase.root)
        proof = mapIt(testCase.proof, Digest.fromHex(it))
        leaf = Digest.fromHex(testCase.leaf)
        index = testCase.index.GeneralizedIndex
        valid = is_valid_merkle_branch(
          leaf, proof, log2trunc(index), get_subtree_index(index), root)
      if testCase.valid:
        check valid
      else:
        check (not valid)

  test "progressiveIndexForChunk":
    check:
      progressiveIndexForChunk(0) == 0b1_0.GeneralizedIndex

      progressiveIndexForChunk(1) == 0b1_10_00.GeneralizedIndex
      progressiveIndexForChunk(2) == 0b1_10_01.GeneralizedIndex
      progressiveIndexForChunk(3) == 0b1_10_10.GeneralizedIndex
      progressiveIndexForChunk(4) == 0b1_10_11.GeneralizedIndex

      progressiveIndexForChunk(5) == 0b1_110_0000.GeneralizedIndex
      progressiveIndexForChunk(20) == 0b1_110_1111.GeneralizedIndex

type
  Inner = object
    x, y: uint64

  Nested = object
    inner: Inner
    z: uint64

  WithArray = object
    a: uint64
    items: array[8, Inner]

  WithBitArray = object
    bits: BitArray[256]

  WithList = object
    a: uint64
    items: List[Inner, 128]

  WithBitList = object
    bits: BitList[256]

  WithSeq = object
    items: seq[Inner]

  WithBitSeq = object
    bits: BitSeq

  SelectorAB {.pure.} = enum
    a = 0
    b = 1

  TestUnion = object
    case selector: SelectorAB
    of SelectorAB.a: aData: uint64
    of SelectorAB.b: bData: Inner

  DeepUnion = object
    case selector: SelectorAB
    of SelectorAB.a: aData: uint64
    of SelectorAB.b: bData: Nested

  MixedUnion = object
    case selector: SelectorAB
    of SelectorAB.a: aData: List[uint64, 64]
    of SelectorAB.b: bData: Inner

  NestedUnion = object
    case selector: SelectorAB
    of SelectorAB.a: aData: TestUnion
    of SelectorAB.b: bData: Inner

  HoleySelector {.pure.} = enum
    a = 3
    b = 1
    c = 99
    d = 2
    e = 5

  HoleyUnion {.allowDiscriminatorsWithoutZero.} = object
    case selector: HoleySelector
    of HoleySelector.a: aData: uint64
    of HoleySelector.b: bData: uint32
    of HoleySelector.c: cData: uint64
    of HoleySelector.d: dData: uint32
    of HoleySelector.e: eData: uint64

  ProgTestStruct {.sszActiveFields: [1, 0, 1, 0, 1].} = object
    a: uint64
    c: uint64
    e: uint64

  ProgTestTuple {.sszActiveFields: [1, 0, 1].} = tuple
    a: uint64
    c: uint64

  SingleField = object
    a: uint64

  TwoFields = object
    a, b: uint64

  ThreeFields = object
    a, b, c: uint64

  FourFields = object
    a, b, c, d: uint64

  FiveFields = object
    a, b, c, d, e: uint64

  DistinctInt = distinct uint64
  DistinctList = distinct seq[DistinctInt]

template toSszType(v: DistinctInt): auto = distinctBase(v)
template toSszType(v: DistinctList): auto = distinctBase(v)

static:
  doAssert ProgTestStruct.isProgressiveContainer
  doAssert ProgTestTuple.isProgressiveContainer

suite "get_generalized_index":
  func buildGindexCalls(
      T, path: NimNode): tuple[staticCall, runtimeCall, varDecls: NimNode] =
    result.staticCall = newCall(newDotExpr(T, ident"get_generalized_index"))
    result.runtimeCall = newCall(newDotExpr(T, ident"get_generalized_index"))
    result.varDecls = newStmtList()
    for i in 0 ..< path.len:
      let p = path[i]
      result.staticCall.add p
      let v = nskLet.genSym "p"
      result.runtimeCall.add v
      if p.kind == nnkStrLit:
        result.varDecls.add quote do:
          let `v` = `p`
      else:
        result.varDecls.add quote do:
          let `v` = `p`.Limit

  macro checkOk(
      T: typedesc, expected: GeneralizedIndex,
      path: varargs[untyped]): untyped =
    let (staticCall, runtimeCall, varDecls) = T.buildGindexCalls(path)
    var code = newStmtList()
    code.add quote do:
      check `staticCall` == `expected`
    if path.len > 0:
      code.add quote do:
        block:
          `varDecls`
          check `runtimeCall`.get == `expected`
    code

  macro checkErr(T: typedesc, path: varargs[untyped]): untyped =
    let (staticCall, runtimeCall, varDecls) = T.buildGindexCalls(path)
    quote do:
      check not compiles(`staticCall`)
      block:
        `varDecls`
        check `runtimeCall`.isErr

  test "Basic":
    bool.checkErr("x")
    uint64.checkErr("x")
    uint64.checkErr(0)

  test "Array":
    WithArray.checkOk(0b1_1_000.GeneralizedIndex, "items", 0)
    WithArray.checkOk(0b1_1_011.GeneralizedIndex, "items", 3)
    WithArray.checkOk(0b1_1_011_1.GeneralizedIndex, "items", 3, "y")
    WithArray.checkOk(0b1_1_111_0.GeneralizedIndex, "items", 7, "x")
    WithBitArray.checkOk(0b1.GeneralizedIndex, "bits", 0)
    WithBitArray.checkOk(0b1.GeneralizedIndex, "bits", 255)
    HashArray[8, uint64].checkOk(0b1_0.GeneralizedIndex, 3)
    array[8, uint64].checkErr(8)
    array[8, uint64].checkErr(-1)

  test "List":
    WithList.checkOk(0b1_1_0_0000000.GeneralizedIndex, "items", 0)
    WithList.checkOk(0b1_1_0_0000000_1.GeneralizedIndex, "items", 0, "y")
    WithList.checkOk(0b1_1_1.GeneralizedIndex, "items", "__len__")
    WithBitList.checkOk(0b1_0.GeneralizedIndex, "bits", 0)
    WithBitList.checkOk(0b1_1.GeneralizedIndex, "bits", "__len__")
    List[ProgTestStruct, 4]
      .checkOk(0b1_0_00_1.GeneralizedIndex, 0, "__active_fields__")
    HashList[uint64, 128].checkOk(0b1_0_00000.GeneralizedIndex, 0)
    HashList[uint64, 128].checkOk(0b1_1.GeneralizedIndex, "__len__")
    List[uint64, 128].checkErr(128)
    List[uint64, 128].checkErr(-1)

  test "Seq":
    seq[uint64].checkOk(0b1_0_0.GeneralizedIndex, 0)
    seq[uint64].checkOk(0b1_0_1110_000100.GeneralizedIndex, 100)
    seq[uint64].checkOk(0b1_1.GeneralizedIndex, "__len__")
    BitSeq.checkOk(0b1_0_0.GeneralizedIndex, 0)
    BitSeq.checkOk(0b1_0_10_10.GeneralizedIndex, 1000)
    BitSeq.checkOk(0b1_1.GeneralizedIndex, "__len__")
    WithSeq.checkOk(0b1_0_0_0.GeneralizedIndex, "items", 0, "x")
    WithSeq.checkOk(0b1_1.GeneralizedIndex, "items", "__len__")
    WithBitSeq.checkOk(0b1_0_0.GeneralizedIndex, "bits", 0)
    WithBitSeq.checkOk(0b1_1.GeneralizedIndex, "bits", "__len__")
    HashSeq[uint64].checkOk(0b1_0_0.GeneralizedIndex, 0)
    HashSeq[uint64].checkOk(0b1_1.GeneralizedIndex, "__len__")
    seq[uint64].checkErr(-1)

  test "Union":
    TestUnion.checkOk(0b1_0.GeneralizedIndex, 0)
    TestUnion.checkOk(0b1_0.GeneralizedIndex, 1)
    TestUnion.checkOk(0b1_0_1.GeneralizedIndex, 1, "y")
    TestUnion.checkOk(0b1_1.GeneralizedIndex, "__selector__")
    NestedUnion.checkOk(0b1_0_0_1.GeneralizedIndex, 0, 1, "y")
    NestedUnion.checkOk(0b1_0_1.GeneralizedIndex, 1, "y")
    NestedUnion.checkOk(0b1_1.GeneralizedIndex, "__selector__")
    TestUnion.checkErr(2)
    TestUnion.checkErr(-1)
    TestUnion.checkErr(0, "y")
    TestUnion.checkErr(1, "z")
    DeepUnion.checkErr(0, "inner", "x")
    MixedUnion.checkErr(1, "__len__")

    HoleyUnion.checkOk(0b1_0.GeneralizedIndex, 3)
    HoleyUnion.checkOk(0b1_0.GeneralizedIndex, 1)
    HoleyUnion.checkOk(0b1_0.GeneralizedIndex, 99)
    HoleyUnion.checkOk(0b1_0.GeneralizedIndex, 2)
    HoleyUnion.checkOk(0b1_0.GeneralizedIndex, 5)
    HoleyUnion.checkOk(0b1_1.GeneralizedIndex, "__selector__")
    HoleyUnion.checkErr(0)
    HoleyUnion.checkErr(4)
    HoleyUnion.checkErr(98)
    HoleyUnion.checkErr(100)

  test "Progressive container":
    ProgTestStruct.checkOk(0b1_0_0.GeneralizedIndex, "a")
    ProgTestStruct.checkOk(0b1_0_10_01.GeneralizedIndex, "c")
    ProgTestStruct.checkOk(0b1_0_10_11.GeneralizedIndex, "e")
    ProgTestStruct.checkOk(0b1_1.GeneralizedIndex, "__active_fields__")
    ProgTestTuple.checkOk(0b1_0_0.GeneralizedIndex, 0)
    ProgTestTuple.checkOk(0b1_0_10_01.GeneralizedIndex, 1)
    ProgTestTuple.checkOk(0b1_1.GeneralizedIndex, "__active_fields__")
    ProgTestStruct.checkErr("b")
    ProgTestStruct.checkErr("d")
    ProgTestTuple.checkErr(2)

  test "Object":
    SingleField.checkOk(0b1.GeneralizedIndex, "a")
    SingleField.checkErr(0)
    TwoFields.checkOk(0b1_0.GeneralizedIndex, "a")
    TwoFields.checkOk(0b1_1.GeneralizedIndex, "b")
    TwoFields.checkErr(1)
    ThreeFields.checkOk(0b1_00.GeneralizedIndex, "a")
    ThreeFields.checkOk(0b1_01.GeneralizedIndex, "b")
    ThreeFields.checkOk(0b1_10.GeneralizedIndex, "c")
    ThreeFields.checkErr(2)
    FourFields.checkOk(0b1_00.GeneralizedIndex, "a")
    FourFields.checkOk(0b1_11.GeneralizedIndex, "d")
    FourFields.checkErr(3)
    FiveFields.checkOk(0b1_000.GeneralizedIndex, "a")
    FiveFields.checkOk(0b1_100.GeneralizedIndex, "e")
    FiveFields.checkErr(4)
    Nested.checkOk(0b1_0.GeneralizedIndex, "inner")
    Nested.checkOk(0b1_0_0.GeneralizedIndex, "inner", "x")
    Nested.checkOk(0b1_0_1.GeneralizedIndex, "inner", "y")
    Nested.checkOk(0b1_1.GeneralizedIndex, "z")
    Nested.checkOk(0b1.GeneralizedIndex)
    Nested.checkErr(5)
    Nested.checkErr("")
    Nested.checkErr("nonexistent")
    Nested.checkErr("inner", "nonexistent")
    Nested.checkErr("nonexistent", "x")

  test "Tuple":
    (uint64, uint64).checkOk(0b1_0.GeneralizedIndex, 0)
    (uint64, uint64).checkOk(0b1_1.GeneralizedIndex, 1)
    (uint64, uint64, uint64).checkOk(0b1_00.GeneralizedIndex, 0)
    (uint64, uint64, uint64).checkOk(0b1_10.GeneralizedIndex, 2)
    (uint64, uint64).checkErr(2)
    (uint64, uint64).checkErr("x")

  test "Distinct":
    seq[DistinctInt].checkOk(0b1_0_0.GeneralizedIndex, 0)
    seq[DistinctInt].checkOk(0b1_0_10_00.GeneralizedIndex, 5)
    DistinctList.checkOk(0b1_0_0.GeneralizedIndex, 0)
    DistinctList.checkOk(0b1_1.GeneralizedIndex, "__len__")

  test "Round-trip with build_proof":
    let
      foo = Nested(inner: Inner(x: 42, y: 99), z: 7)
      root = hash_tree_root(foo)
    const index = Nested.get_generalized_index("inner", "y")
    let
      leaf = hash_tree_root(foo.inner.y)
      proof = foo.build_proof(index).get
    check is_valid_merkle_branch(
      leaf, proof, log2trunc(index), get_subtree_index(index), root)
