# ssz_serialization
# Copyright (c) 2018-2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/sequtils,
  stew/[bitops2, staticfor],
  unittest2,
  serialization/case_objects,
  ../ssz_serialization/proofs

type
  ProgTestStruct {.sszActiveFields: [1, 0, 1, 0, 1].} = object
    a: uint64
    c: uint64
    e: uint64

  U = distinct uint64
  UList = distinct seq[U]

  SelectorAC {.pure.} = enum
    a = 1
    c = 3
  SparseUnion {.allowDiscriminatorsWithoutZero.} = object
    case selector: SelectorAC
    of SelectorAC.a: aData: uint64
    of SelectorAC.c: cData: uint32

template toSszType*(v: U): auto = uint64(v)
template toSszType*(v: UList): auto = seq[U](v)

static:
  doAssert ProgTestStruct.isProgressiveContainer

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
      checkpoint "Verifying " & $index  & " --- static"
      check:
        nodes[index_int] == foo.hash_tree_root(index).get
        nodes[index_int] == allLeaves.hash_tree_root(index).get

    for index_int in 1 .. 15:
      let index = index_int.GeneralizedIndex
      checkpoint "Verifying " & $index  & " --- dynamic"
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
        valid = is_valid_merkle_branch(leaf, proof,
                                       log2trunc(index),
                                       get_subtree_index(index),
                                       root)
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

  test "get_generalized_index":
    type
      TwoFields = object
        a: uint64
        b: uint64

      ThreeFields = object
        a: uint64
        b: uint64
        c: uint64

      FourFields = object
        a: uint64
        b: uint64
        c: uint64
        d: uint64

      FiveFields = object
        a: uint64
        b: uint64
        c: uint64
        d: uint64
        e: uint64

      Inner = object
        x: uint64
        y: uint64

      Nested = object
        inner: Inner
        z: uint64

      WithList = object
        a: uint64
        items: List[Inner, 128]

      WithArray = object
        a: uint64
        items: array[8, Inner]

      WithBitList = object
        bits: BitList[256]

      WithBitArray = object
        bits: BitArray[256]

      SingleField = object
        a: uint64

      SelectorAB {.pure.} = enum
        a = 0
        b = 1

      TestUnion = object
        case selector: SelectorAB
        of SelectorAB.a: aData: uint64
        of SelectorAB.b: bData: Inner

    # Container navigation
    check:
      # 1-field: next_pow2(1) = 1
      get_generalized_index(SingleField, "a") == 1.GeneralizedIndex
      # 2-field: next_pow2(2) = 2
      get_generalized_index(TwoFields, "a") == 2.GeneralizedIndex
      get_generalized_index(TwoFields, "b") == 3.GeneralizedIndex
      # 3-field: next_pow2(3) = 4
      get_generalized_index(ThreeFields, "a") == 4.GeneralizedIndex
      get_generalized_index(ThreeFields, "b") == 5.GeneralizedIndex
      get_generalized_index(ThreeFields, "c") == 6.GeneralizedIndex
      # 4-field: next_pow2(4) = 4
      get_generalized_index(FourFields, "a") == 4.GeneralizedIndex
      get_generalized_index(FourFields, "d") == 7.GeneralizedIndex
      # 5-field: next_pow2(5) = 8
      get_generalized_index(FiveFields, "a") == 8.GeneralizedIndex
      get_generalized_index(FiveFields, "e") == 12.GeneralizedIndex

    # Nested container
    check:
      get_generalized_index(Nested, "inner") == 2.GeneralizedIndex
      get_generalized_index(Nested, "inner", "x") == 4.GeneralizedIndex
      get_generalized_index(Nested, "inner", "y") == 5.GeneralizedIndex
      get_generalized_index(Nested, "z") == 3.GeneralizedIndex

    # List: data at root*2, length at root*2+1
    check:
      get_generalized_index(WithList, "items", "__len__") ==
        7.GeneralizedIndex  # 3*2+1

    # Array: no mix-in-length
    check:
      get_generalized_index(WithArray, "items", 0) ==
        (3.GeneralizedIndex * nextPow2(8'u64).GeneralizedIndex + 0)
      get_generalized_index(WithArray, "items", 3) ==
        (3.GeneralizedIndex * nextPow2(8'u64).GeneralizedIndex + 3)

    # BitList: data at root*2, length at root*2+1
    check:
      get_generalized_index(WithBitList, "bits", "__len__") ==
        3.GeneralizedIndex  # 1*2+1

    # BitArray
    check:
      # 256 bits = 1 chunk, next_pow2(1) = 1
      get_generalized_index(WithBitArray, "bits", 0) == 1.GeneralizedIndex

    # Union
    check:
      get_generalized_index(TestUnion, "__selector__") == 3.GeneralizedIndex
      get_generalized_index(TestUnion, 0) == 2.GeneralizedIndex
      get_generalized_index(TestUnion, 1) == 2.GeneralizedIndex

    # Union: nested into variant field
    check:
      # selector 1 -> bData: Inner, then "y" -> gindex concat(2, 3)
      get_generalized_index(TestUnion, 1, "y") ==
        concat_generalized_indices(2.GeneralizedIndex, 3.GeneralizedIndex)

    # Union: out of range selector (runtime Result)
    for i in [-1.Limit, 2.Limit]:
      check:
        TestUnion.get_generalized_index(i).isErr

    # Non-contiguous union (CompatibleUnion style)
    check:
      SparseUnion.get_generalized_index(1) == 2.GeneralizedIndex
      SparseUnion.get_generalized_index(3) == 2.GeneralizedIndex
    static: doAssert not compiles(SparseUnion.get_generalized_index(0.Limit))
    static: doAssert not compiles(SparseUnion.get_generalized_index(2.Limit))
    static: doAssert not compiles(SparseUnion.get_generalized_index(4.Limit))

    # Runtime selector validation
    for i in -2.Limit .. 5.Limit:
      let res = SparseUnion.get_generalized_index(i)
      if i in [1.Limit, 3.Limit]:
        check res.isOk and res.get == 2.GeneralizedIndex
      else:
        check res.isErr

    # Progressive container
    check:
      get_generalized_index(ProgTestStruct, "a") ==
        2.GeneralizedIndex.concat_generalized_indices(
          progressiveIndexForChunk(0))
      get_generalized_index(ProgTestStruct, "c") ==
        2.GeneralizedIndex.concat_generalized_indices(
          progressiveIndexForChunk(2))
      get_generalized_index(ProgTestStruct, "e") ==
        2.GeneralizedIndex.concat_generalized_indices(
          progressiveIndexForChunk(4))
      get_generalized_index(ProgTestStruct, "__active_fields__") ==
        3.GeneralizedIndex

    # List element navigation
    check:
      get_generalized_index(WithList, "items", 0) ==
        (3.GeneralizedIndex * 2 * nextPow2(128'u64).GeneralizedIndex + 0)

    # List of progressive container — navigate into element's field
    check:
      get_generalized_index(
        List[ProgTestStruct, 4], 0, "__active_fields__") ==
        2.GeneralizedIndex.concat_generalized_indices(
          nextPow2(4'u64).GeneralizedIndex,
          3.GeneralizedIndex)

    # Array element -> sub-field
    check:
      get_generalized_index(WithArray, "items", 3, "y") ==
        (3.GeneralizedIndex * nextPow2(8'u64).GeneralizedIndex + 3) * 2 + 1

    # Distinct types
    check:
      # seq[distinct uint64] — U packs 4 per chunk like uint64
      get_generalized_index(seq[U], 0) ==
        get_generalized_index(seq[uint64], 0)
      get_generalized_index(seq[U], 5) ==
        get_generalized_index(seq[uint64], 5)
      # distinct seq[distinct uint64] — resolves via toSszType
      get_generalized_index(UList, 0) ==
        get_generalized_index(seq[uint64], 0)
      get_generalized_index(UList, "__len__") ==
        get_generalized_index(seq[uint64], "__len__")

    # Spec docstring examples: x[7].foo[3], len(x[12].bar)
    check:
      get_generalized_index(WithArray, "items", 7, "x") > 0.GeneralizedIndex
      get_generalized_index(WithList, "items", "__len__") > 0.GeneralizedIndex

    # Negative tests (compile-time errors for wrong type categories)
    static:
      doAssert not compiles(get_generalized_index(bool, "x"))
      doAssert not compiles(get_generalized_index(uint64, "x"))
      doAssert not compiles(get_generalized_index(TwoFields, 0))
      doAssert not compiles(get_generalized_index(array[8, uint64], "x"))

    # Compile-time evaluation
    static:
      doAssert get_generalized_index(TwoFields, "a") == 2.GeneralizedIndex
      doAssert get_generalized_index(Nested, "inner", "y") ==
        5.GeneralizedIndex

    # Round-trip: get_generalized_index -> build_proof -> verify
    block:
      let foo = Nested(inner: Inner(x: 42, y: 99), z: 7)
      let root = hash_tree_root(foo)
      const index = get_generalized_index(Nested, "inner", "y")
      let leaf = hash_tree_root(foo.inner.y)
      let proof = foo.build_proof(index).get
      check is_valid_merkle_branch(
        leaf, proof, log2trunc(index), get_subtree_index(index), root)
