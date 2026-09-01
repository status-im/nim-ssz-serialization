# ssz_serialization
# Copyright (c) 2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}
{.used.}

import
  std/[algorithm, random, sequtils, sets],
  stew/byteutils,
  unittest2,
  ../ssz_serialization,
  ../ssz_serialization/[merkleization, proofs]

type Foo = object
  x: Digest
  y: uint64

const foo = Foo(
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
        check:
          items.add(foo)
          items.hash_tree_root() == items.data.hash_tree_root()
      else:
        let count =
          when items is HashList:
            rand(int(items.maxLen) - 4)
          else:
            rand(4000)
        items.checkResize(count)

suite "HashList":
  runHashCacheTests(HashList[Foo, 8192])

suite "HashList mutation":
  template runMutationTests(maxLen: static Limit): untyped =
    test "Mutate elements after hashing - " & $maxLen:
      var hl: HashList[Foo, maxLen]
      for i in 0 ..< int(maxLen):
        check:
          hl.add(foo)
          hl.hash_tree_root() == hl.data.hash_tree_root()
        for j in 0 ..< hl.data.len:
          hl.mitem(j).y = uint64(1000 + i * 100 + j)
          check hl.hash_tree_root() == hl.data.hash_tree_root()

    test "Add after empty read - " & $maxLen:
      var hl: HashList[Foo, maxLen]
      try:
        readSszBytes(@[], hl)
      except SszError:
        raiseAssert "Valid SSZ"
      for i in 0 ..< int(maxLen):
        check:
          hl.add(foo)
          hl.hash_tree_root() == hl.data.hash_tree_root()

    test "Resize via read - " & $maxLen:
      var hl: HashList[Foo, maxLen]
      for i, len in [
          0, 0, int(maxLen), int(maxLen), 0, 1, 1, int(maxLen), 0, 0, 1]:
        let contents = (0 ..< len).mapIt(
          Foo(x: foo.x, y: uint64(1000 * (i + 1) + it)))
        try:
          readSszBytes(SSZ.encode(contents), hl)
        except SszError:
          raiseAssert "Valid SSZ"
        check hl.hash_tree_root() == hl.data.hash_tree_root()

  runMutationTests(1)
  runMutationTests(2)
  runMutationTests(3)
  runMutationTests(4)
  runMutationTests(8)

suite "HashSeq":
  runHashCacheTests(HashSeq[Foo])

suite "Cache layout equivalence (for HashSeq)":
  template checkEquivalence(maxLen: static Limit) =
    test $maxLen:
      var
        ha: HashArray[maxLen, Foo]
        hl: HashList[Foo, maxLen]
      for i in 0 ..< int(maxLen):
        ha.mitem(i) = foo
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

suite "HashArray":
  template runHashArrayTests(maxLen: static Limit): untyped =
    for numItems in deduplicate([0, maxLen div 3, maxLen div 2, maxLen]):
      test "Nested HashArray[3, uint64] - " & $numItems & "/" & $maxLen:
        var ha: HashArray[maxLen, HashArray[3, uint64]]
        for i in 0 ..< numItems:
          ha.mitem(i).mitem(0) = i.byte
        check ha.hash_tree_root() == ha.data.hash_tree_root()
        for i in 0 ..< numItems:
          ha.mitem(i).reset()
        check ha.hash_tree_root() == ha.data.hash_tree_root()

      test "Nested HashArray[8, uint64] - " & $numItems & "/" & $maxLen:
        var ha: HashArray[maxLen, HashArray[8, uint64]]
        for i in 0 ..< numItems:
          ha.mitem(i).mitem(0) = i.byte
        check ha.hash_tree_root() == ha.data.hash_tree_root()
        for i in 0 ..< numItems:
          ha.mitem(i).reset()
        check ha.hash_tree_root() == ha.data.hash_tree_root()

      test "Composite object - " & $numItems & "/" & $maxLen:
        var ha: HashArray[maxLen, Foo]
        for i in 0 ..< numItems:
          ha.mitem(i) = foo
          ha.mitem(i).x.data[0] = i.byte
        check ha.hash_tree_root() == ha.data.hash_tree_root()
        for i in 0 ..< numItems:
          ha.mitem(i).reset()
        check ha.hash_tree_root() == ha.data.hash_tree_root()

    test "Fill after hashing - " & $maxLen:
      var ha: HashArray[maxLen, Foo]
      for i in 0 ..< int(maxLen):
        ha.mitem(i) = foo
        ha.mitem(i).x.data[0] = i.byte
      check ha.hash_tree_root() == ha.data.hash_tree_root()
      ha.fill(foo)
      check ha.hash_tree_root() == ha.data.hash_tree_root()

  runHashArrayTests(1)
  runHashArrayTests(2)
  runHashArrayTests(3)
  runHashArrayTests(4)
  runHashArrayTests(5)
  runHashArrayTests(6)
  runHashArrayTests(7)
  runHashArrayTests(8)
  runHashArrayTests(9)
  runHashArrayTests(10)
  runHashArrayTests(50)
  runHashArrayTests(96)
  runHashArrayTests(127)
  runHashArrayTests(128)
  runHashArrayTests(129)

const BarXMaxLen = 9

type Bar = object
  x: HashArray[BarXMaxLen, uint64]
  y: uint64

suite "Multiproof cache":
  func init(T: typedesc[Foo], i: int): T =
    T(x: foo.x, y: (i + 1).uint64)

  func init(T: typedesc[Bar], i: int): T =
    var res: T
    for k in 0 ..< 9:
      res.x[k] = (i * 10 + k).uint64
    res.y = i.uint64
    res

  func copy[T](x: T): T =
    try:
      SSZ.decode(SSZ.encode(x), T)
    except SerializationError:
      raiseAssert "Valid SSZ"

  template runCachedTest(T: typedesc, maxGindex: GeneralizedIndex): untyped =
    let
      obj = initObj(T)
      suffix = " - " & $T & " (" & $maxGindex & ") - " & $obj.len

      allGindices = toSeq(1.GeneralizedIndex .. maxGindex)
      allGindicesPlusOne = toSeq(1.GeneralizedIndex .. maxGindex + 1)
      validGindices = allGindices.filterIt(obj.hash_tree_root(it).isOk)

      itemGindices = block:
        when ElemType(T) is Bar:
          var res: seq[GeneralizedIndex]
          for i in 0 ..< obj.len:
            res.add T.get_generalized_index(i).get
            for j in 0 ..< BarXMaxLen:
              res.add T.get_generalized_index(i, "x", j).get
            res.add T.get_generalized_index(i, "y").get
          res
        else:
          (0 ..< obj.len).mapIt(T.get_generalized_index(it).get).deduplicate()
      cachedGindices = block:
        var indices = initHashSet[GeneralizedIndex]()
        for idx in itemGindices.get_union_indices():
          indices.incl idx
        for idx in itemGindices:
          indices.excl idx
        var res = newSeqOfCap[GeneralizedIndex](indices.len)
        for idx in indices.items():
          res.add idx
        res

      topGindices = @[2.GeneralizedIndex, 3.GeneralizedIndex]
        .filterIt(obj.hash_tree_root(it).isOk)
      itemGindicesWithTop = topGindices & itemGindices
      evenGindicesWithTop = topGindices &
        itemGindices.filterIt(it == it.generalized_index_sibling_left)
      oddGindicesWithTop = topGindices &
        itemGindices.filterIt(it == it.generalized_index_sibling_right)

    randomize()
    const numRandomTests = 100
    var tests = @[
      allGindices, allGindicesPlusOne,
      validGindices, itemGindices, cachedGindices,
      topGindices, itemGindicesWithTop, evenGindicesWithTop, oddGindicesWithTop]
    for i in 1 .. maxGindex + 1:
      tests.add @[i.GeneralizedIndex]
    for _ in 0 ..< numRandomTests:
      var indices: seq[GeneralizedIndex]
      for i in (if rand(1.0) < 0.8: validGindices else: allGindices):
        if rand(1.0) < 0.35:
          indices.add i
      indices.shuffle()
      tests.add indices

    test "Cached matches uncached result" & suffix:
      for indices in tests:
        checkpoint $indices

        var
          uncached = initObj(T)
          uncachedRoots = newSeqUninit[Digest](indices.len)
          uncachedTopRoot: Digest
        let res1 =
          hash_tree_root(uncached, indices, uncachedRoots, uncachedTopRoot)

        var
          cached = initObj(T)
          cachedRoots = newSeqUninit[Digest](indices.len)
          cachedTopRoot: Digest
        let
          root = cached.hash_tree_root()
          res2 = hash_tree_root(cached, indices, cachedRoots, cachedTopRoot)

        check:
          hash_tree_root(uncached) == root
          hash_tree_root(cached) == root
          res1.isOk == res2.isOk
        if res1.isOk:
          check:
            uncachedRoots == cachedRoots
            uncachedTopRoot == cachedTopRoot
            uncachedTopRoot == root
          for o, i in indices:
            if i == 1.GeneralizedIndex:
              check uncachedRoots[o] == root

    if obj.len > 0:
      test "Mutation invalidates cache" & suffix:
        for indices in tests:
          let
            i = (0 ..< obj.len).rand()
            iIndex = T.get_generalized_index(i).get
            siblingIndex = iIndex.generalized_index_sibling
            j = block:
              var res = max(i, T.dataPerChunk) - T.dataPerChunk
              if T.get_generalized_index(res).get == siblingIndex:
                res
              else:
                res = min(i + T.dataPerChunk, obj.high)
                if T.get_generalized_index(res).get == siblingIndex:
                  res
                else:
                  i
          checkpoint $indices & "-" & $i

          var
            uncached = initObj(T)
            uncachedRoots = newSeqUninit[Digest](indices.len)
            uncachedTopRoot: Digest
          when T isnot HashArray:
            discard uncached.add(uncached.item(i))
          uncached.modObj(i)
          let res1 =
            hash_tree_root(uncached, indices, uncachedRoots, uncachedTopRoot)

          var
            cached = initObj(T)
            cachedRoots = newSeqUninit[Digest](indices.len)
            cachedTopRoot: Digest
          discard cached.hash_tree_root()
          when T isnot HashArray:
            discard cached.add(cached.item(i))
          cached.modObj(i)
          let res2 =
            hash_tree_root(cached, indices, cachedRoots, cachedTopRoot)

          var reference = initObj(T)
          when T isnot HashArray:
            discard reference.add(reference.item(i))
          reference.modObj(i)
          let root1 = reference.hash_tree_root()

          uncached.modObj(j)
          cached.modObj(j)
          reference.modObj(j)
          let root2 = reference.hash_tree_root()

          check:
            hash_tree_root(uncached) == root2
            hash_tree_root(cached) == root2
            res1.isOk == res2.isOk
          if res1.isOk:
            check:
              uncachedRoots == cachedRoots
              uncachedTopRoot == cachedTopRoot
              uncachedTopRoot == root1
            for o, i in indices:
              if i == 1.GeneralizedIndex:
                check uncachedRoots[o] == root1

      test "Cache avoids re-hashing" & suffix:
        when SSZ_DEBUG_COUNT_HASHES:
          var cached = initObj(T)
          let
            root = cached.hash_tree_root()
            numHashes = debugTotalSszHashes
          check:
            numHashes > 0
            cached.hash_tree_root() == root
            debugTotalSszHashes == numHashes
            cached.hash_tree_root(cachedGindices).isOk
            debugTotalSszHashes == numHashes

          if cached.len > 0:
            let numItemHashes = block:
              let numHashesBefore = debugTotalSszHashes
              discard default(ElemType(T)).hash_tree_root()
              debugTotalSszHashes - numHashesBefore

            when ElemType(T).dataPerChunk == 1:
              block:
                const itemGindex = T.get_generalized_index(0)
                let
                  itemRoot = cached.item(0).hash_tree_root()
                  numHashesBefore = debugTotalSszHashes
                check:
                  cached.hash_tree_root(itemGindex).get == itemRoot
                  debugTotalSszHashes <= numHashesBefore + numItemHashes

            let i = (0 ..< cached.len).rand()
            checkpoint $i
            cached.modObj(i)
            let numHashesBefore = debugTotalSszHashes
            discard cached.hash_tree_root()
            check debugTotalSszHashes <= numHashesBefore + 2 * numItemHashes +
              T.get_generalized_index(i).get.int64.layer.uint64

            let allHashes = debugTotalSszHashes
            check:
              cached.hash_tree_root(cachedGindices).isOk
              debugTotalSszHashes == allHashes

          when T is HashList:
            if cached.len < T.maxLen:
              check:
                cached.add(cached.item(0))
                cached.hashes.countIt(not isCached(it)) <=
                  max(cached.maxChunks, 2).binaryTreeHeight
        else:
          skip()

      test "Random operations" & suffix:
        var cached = initObj(T)

        const NumRandomTests = 200
        for _ in 0 ..< NumRandomTests:
          case rand(8)
          of 0:
            let i = (0 ..< cached.len).rand()
            checkpoint "mod-" & $i
            cached.modObj(i)
          of 1:
            let i = (0 ..< cached.len).rand()
            checkpoint "htr-leaf-" & $i
            check cached.hash_tree_root(T.get_generalized_index(i).get) ==
              cached.copy.hash_tree_root(T.get_generalized_index(i).get)
          of 2:
            let i = allGindices.sample()
            checkpoint "htr-all-" & $i
            check cached.hash_tree_root(i) == cached.copy.hash_tree_root(i)
          of 3:
            let i = validGindices.sample()
            checkpoint "htr-valid-" & $i
            check cached.hash_tree_root(i) == cached.copy.hash_tree_root(i)
          of 4:
            checkpoint "htr-top"
            check cached.hash_tree_root() == cached.copy.hash_tree_root()
          of 5:
            when typeof(cached) isnot HashArray:
              let i = (0 ..< cached.len).rand()
              checkpoint "htr-add-" & $i
              discard cached.add(cached.item(i))
          of 6:
            let frequency = rand(0.5)
            var
              indices = (if rand(1.0) < 0.2: allGindices else: validGindices)
                .filterIt(rand(1.0) < frequency)
              cachedRoots = newSeqUninit[Digest](indices.len)
              refRoots = newSeqUninit[Digest](indices.len)
            indices.shuffle()
            checkpoint "htr-multi-" & $indices
            let
              res1 = cached.hash_tree_root(indices, cachedRoots)
              res2 = cached.copy.hash_tree_root(indices, refRoots)
            check res1 == res2
            if res1.isOk:
              check cachedRoots == refRoots
          else:
            let frequency = rand(0.5)
            var
              indices = (if rand(1.0) < 0.2: allGindices else: validGindices)
                .filterIt(rand(1.0) < frequency)
              cachedRoots = newSeqUninit[Digest](indices.len)
              refRoots = newSeqUninit[Digest](indices.len)
              cachedTopRoot: Digest
              refTopRoot: Digest
            indices.shuffle()
            checkpoint "htr-multitop-" & $indices
            let
              res1 = cached.hash_tree_root(indices, cachedRoots, cachedTopRoot)
              res2 = cached.copy.hash_tree_root(indices, refRoots, refTopRoot)
            check res1 == res2
            if res1.isOk:
              check:
                cachedRoots == refRoots
                cachedTopRoot == refTopRoot

        var
          cachedRoots = newSeqUninit[Digest](validGindices.len)
          refRoots = newSeqUninit[Digest](validGindices.len)
          cachedTopRoot: Digest
          refTopRoot: Digest
        check:
          cached.hash_tree_root() == cached.copy.hash_tree_root()
          cached.hash_tree_root(validGindices, cachedRoots) ==
            cached.copy.hash_tree_root(validGindices, refRoots)
          cachedRoots == refRoots
          cached.hash_tree_root(validGindices, cachedRoots, cachedTopRoot) ==
            cached.copy.hash_tree_root(validGindices, refRoots, refTopRoot)
          cachedRoots == refRoots
          cachedTopRoot == refTopRoot

  block:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< T.maxLen:
          res[i] = (i + 1).uint64
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i) += 999'u64

    HashArray[8, uint64].runCachedTest(7.GeneralizedIndex)
    HashArray[9, uint64].runCachedTest(15.GeneralizedIndex)
    HashArray[17, uint64].runCachedTest(31.GeneralizedIndex)

  block:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< T.maxLen:
          res[i] = Foo.init(i)
        res

    template modObj(obj: untyped, i: int) =
      obj[i] = Foo.init(42)

    HashArray[1, Foo].runCachedTest(3.GeneralizedIndex)
    HashArray[3, Foo].runCachedTest(31.GeneralizedIndex)
    HashArray[4, Foo].runCachedTest(63.GeneralizedIndex)
    HashArray[6, Foo].runCachedTest(63.GeneralizedIndex)

  block:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< T.maxLen:
          res[i] = Bar.init(i)
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i).x.mitem(i mod BarXMaxLen) += 123'u64

    HashArray[3, Bar].runCachedTest(127.GeneralizedIndex)
    HashArray[4, Bar].runCachedTest(127.GeneralizedIndex)
    HashArray[6, Bar].runCachedTest(127.GeneralizedIndex)

  func zeroPrefixedChunk(i: int): uint64 =
    # Ensure every chunk starts with 8 zero bytes, so `isCached` report false
    # and the raw chunk is considered deliberately cleared (!= `uninitSentinel`)
    if i mod 4 == 0:
      0'u64
    else:
      i.uint64

  block:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< T.maxLen:
          res[i] = zeroPrefixedChunk(i)
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i) += 999'u64

    HashArray[4, uint64].runCachedTest(3.GeneralizedIndex)

  for n in [0, 1, 2, 4]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add(zeroPrefixedChunk(i))
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i) += 999'u64

    HashList[uint64, 4].runCachedTest(7.GeneralizedIndex)

  for n in [0, 1]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add(Foo.init(i))
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i) = Foo.init(42)

    HashList[Foo, 1].runCachedTest(7.GeneralizedIndex)

  for n in [0, 1, 2, 4, 5, 8, 16, 20, 21]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add(zeroPrefixedChunk(i))
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i) += 999'u64

    HashSeq[uint64].runCachedTest(63.GeneralizedIndex)

  for n in [0, 1, 2, 3, 4, 5, 7, 8, 9, 16, 31, 32]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add((i + 1).uint64)
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i) += 999'u64

    HashList[uint64, 32].runCachedTest(63.GeneralizedIndex)

  for n in [0, 1, 2, 3, 5, 8, 13, 16]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add(Foo.init(i))
        res

    template modObj(obj: untyped, i: int) =
      obj[i] = Foo.init(42)

    HashList[Foo, 16].runCachedTest(127.GeneralizedIndex)

  for n in [1, 3, 8]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add(Bar.init(i))
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i).x.mitem(i mod BarXMaxLen) += 123'u64

    HashList[Bar, 8].runCachedTest(127.GeneralizedIndex)

  for n in [0, 1, 2, 4, 5, 6, 7, 20, 21, 22, 84, 85, 86, 340, 341]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add((i + 1).uint64)
        res

    template modObj(obj: untyped, i: int) =
      obj.mitem(i) += 999'u64

    HashSeq[uint64].runCachedTest(1023.GeneralizedIndex)

  for n in [1, 2, 5, 6, 21, 22, 85, 86]:
    template initObj(T: typedesc): untyped =
      block:
        var res: T
        for i in 0 ..< n:
          doAssert res.add(Foo.init(i))
        res

    template modObj(obj: untyped, i: int) =
      obj[i] = Foo.init(42)

    HashSeq[Foo].runCachedTest(1023.GeneralizedIndex)

  test "Boundary at data end":
    var cached = HashList[uint64, 128].init(toSeq(0'u64 ..< 9'u64))
    discard hash_tree_root(cached)
    cached.mitem(0) += 1

    for i in [32.GeneralizedIndex, 16, 8, 4, 2]:
      check not isCached(cached.hashes.cachedPtrList(
        cached.indices, cached.maxChunks, i shr 1)[])
    check not isCached(cached.hashes[0])

    block:
      let i = [16.GeneralizedIndex, 17]
      var cachedRoots {.noinit.}, refRoots {.noinit.}: array[2, Digest]
      check:
        cached.hash_tree_root(i, cachedRoots) ==
          cached.copy.hash_tree_root(i, refRoots)
        cachedRoots == refRoots
        cachedRoots[1] == zeroHashes[2]

    block:
      let i = [8.GeneralizedIndex, 9]
      var cachedRoots {.noinit.}, refRoots {.noinit.}: array[2, Digest]
      check:
        cached.hash_tree_root(i, cachedRoots) ==
          cached.copy.hash_tree_root(i, refRoots)
        cachedRoots == refRoots
        cachedRoots[1] == zeroHashes[3]

  test "Progressive boundary at data end":
    var cached = HashSeq[uint64].init(toSeq(0'u64 ..< 22'u64))
    discard hash_tree_root(cached)
    cached.mitem(0) += 1
    check not isCached(cached.root)

    for i in 2'u64 .. 128'u64:
      checkpoint $i
      var cachedRoots {.noinit.}, refRoots {.noinit.}: array[2, Digest]
      let
        res1 = cached.hash_tree_root([i.GeneralizedIndex, 4], cachedRoots)
        res2 = cached.copy.hash_tree_root([i.GeneralizedIndex, 4], refRoots)
      check res1 == res2
      if res1.isOk:
        check cachedRoots == refRoots
    check cached.hash_tree_root() == cached.copy.hash_tree_root()

  type
    Inner = object
      a, b, c, d: uint64
    Outer = object
      x: Inner
      y: uint64

  func initTestArray(maxLen: static Limit = 8): HashArray[maxLen, Outer] =
    var res: HashArray[maxLen, Outer]
    for i in 0'u64 ..< maxLen.uint64:
      res.mitem(i).x.a = 100 + i
      res.mitem(i).y = 500 + i
    res

  test "Overlapped item root":
    let testArray = initTestArray()

    when SSZ_DEBUG_COUNT_HASHES:
      let numHalfHashes = block:
        let numHashesBefore = debugTotalSszHashes
        check testArray.copy.hash_tree_root(2.GeneralizedIndex).isOk
        debugTotalSszHashes - numHashesBefore

    block:
      var roots {.noinit.}: array[3, Digest]
      when SSZ_DEBUG_COUNT_HASHES:
        let numHashesBefore = debugTotalSszHashes
      check testArray.copy.hash_tree_root(
        [2.GeneralizedIndex, 9, 18], roots).isOk
      when SSZ_DEBUG_COUNT_HASHES:
        check debugTotalSszHashes == numHashesBefore + numHalfHashes
      check:
        roots[1] == testArray.item(1).hash_tree_root()
        roots[2] == testArray.item(1).x.hash_tree_root()

    block:
      var roots {.noinit.}: array[3, Digest]
      when SSZ_DEBUG_COUNT_HASHES:
        let numHashesBefore = debugTotalSszHashes
      check testArray.copy.hash_tree_root(
        [2.GeneralizedIndex, 9, 11], roots).isOk
      when SSZ_DEBUG_COUNT_HASHES:
        check debugTotalSszHashes == numHashesBefore + numHalfHashes
      check:
        roots[1] == testArray.item(1).hash_tree_root()
        roots[2] == testArray.item(3).hash_tree_root()

  when SSZ_DEBUG_COUNT_HASHES:
    let
      numOuterHashes = block:
        let numHashesBefore = debugTotalSszHashes
        discard default(Outer).hash_tree_root()
        debugTotalSszHashes - numHashesBefore
      numInnerHashes = block:
        let numHashesBefore = debugTotalSszHashes
        discard default(Inner).hash_tree_root()
        debugTotalSszHashes - numHashesBefore

  test "Multiproof hash counts":
    when SSZ_DEBUG_COUNT_HASHES:
      let numHalfHashes = block:
        let numHashesBefore = debugTotalSszHashes
        check initTestArray().copy.hash_tree_root(2.GeneralizedIndex).isOk
        debugTotalSszHashes - numHashesBefore
      check numHalfHashes == 4 * numOuterHashes + 3

      block:
        let
          testArray = initTestArray()
          tests = [
            (@[72.GeneralizedIndex], 0'u64),
            (@[18.GeneralizedIndex], numInnerHashes),
            (@[9.GeneralizedIndex], numOuterHashes),
            (@[9.GeneralizedIndex, 18], numOuterHashes),
            (@[9.GeneralizedIndex, 72], numOuterHashes),
          ]
        for (indices, numHashes) in tests:
          let numHashesBefore = debugTotalSszHashes
          check:
            testArray.hash_tree_root(indices).isOk
            debugTotalSszHashes == numHashesBefore + numHashes

      block:
        let tests = [
          (@[2.GeneralizedIndex, 9], numHalfHashes),
          (@[2.GeneralizedIndex, 9, 18], numHalfHashes),
          (@[2.GeneralizedIndex, 9, 11], numHalfHashes),
          (@[2.GeneralizedIndex, 18], numHalfHashes),
          (@[2.GeneralizedIndex, 18, 22], numHalfHashes),
        ]
        for (indices, numHashes) in tests:
          let numHashesBefore = debugTotalSszHashes
          check:
            initTestArray().hash_tree_root(indices).isOk
            debugTotalSszHashes == numHashesBefore + numHashes

      block:
        var testArray = initTestArray()
        discard testArray.hash_tree_root()
        let tests = [
          (@[2.GeneralizedIndex], 0'u64),
          (@[72.GeneralizedIndex], 0'u64),
          (@[18.GeneralizedIndex], numInnerHashes),
          (@[2.GeneralizedIndex, 18], numInnerHashes),
          (@[2.GeneralizedIndex, 9, 18], numOuterHashes),
        ]
        for (indices, numHashes) in tests:
          let numHashesBefore = debugTotalSszHashes
          check:
            testArray.hash_tree_root(indices).isOk
            debugTotalSszHashes == numHashesBefore + numHashes

        testArray.mitem(0).y += 1
        let numHashesBefore = debugTotalSszHashes
        check:
          testArray.hash_tree_root(2.GeneralizedIndex).isOk
          debugTotalSszHashes == numHashesBefore + 2 * numOuterHashes + 2

      for indices in [
          @[2.GeneralizedIndex, 9],
          @[2.GeneralizedIndex, 8],
          @[2.GeneralizedIndex, 9, 18]]:
        var testArray = initTestArray()
        discard testArray.hash_tree_root()
        testArray.mitem(0).y += 1
        let numHashesBefore = debugTotalSszHashes
        check:
          testArray.hash_tree_root(indices).isOk
          debugTotalSszHashes == numHashesBefore + 2 * numOuterHashes + 2

      block:
        var testArray = initTestArray()
        discard testArray.hash_tree_root()
        testArray.mitem(6).y += 1
        let numHashesBefore = debugTotalSszHashes
        check:
          testArray.hash_tree_root([3.GeneralizedIndex]).isOk
          debugTotalSszHashes == numHashesBefore + 2 * numOuterHashes + 2

      block:
        var testArray = initTestArray(16)
        discard testArray.hash_tree_root()
        testArray.mitem(14).y += 1
        let numHashesBefore = debugTotalSszHashes
        check:
          testArray.hash_tree_root([3.GeneralizedIndex]).isOk
          debugTotalSszHashes == numHashesBefore + 2 * numOuterHashes + 3
    else:
      skip()

  test "Multiproof with top root":
    when SSZ_DEBUG_COUNT_HASHES:
      let numOuterHashes = block:
        let numHashesBefore = debugTotalSszHashes
        discard hash_tree_root(default(Outer))
        debugTotalSszHashes - numHashesBefore
      block:
        let
          testArray = initTestArray()
          numTotalHashes = block:
            let numHashesBefore = debugTotalSszHashes
            discard testArray.copy.hash_tree_root()
            debugTotalSszHashes - numHashesBefore
        var
          roots {.noinit.}: array[1, Digest]
          topRoot {.noinit.}: Digest
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            testArray.hash_tree_root([8.GeneralizedIndex], roots, topRoot).isOk
            debugTotalSszHashes == numHashesBefore + numTotalHashes
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            testArray.hash_tree_root([8.GeneralizedIndex], roots, topRoot).isOk
            debugTotalSszHashes == numHashesBefore + numOuterHashes
        check:
          roots == [testArray.data[0].hash_tree_root()]
          topRoot == testArray.copy.hash_tree_root()

      block:
        let
          x = HashSeq[Outer].init(
            (0'u64 ..< 6'u64).mapIt(Outer(x: Inner(a: 100 + it), y: 500 + it)))
          numTotalHashes = block:
            let numHashesBefore = debugTotalSszHashes
            discard x.copy.hash_tree_root()
            debugTotalSszHashes - numHashesBefore
        var
          roots {.noinit.}: array[1, Digest]
          topRoot {.noinit.}: Digest
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            x.hash_tree_root([4.GeneralizedIndex], roots, topRoot).isOk
            debugTotalSszHashes == numHashesBefore + numTotalHashes
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            x.hash_tree_root([4.GeneralizedIndex], roots, topRoot).isOk
            debugTotalSszHashes == numHashesBefore
        check:
          roots == [x.data[0].hash_tree_root()]
          topRoot == x.copy.hash_tree_root()
    else:
      skip()

  test "Single chunk with top root":
    when SSZ_DEBUG_COUNT_HASHES:
      block:
        let x = initTestArray(1)
        var
          roots {.noinit.}: array[1, Digest]
          topRoot {.noinit.}: Digest
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            x.hash_tree_root([3.GeneralizedIndex], roots, topRoot).isOk
            debugTotalSszHashes == numHashesBefore + numOuterHashes
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            x.hash_tree_root([3.GeneralizedIndex], roots, topRoot).isOk
            debugTotalSszHashes == numHashesBefore
            topRoot == x.copy.hash_tree_root()
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            x.hash_tree_root([1.GeneralizedIndex], roots).isOk
            debugTotalSszHashes == numHashesBefore
            roots == [topRoot]
      block:
        let x = HashList[Outer, 1].init(@[Outer(x: Inner(a: 100), y: 500)])
        var
          roots {.noinit.}: array[1, Digest]
          topRoot {.noinit.}: Digest
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            x.hash_tree_root([5.GeneralizedIndex], roots, topRoot).isOk
            debugTotalSszHashes == numHashesBefore + numOuterHashes + 1
            topRoot == x.copy.hash_tree_root()
        block:
          let numHashesBefore = debugTotalSszHashes
          check:
            x.hash_tree_root([2.GeneralizedIndex], roots).isOk
            debugTotalSszHashes == numHashesBefore
    else:
      skip()

  test "Mutation with top root":
    when SSZ_DEBUG_COUNT_HASHES:
      var
        roots {.noinit.}: array[1, Digest]
        topRoot {.noinit.}: Digest
      for i in [8.GeneralizedIndex, 2]:
        var x = initTestArray()
        discard x.hash_tree_root()
        x.mitem(0).y += 1
        let numHashesBefore = debugTotalSszHashes
        check:
          x.hash_tree_root([i], roots, topRoot).isOk
          debugTotalSszHashes == numHashesBefore + 2 * numOuterHashes + 3
          topRoot == x.copy.hash_tree_root()
      block:
        var x = HashList[Outer, 8].init(
          (0'u64 ..< 6'u64).mapIt(Outer(x: Inner(a: 100 + it), y: 500 + it)))
        discard x.hash_tree_root()
        x.mitem(0).y += 1
        let numHashesBefore = debugTotalSszHashes
        check:
          x.hash_tree_root([16.GeneralizedIndex], roots, topRoot).isOk
          debugTotalSszHashes == numHashesBefore + 2 * numOuterHashes + 4
          topRoot == x.copy.hash_tree_root()
      block:
        var x = HashSeq[Outer].init(
          (0'u64 ..< 6'u64).mapIt(Outer(x: Inner(a: 100 + it), y: 500 + it)))
        discard x.hash_tree_root()
        x.mitem(5).y += 1
        let numHashesBefore = debugTotalSszHashes
        check:
          x.hash_tree_root([88.GeneralizedIndex], roots, topRoot).isOk
          debugTotalSszHashes == numHashesBefore + 2 * numOuterHashes + 4
          topRoot == x.copy.hash_tree_root()
    else:
      skip()

  test "Caching across batches":
    when SSZ_DEBUG_COUNT_HASHES:
      block:
        let x = initTestArray()
        check x.hash_tree_root(2.GeneralizedIndex).isOk
        let numHashesBefore = debugTotalSszHashes
        check:
          x.hash_tree_root(2.GeneralizedIndex).isOk
          debugTotalSszHashes == numHashesBefore
      block:
        let x = HashSeq[uint64].init(toSeq(0'u64 ..< 21'u64))
        check x.hash_tree_root(5.GeneralizedIndex).isOk
        let numHashesBefore = debugTotalSszHashes
        check:
          x.hash_tree_root(5.GeneralizedIndex).isOk
          debugTotalSszHashes == numHashesBefore
      block:
        let x = HashList[uint64, 128].init(toSeq(0'u64 ..< 9'u64))
        check x.hash_tree_root([16.GeneralizedIndex, 17]).isOk
        let numHashesBefore = debugTotalSszHashes
        check:
          x.hash_tree_root([16.GeneralizedIndex, 17]).isOk
          debugTotalSszHashes == numHashesBefore
    else:
      skip()

  test "Top hash_tree_root uses partial cache":
    when SSZ_DEBUG_COUNT_HASHES:
      let
        x = HashSeq[uint64].init(toSeq(0'u64 ..< 21'u64))
        numHashesBefore = debugTotalSszHashes
      discard x.copy.hash_tree_root()
      let numHashes = debugTotalSszHashes - numHashesBefore
      check x.hash_tree_root(5.GeneralizedIndex).isOk
      discard x.hash_tree_root()
      check debugTotalSszHashes == numHashesBefore + 2 * numHashes
    else:
      skip()

  test "Progressive item root reuse":
    when SSZ_DEBUG_COUNT_HASHES:
      var x: HashSeq[Outer]
      for e in 0'u64 ..< 6'u64:
        doAssert x.add Outer(x: Inner(a: 100 + e), y: 500 + e)
      discard x.hash_tree_root()
      var roots {.noinit.}: array[2, Digest]
      for (i, numHashes) in [
          (9.GeneralizedIndex, 0'u64),
          (32.GeneralizedIndex, 0'u64),
          (81.GeneralizedIndex, 0'u64),
          (88.GeneralizedIndex, 0'u64),
          (40.GeneralizedIndex, numOuterHashes),
          (80.GeneralizedIndex, numInnerHashes)]:
        let numHashesBefore = debugTotalSszHashes
        check:
          x.hash_tree_root([4.GeneralizedIndex, i], roots).isOk
          debugTotalSszHashes == numHashesBefore + numHashes
          roots[0] == x.data[0].hash_tree_root()
    else:
      skip()

  test "Empty lists":
    let
      implicit = default(HashList[uint64, 128])
      explicit = HashList[uint64, 128].init(newSeq[uint64]())
      uncached = default(List[uint64, 128])

      emptyBits = BitList[100].init(0)
      bigBits = BitList[3000].init(0)
      implicitBigBits = default(BitList[3000])
      emptyBitSeq = BitSeq.init(0)

      cachedSeq = default(HashSeq[uint64])
      uncachedSeq = newSeq[uint64]()
    var
      roots {.noinit.}: array[2, Digest]
      topRoot {.noinit.}: Digest

    when SSZ_DEBUG_COUNT_HASHES:
      let numHashesBefore = debugTotalSszHashes

    check:
      implicit.hash_tree_root() == uncached.hash_tree_root()
      explicit.hash_tree_root() == uncached.hash_tree_root()
      cachedSeq.hash_tree_root() == uncachedSeq.hash_tree_root()

      implicit.hash_tree_root(1.GeneralizedIndex).get ==
        uncached.hash_tree_root()
      implicit.hash_tree_root([2.GeneralizedIndex, 9]) ==
        uncached.hash_tree_root([2.GeneralizedIndex, 9])

      emptyBits.hash_tree_root() == zeroHashes[1]
      bigBits.hash_tree_root() ==
        [zeroHashes[4], zeroHashes[0]].hash_tree_root()
      implicitBigBits.hash_tree_root([2.GeneralizedIndex, 3]) ==
        bigBits.hash_tree_root([2.GeneralizedIndex, 3])
      emptyBitSeq.hash_tree_root() == zeroHashes[1]

      cachedSeq.hash_tree_root([2.GeneralizedIndex, 3], roots, topRoot).isOk
      topRoot == uncachedSeq.hash_tree_root()

    when SSZ_DEBUG_COUNT_HASHES:
      check debugTotalSszHashes == numHashesBefore + 1
