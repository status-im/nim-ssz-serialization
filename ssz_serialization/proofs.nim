# ssz_serialization
# Copyright (c) 2018-2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  std/[algorithm, enumutils, macros, sequtils, sets, tables],
  results,
  stew/[bitops2, objects],
  serialization/case_objects,
  "."/[codec, digest, merkleization]

export digest, merkleization

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/specs/altair/light-client/sync-protocol.md#get_subtree_index
func get_subtree_index*(idx: GeneralizedIndex): uint64 =
  doAssert idx > 0
  uint64(idx mod (type(idx)(1) shl log2trunc(idx)))

# https://github.com/ethereum/consensus-specs/blob/v1.6.0-alpha.4/ssz/merkle-proofs.md#concat_generalized_indices
func concat_generalized_indices*(
    indices: varargs[GeneralizedIndex]): GeneralizedIndex =
  ## Given generalized indices i1 for A -> B, i2 for B -> C .... i_n for Y -> Z,
  ## returns the generalized index for A -> Z.
  result = 1.GeneralizedIndex
  for i in indices:
    let depth = log2trunc(i)
    result = (result shl depth) + i - (1.GeneralizedIndex shl depth)

template `&`*(a, b: GeneralizedIndex): GeneralizedIndex =
  concat_generalized_indices(a, b)

func `&=`*(a: var GeneralizedIndex, b: GeneralizedIndex) =
  a = a & b

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#generalized_index_sibling
template generalized_index_sibling*(
    index: GeneralizedIndex): GeneralizedIndex =
  index xor 1.GeneralizedIndex

template generalized_index_sibling_left*(
    index: GeneralizedIndex): GeneralizedIndex =
  index and not 1.GeneralizedIndex

template generalized_index_sibling_right*(
    index: GeneralizedIndex): GeneralizedIndex =
  index or 1.GeneralizedIndex

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#generalized_index_parent
template generalized_index_parent*(
    index: GeneralizedIndex): GeneralizedIndex =
  index shr 1

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#merkle-multiproofs
iterator get_branch_indices*(
    tree_index: GeneralizedIndex): GeneralizedIndex =
  ## Get the generalized indices of the sister chunks along the path
  ## from the chunk with the given tree index to the root.
  var index = tree_index
  while index > 1.GeneralizedIndex:
    yield generalized_index_sibling(index)
    index = generalized_index_parent(index)

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#merkle-multiproofs
iterator get_path_indices*(
    tree_index: GeneralizedIndex): GeneralizedIndex =
  ## Get the generalized indices of the chunks along the path
  ## from the chunk with the given tree index to the root.
  var index = tree_index
  while index > 1.GeneralizedIndex:
    yield index
    index = generalized_index_parent(index)

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#merkle-multiproofs
func get_helper_indices_impl(
    withPathIndices: static bool,
    indices: openArray[GeneralizedIndex],
    extra_indices: openArray[GeneralizedIndex] = []): seq[GeneralizedIndex] =
  ## Get the generalized indices of all "extra" chunks in the tree needed
  ## to prove the chunks with the given generalized indices. Note that the
  ## decreasing order is chosen deliberately to ensure equivalence to the order
  ## of hashes in a regular single-item Merkle proof in the single-item case.
  var all_helper_indices = initHashSet[GeneralizedIndex]()
  for index in indices:
    for idx in get_branch_indices(index):
      all_helper_indices.incl idx
  when not withPathIndices:
    for index in indices:
      for idx in get_path_indices(index):
        all_helper_indices.excl idx
  for idx in extra_indices:
    all_helper_indices.incl idx

  var res = newSeqOfCap[GeneralizedIndex](all_helper_indices.len)
  for idx in all_helper_indices.items():
    res.add idx
  res.sort(SortOrder.Descending)
  res

template get_helper_indices*(
    indices: varargs[GeneralizedIndex]): seq[GeneralizedIndex] =
  get_helper_indices_impl(withPathIndices = false, indices)

template get_union_indices*(
    indices: varargs[GeneralizedIndex]): seq[GeneralizedIndex] =
  get_helper_indices_impl(withPathIndices = true, indices)

template get_union_indices*(
    indices: openArray[GeneralizedIndex],
    extra_indices: openArray[GeneralizedIndex]): seq[GeneralizedIndex] =
  get_helper_indices_impl(withPathIndices = true, indices, extra_indices)

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#merkle-multiproofs
func check_multiproof_acceptable*(
    indices: varargs[GeneralizedIndex]): Result[void, string] =
  # Check that proof verification won't allocate excessive amounts of memory.
  const max_multiproof_complexity = nextPow2(256'u64).int
  if indices.len > max_multiproof_complexity:
    return err("Unsupported multiproof complexity (" & $indices.len & ")")

  if indices.len == 0:
    return err("No indices specified")
  if indices.anyIt(it <= 0.GeneralizedIndex):
    return err("Invalid index specified")
  ok()

func calculate_multi_merkle_root_impl(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex],
    helper_indices: openArray[GeneralizedIndex]): Result[Digest, string] =
  # All callers have already verified the checks in check_multiproof_acceptable,
  # as well as whether lengths of leaves/indices and proof/helper_indices match.

  # Helper to retrieve a value from a table that is statically known to exist.
  template getExisting[A, B](t: var Table[A, B], key: A): var B =
    try: t[key]
    except KeyError: raiseAssert "Unreachable"
  template popExisting[A, B](t: var Table[A, B], key: A): var B =
    var tmp {.noinit.}: Digest
    doAssert t.pop(key, tmp)
    tmp

  # Populate data structure with all leaves.
  # This data structure only scales with the number of `leaves`,
  # in contrast to the spec one that also scales with the number of `proof`
  # items and the number of all intermediate roots, potentially the entire tree.
  let capacity = nextPow2(leaves.len.uint64).int
  var objects = initTable[GeneralizedIndex, Digest](capacity)
  for i, index in indices:
    if objects.mgetOrPut(index, leaves[i]) != leaves[i]:
      return err("Conflicting roots for same index")

  # Create list with keys of all active nodes that need to be visited.
  # This list is sorted in descending order, same as `helper_indices`.
  # Pulling from `objects` instead of from `indices` deduplicates the list.
  var keys = newSeqOfCap[GeneralizedIndex](objects.len)
  for index in objects.keys:
    if index > 1.GeneralizedIndex: # For the root, no work needs to be done.
      keys.add index
  keys.sort(SortOrder.Descending)

  # The Merkle tree is processed from bottom to top, pulling in helper
  # indices from `proof` as needed. Keys need to be processed in descending
  # order to ensure that intermediate roots remain available until they are no
  # longer needed, ensuring that conflicting roots are detected in all cases.
  # During processing, parent items above the `keys` are temporarily split into
  # a separate list, also sorted descending, and processed in parallel.
  var
    parents = newSeqOfCap[GeneralizedIndex](keys.len)
    completedKeys = 0     # All key indices before this are fully processed.
    completedParents = 0  # All parent indices before this are fully processed.
    helper = 0            # Helper index from `proof` to be pulled next.

  # Processing is done when there are no more keys or parents to process.
  while completedKeys < keys.len or completedParents < parents.len:
    if completedParents == parents.len:
      parents.setLen(0)
      completedParents = 0
    if completedParents == keys.len:
      parents.delete(0 .. keys.high)
      completedParents = 0

    let
      k =
        if completedParents >= parents.len:
          inc completedKeys
          keys[completedKeys - 1]
        elif completedKeys >= keys.len:
          inc completedParents
          parents[completedParents - 1]
        elif keys[completedKeys] > parents[completedParents]:
          inc completedKeys
          keys[completedKeys - 1]
        else:
          inc completedParents
          parents[completedParents - 1]
      sibling = generalized_index_sibling(k)
      left = generalized_index_sibling_left(k)
      right = generalized_index_sibling_right(k)
      parent = generalized_index_parent(k)

    # A previous computation may have already merged this key with its sibling.
    if objects.hasKey(k):
      # Compute expected root for parent. This deletes child roots. Because
      # the keys are processed in descending order, they are no longer needed.
      let root =
        if helper < helper_indices.len and helper_indices[helper] == sibling:
          # The next proof item is required to form the parent hash.
          let h = helper
          inc(helper)
          if sibling == left:
            digest(proof[h].data, objects.popExisting(right).data)
          else:
            digest(objects.popExisting(left).data, proof[h].data)
        else:
          # Both siblings are already known.
          digest(
            objects.popExisting(left).data,
            objects.popExisting(right).data)

      # Store parent root, and queue the parent for processing.
      if objects.hasKeyOrPut(parent, root):
        if objects.getExisting(parent) != root:
          return err("Conflicting roots for same index")
      elif parent > 1.GeneralizedIndex:
        parents.add parent

  # Proof is guaranteed to provide all info needed to reach the root.
  doAssert helper == helper_indices.len
  doAssert objects.len == 1
  ok(objects.getExisting(1.GeneralizedIndex))

func calculate_multi_merkle_root*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex],
    helper_indices: openArray[GeneralizedIndex]): Result[Digest, string] =
  doAssert proof.len == helper_indices.len
  if leaves.len != indices.len:
    return err("Length mismatch for leaves and indices")
  ? check_multiproof_acceptable(indices)
  calculate_multi_merkle_root_impl(leaves, proof, indices, helper_indices)

func calculate_multi_merkle_root*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex]): Result[Digest, string] =
  if leaves.len != indices.len:
    return err("Length mismatch for leaves and indices")
  ? check_multiproof_acceptable(indices)
  let helper_indices = get_helper_indices(indices)
  if proof.len != helper_indices.len:
    return err("Length mismatch for proof and helper indices")
  calculate_multi_merkle_root_impl(leaves, proof, indices, helper_indices)

func calculate_multi_merkle_root*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: static openArray[GeneralizedIndex]): Result[Digest, string] =
  const v = check_multiproof_acceptable(indices)
  when v.isErr:
    result.err(v.error)
  else:
    if leaves.len != indices.len:
      return err("Length mismatch for leaves and indices")
    const helper_indices = get_helper_indices(indices)
    if proof.len != helper_indices.len:
      return err("Length mismatch for proof and helper indices")
    calculate_multi_merkle_root_impl(leaves, proof, indices, helper_indices)

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#merkle-multiproofs
func verify_merkle_multiproof*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex],
    helper_indices: openArray[GeneralizedIndex],
    root: Digest): bool =
  let calc = calculate_multi_merkle_root(leaves, proof, indices, helper_indices)
  if calc.isErr:
    return false
  calc.get == root

func verify_merkle_multiproof*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex],
    root: Digest): bool =
  let calc = calculate_multi_merkle_root(leaves, proof, indices)
  if calc.isErr:
    return false
  calc.get == root

func verify_merkle_multiproof*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: static openArray[GeneralizedIndex],
    root: Digest): bool =
  let calc = calculate_multi_merkle_root(leaves, proof, indices)
  if calc.isErr:
    return false
  calc.get == root

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/tests/core/pyspec/eth_consensus_specs/test/helpers/merkle.py#L4-L21
func build_proof*(
    anchor: auto,
    indices: openArray[GeneralizedIndex],
    helper_indices: openArray[GeneralizedIndex],
    proof: var openArray[Digest]): Result[void, string] =
  doAssert proof.len == helper_indices.len
  ? check_multiproof_acceptable(indices)
  hash_tree_root(anchor, helper_indices, proof)

func build_proof*(
    anchor: auto,
    indices: openArray[GeneralizedIndex],
    proof: var openArray[Digest]): Result[void, string] =
  ? check_multiproof_acceptable(indices)
  let helper_indices = get_helper_indices(indices)
  doAssert proof.len == helper_indices.len
  hash_tree_root(anchor, helper_indices, proof)

func build_proof*(
    anchor: auto,
    indices: static openArray[GeneralizedIndex],
    proof: var openArray[Digest]): Result[void, string] =
  const v = check_multiproof_acceptable(indices)
  when v.isErr:
    result.err(v.error)
  else:
    const helper_indices = get_helper_indices(indices)
    doAssert proof.len == helper_indices.len
    hash_tree_root(anchor, helper_indices, proof)

func build_proof*(
    anchor: auto,
    index: GeneralizedIndex,
    proof: var openArray[Digest]): Result[void, string] =
  ? check_multiproof_acceptable(index)
  let helper_indices = get_helper_indices(index)
  doAssert proof.len == helper_indices.len
  hash_tree_root(anchor, helper_indices, proof)

func build_proof*(
    anchor: auto,
    index: static GeneralizedIndex,
    proof: var openArray[Digest]): Result[void, string] =
  const v = check_multiproof_acceptable(index)
  when v.isErr:
    result.err(v.error)
  else:
    const helper_indices = get_helper_indices(index)
    doAssert proof.len == helper_indices.len
    hash_tree_root(anchor, helper_indices, proof)

func build_proof*(
    anchor: auto,
    indices: openArray[GeneralizedIndex]
): Result[seq[Digest], string] =
  ? check_multiproof_acceptable(indices)
  let helper_indices = get_helper_indices(indices)
  hash_tree_root(anchor, helper_indices)

func build_proof*(
    anchor: auto,
    indices: static openArray[GeneralizedIndex]
): auto =
  const v = check_multiproof_acceptable(indices)
  when v.isErr:
    Result[array[0, Digest], string].err(v.error)
  else:
    const helper_indices = get_helper_indices(indices)
    hash_tree_root(anchor, helper_indices)

func build_proof*(
    anchor: auto,
    index: GeneralizedIndex
): Result[seq[Digest], string] =
  ? check_multiproof_acceptable(index)
  let helper_indices = get_helper_indices(index)
  hash_tree_root(anchor, helper_indices)

func build_proof*(
    anchor: auto,
    index: static GeneralizedIndex
): auto =
  const v = check_multiproof_acceptable(index)
  when v.isErr:
    Result[array[0, Digest], string].err(v.error)
  else:
    const helper_indices = get_helper_indices(index)
    hash_tree_root(anchor, helper_indices)

func extract_branch*(
    roots: openArray[Digest],
    union_indices: openArray[GeneralizedIndex],
    indices: openArray[GeneralizedIndex],
    branch: var openArray[Digest]): Result[void, string] =
  if roots.len != union_indices.len:
    return err("Length mismatch for roots and indices")
  if branch.len != indices.len:
    return err("Length mismatch for branch and indices")
  var j = 0
  for i, idx in indices:
    while j < union_indices.len and union_indices[j] > idx:
      inc j
    if j >= union_indices.len or union_indices[j] != idx:
      return err("Index not covered by union")
    branch[i] = roots[j]
  ok()

func extract_branch*(
    roots: openArray[Digest],
    union_indices: openArray[GeneralizedIndex],
    indices: openArray[GeneralizedIndex]): Result[seq[Digest], string] =
  var branch = newSeqUninit[Digest](indices.len)
  ? roots.extract_branch(union_indices, indices, branch)
  ok branch

func extract_branch*(
    roots: openArray[Digest],
    union_indices: openArray[GeneralizedIndex],
    indices: static openArray[GeneralizedIndex]): auto =
  type ResultType = Result[array[indices.len, Digest], string]
  var branch {.noinit.}: array[indices.len, Digest]
  roots.extract_branch(union_indices, indices, branch).isOkOr:
    return ResultType.err(error)
  ResultType.ok(branch)

func extract_branch*(
    roots: openArray[Digest],
    union_indices: openArray[GeneralizedIndex],
    index: GeneralizedIndex): Result[seq[Digest], string] =
  let indices = get_helper_indices(index)
  roots.extract_branch(union_indices, indices)

func extract_branch*(
    roots: openArray[Digest],
    union_indices: openArray[GeneralizedIndex],
    index: static GeneralizedIndex): auto =
  const indices = get_helper_indices(index)
  roots.extract_branch(union_indices, indices)

func extract_root*(
    roots: openArray[Digest],
    union_indices: openArray[GeneralizedIndex],
    index: GeneralizedIndex | static GeneralizedIndex): Result[Digest, string] =
  let branch = ? roots.extract_branch(union_indices, [index])
  doAssert branch.len == 1
  ok(branch[0])

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.6/specs/phase0/beacon-chain.md#compute_merkle_branch_root
func compute_merkle_branch_root*(
    leaf: Digest, branch: openArray[Digest],
    depth: int, index: uint64): Digest =
  ## Return the Merkle root obtained by hashing ``leaf`` at ``index``
  ## with ``branch``.
  var
    value = leaf
    buf: array[64, byte]

  for i in 0 ..< depth:
    if (index div (1'u64 shl i)) mod 2 != 0:
      buf[0..31] = branch[i].data
      buf[32..63] = value.data
    else:
      buf[0..31] = value.data
      buf[32..63] = branch[i].data
    value = digest(buf)
  value

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/specs/phase0/beacon-chain.md#is_valid_merkle_branch
func is_valid_merkle_branch*(
    leaf: Digest, branch: openArray[Digest],
    depth: int, index: uint64, root: Digest): bool =
  ## Check if ``leaf`` at ``index`` verifies against the Merkle ``root`` and
  ## ``branch``.
  if depth != branch.len:
    return false
  compute_merkle_branch_root(leaf, branch, depth, index) == root

# https://github.com/ethereum/consensus-specs/blob/v1.7.0-alpha.3/ssz/merkle-proofs.md#ssz-object-to-index
type
  SszSchemaRef = proc(): lent SszSchema {.noSideEffect, nimcall, raises: [].}

  SszSchemaKind {.pure.} = enum
    sszBasic
    sszArray
    sszList
    sszSeq
    sszUnion
    sszProgressiveObject
    sszObject
    sszProgressiveTuple
    sszTuple

  SszObjectField = object
    name: string
    gindex: GeneralizedIndex
    schema: SszSchemaRef

  SszTupleField = object
    gindex: GeneralizedIndex
    schema: SszSchemaRef

  SszUnionVariant = object
    selector: uint8
    schema: SszSchemaRef

  SszSchema = object
    case kind: SszSchemaKind
    of sszBasic:
      discard
    of sszArray, sszList, sszSeq:
      dataPerChunkExp: int
      maxLen, firstIdx: Limit
      elemSchema: SszSchemaRef
    of sszUnion:
      unionVariants: seq[SszUnionVariant]
    of sszProgressiveObject, sszObject:
      objectFields: seq[SszObjectField]
    of sszProgressiveTuple, sszTuple:
      tupleFields: seq[SszTupleField]

func indexForChunk(firstIdx: Limit, chunkIdx: Limit): GeneralizedIndex =
  firstIdx.GeneralizedIndex + chunkIdx.GeneralizedIndex

func progressiveIndexForChunk*(chunkIdx: Limit): GeneralizedIndex =
  var
    gindex = 1.GeneralizedIndex
    chunkIdx = chunkIdx
    depth = 0.Limit
  while true:
    let numChunks = 1.Limit shl depth
    if chunkIdx < numChunks:
      let firstIdx = (gindex shl (depth + 1)).Limit
      return firstIdx.indexForChunk(chunkIdx)
    gindex = (gindex shl 1) or 1
    chunkIdx -= numChunks
    depth += 2

func sszSchema(T: typedesc): lent SszSchema

func sszSchemaRef(T: typedesc): SszSchemaRef =
  const res: SszSchemaRef =
    func(): lent SszSchema {.nimcall.} =
      T.sszSchema
  res

const basicSchema = SszSchema(kind: sszBasic)

func sszSchema(T: typedesc): lent SszSchema =
  mixin toSszType, enumAllSerializedFields
  template S: untyped = typeof toSszType(declval T)
  when S is bool|char|UintN:
    return basicSchema
  else:
    const res = block:
      when S is BitArray:
        SszSchema(
          kind: sszArray, dataPerChunkExp: log2trunc(bitsPerChunk.uint64),
          maxLen: S.bits, firstIdx: S.bits.maxBitChunkIdx)
      elif S is BitList:
        SszSchema(
          kind: sszList, dataPerChunkExp: log2trunc(bitsPerChunk.uint64),
          maxLen: S.maxLen, firstIdx: S.maxLen.maxBitChunkIdx shl 1)
      elif S is array|HashArray:
        template E: untyped = typeof toSszType(declval ElemType(S))
        SszSchema(
          kind: sszArray, dataPerChunkExp: log2trunc(E.dataPerChunk.uint64),
          maxLen: S.len, firstIdx: E.maxChunkIdx(S.len),
          elemSchema: E.sszSchemaRef)
      elif S is List|HashList:
        template E: untyped = typeof toSszType(declval ElemType(S))
        SszSchema(
          kind: sszList, dataPerChunkExp: log2trunc(E.dataPerChunk.uint64),
          maxLen: S.maxLen, firstIdx: E.maxChunkIdx(S.maxLen) shl 1,
          elemSchema: E.sszSchemaRef)
      elif S is BitSeq:
        SszSchema(
          kind: sszSeq, dataPerChunkExp: log2trunc(bitsPerChunk.uint64))
      elif S is seq|HashSeq:
        template E: untyped = typeof toSszType(declval ElemType(S))
        SszSchema(
          kind: sszSeq, dataPerChunkExp: log2trunc(E.dataPerChunk.uint64),
          elemSchema: E.sszSchemaRef)
      elif S.isUnion:
        var variants: seq[SszUnionVariant]
        for selector in S.unionSelectorType.items():
          doAssert selector.int in 0 .. uint8.high.int
          let sample = S.doInit(S.unionSelectorKey, selector)
          var isSome = false
          sample.withFieldPairs(key, val):
            when key != S.unionSelectorKey:
              doAssert not isSome
              isSome = true
              variants.add SszUnionVariant(
                selector: selector.int.uint8,
                schema: sszSchemaRef(typeof(val)))
          if not isSome:
            variants.add SszUnionVariant(
              selector: selector.int.uint8)
        SszSchema(kind: sszUnion, unionVariants: variants)
      elif S is object|tuple:
        when S.isProgressiveContainer:
          const
            activeFields = S.activeFields
            totalChunks = activeFields.bitWidth
          var i = 0
        else:
          const
            totalChunks = T.totalSerializedFields
            firstIdx = nextPow2(totalChunks.uint64).Limit
        when S is object:
          var fields: seq[SszObjectField]
        else:
          var fields: seq[SszTupleField]
        var fieldIdx = 0
        S.enumAllSerializedFields:
          when S.isProgressiveContainer:
            while not activeFields[i]:
              inc i
          let gindex =
            when S.isProgressiveContainer:
              2.GeneralizedIndex & i.progressiveIndexForChunk
            else:
              firstIdx.indexForChunk(fieldIdx)
          when S is object:
            fields.add SszObjectField(
              name: fieldName,
              gindex: gindex,
              schema: sszSchemaRef(FieldType))
          else:
            fields.add SszTupleField(
              gindex: gindex,
              schema: sszSchemaRef(FieldType))
          inc fieldIdx
          when S.isProgressiveContainer:
            inc i
        when S.isProgressiveContainer:
          doAssert i == totalChunks
        else:
          doAssert fieldIdx == totalChunks
        when S is object:
          const kind =
            when S.isProgressiveContainer:
              sszProgressiveObject
            else:
              sszObject
          SszSchema(kind: kind, objectFields: fields)
        else:
          const kind =
            when S.isProgressiveContainer:
              sszProgressiveTuple
            else:
              sszTuple
          SszSchema(kind: kind, tupleFields: fields)
      else:
        unsupported S
    res

func gindex(schema: SszSchema, p: string): Result[GeneralizedIndex, string] =
  case schema.kind
  of sszBasic, sszArray, sszTuple:
    discard
  of sszList, sszSeq:
    if p == "__len__":
      return ok 3.GeneralizedIndex
  of sszUnion:
    if p == "__selector__":
      return ok 3.GeneralizedIndex
  of sszProgressiveObject, sszObject:
    if schema.kind == sszProgressiveObject and p == "__active_fields__":
      return ok 3.GeneralizedIndex
    for field in schema.objectFields:
      if field.name == p:
        return ok field.gindex
  of sszProgressiveTuple:
    if p == "__active_fields__":
      return ok 3.GeneralizedIndex
  err "Field '" & p & "' not found"

func schema(schema: SszSchema, p: string): lent SszSchema =
  case schema.kind
  of sszBasic, sszArray, sszList, sszSeq,
      sszUnion, sszProgressiveTuple, sszTuple:
    return basicSchema
  of sszProgressiveObject, sszObject:
    for field in schema.objectFields:
      if field.name == p:
        if field.schema != nil:
          return field.schema()
        break
    return basicSchema

func gindex(schema: SszSchema, p: Limit): Result[GeneralizedIndex, string] =
  case schema.kind
  of sszBasic, sszProgressiveObject, sszObject:
    discard
  of sszArray, sszList:
    if p in 0 ..< schema.maxLen:
      let chunkIdx = p shr schema.dataPerChunkExp
      return ok schema.firstIdx.indexForChunk(chunkIdx)
  of sszSeq:
    if p >= 0:
      let chunkIdx = p shr schema.dataPerChunkExp
      return ok(2.GeneralizedIndex & chunkIdx.progressiveIndexForChunk)
  of sszUnion:
    if p in 0.Limit .. uint8.high.Limit:
      for v in schema.unionVariants:
        if v.selector == p.uint8:
          return ok 2.GeneralizedIndex
  of sszProgressiveTuple, sszTuple:
    if p in 0.Limit ..< schema.tupleFields.len.Limit:
      return ok schema.tupleFields[p].gindex
  err "Index '" & $p & "' not supported"

func schema(schema: SszSchema, p: Limit): lent SszSchema =
  case schema.kind
  of sszBasic, sszProgressiveObject, sszObject:
    return basicSchema
  of sszArray, sszList, sszSeq:
    if schema.elemSchema != nil:
      return schema.elemSchema()
    return basicSchema
  of sszUnion:
    if p in 0.Limit .. uint8.high.Limit:
      for v in schema.unionVariants:
        if v.selector == p.uint8:
          if v.schema != nil:
            return v.schema()
          break
    return basicSchema
  of sszProgressiveTuple, sszTuple:
    if p in 0.Limit ..< schema.tupleFields.len.Limit:
      if schema.tupleFields[p].schema != nil:
        return schema.tupleFields[p].schema()
    return basicSchema

macro get_generalized_index_impl(T: typedesc, path: varargs[untyped]): untyped =
  if path.len == 0:
    return quote do:
      Result[GeneralizedIndex, string].ok(1.GeneralizedIndex)
  if path.len == 1:
    let firstP = path[0]
    return quote do:
      `T`.sszSchema.gindex(`firstP`)

  let
    res = nskVar.genSym "res"
    syms = (0 ..< path.len).mapIt (
      p: path[it],
      schema: nskLet.genSym "schema",
      gindex: nskLet.genSym "gindex")
    (firstP, firstSchema, firstGindex) = syms[0]
    (_, _, lastGindex) = syms[^1]
  var body = quote do:
    if `lastGindex`.isOk:
      Result[GeneralizedIndex, string].ok `res` & `lastGindex`.unsafeGet
    else:
      `lastGindex`
  for i in countdown(path.len - 1, 1):
    let
      (prevP, prevSchema, prevGindex) = syms[i - 1]
      (currP, currSchema, currGindex) = syms[i]
    body = quote do:
      if `prevGindex`.isOk:
        `res` &= `prevGindex`.unsafeGet
        let
          `currSchema` = `prevSchema`.schema(`prevP`)
          `currGindex` = `currSchema`.gindex(`currP`)
        `body`
      else:
        `prevGindex`
  quote do:
    block:
      var `res` = 1.GeneralizedIndex
      let
        `firstSchema` = `T`.sszSchema
        `firstGindex` = `firstSchema`.gindex(`firstP`)
      `body`

macro get_generalized_index*(T: typedesc, path: varargs[untyped]): untyped =
  ## Converts a path (eg. `[7, "foo", 3]` for `x[7].foo[3]`,
  ## `[12, "bar", "__len__"]` for `len(x[12].bar)`) into the generalized index
  ## representing its position in the Merkle tree.
  let impl = quote do:
    `T`.get_generalized_index_impl(`path`)
  quote do:
    when compiles(static(`impl`)):
      const res = `impl`
      when res.isErr:
        {.error: res.error.}
      res.unsafeGet
    else:
      `impl`
