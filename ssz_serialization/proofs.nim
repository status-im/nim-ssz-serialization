# ssz_serialization
# Copyright (c) 2018, 2021 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [Defect].}

import
  std/[algorithm, math, sequtils, sets, tables],
  stew/[bitops2, results],
  ./merkleization

export merkleization

type GeneralizedIndex* = uint64

# https://github.com/ethereum/consensus-specs/blob/v1.1.6/specs/altair/sync-protocol.md#get_subtree_index
func get_subtree_index*(idx: GeneralizedIndex): uint64 =
  doAssert idx > 0
  uint64(idx mod (type(idx)(1) shl log2trunc(idx)))

# https://github.com/ethereum/consensus-specs/blob/v1.1.6/ssz/merkle-proofs.md#generalized_index_sibling
template generalized_index_sibling*(
    index: GeneralizedIndex): GeneralizedIndex =
  index xor 1.GeneralizedIndex

template generalized_index_sibling_left(
    index: GeneralizedIndex): GeneralizedIndex =
  index and not 1.GeneralizedIndex

template generalized_index_sibling_right(
    index: GeneralizedIndex): GeneralizedIndex =
  index or 1.GeneralizedIndex

# https://github.com/ethereum/consensus-specs/blob/v1.1.6/ssz/merkle-proofs.md#generalized_index_parent
template generalized_index_parent*(
    index: GeneralizedIndex): GeneralizedIndex =
  index shr 1

# https://github.com/ethereum/consensus-specs/blob/v1.1.5/ssz/merkle-proofs.md#merkle-multiproofs
iterator get_branch_indices*(
    tree_index: GeneralizedIndex): GeneralizedIndex =
  ## Get the generalized indices of the sister chunks along the path
  ## from the chunk with the given tree index to the root.
  var index = tree_index
  while index > 1.GeneralizedIndex:
    yield generalized_index_sibling(index)
    index = generalized_index_parent(index)

# https://github.com/ethereum/consensus-specs/blob/v1.1.5/ssz/merkle-proofs.md#merkle-multiproofs
iterator get_path_indices*(
    tree_index: GeneralizedIndex): GeneralizedIndex =
  ## Get the generalized indices of the chunks along the path
  ## from the chunk with the given tree index to the root.
  var index = tree_index
  while index > 1.GeneralizedIndex:
    yield index
    index = generalized_index_parent(index)

# https://github.com/ethereum/consensus-specs/blob/v1.1.6/ssz/merkle-proofs.md#merkle-multiproofs
func get_helper_indices*(
    indices: openArray[GeneralizedIndex]): seq[GeneralizedIndex] =
  ## Get the generalized indices of all "extra" chunks in the tree needed
  ## to prove the chunks with the given generalized indices. Note that the
  ## decreasing order is chosen deliberately to ensure equivalence to the order
  ## of hashes in a regular single-item Merkle proof in the single-item case.
  var all_helper_indices = initHashSet[GeneralizedIndex]()
  for index in indices:
    for idx in get_branch_indices(index):
      all_helper_indices.incl idx
  for index in indices:
    for idx in get_path_indices(index):
      all_helper_indices.excl idx

  var res = newSeqOfCap[GeneralizedIndex](all_helper_indices.len)
  for idx in all_helper_indices:
    res.add idx
  res.sort(SortOrder.Descending)
  res

# https://github.com/ethereum/consensus-specs/blob/v1.1.5/ssz/merkle-proofs.md#merkle-multiproofs
func check_multiproof_acceptable*(
    indices: openArray[GeneralizedIndex]): Result[void, string] =
  # Check that proof verification won't allocate excessive amounts of memory.
  const max_multiproof_complexity = nextPowerOfTwo(256)
  if indices.len > max_multiproof_complexity:
    return err("Unsupported multiproof complexity (" & $indices.len & ")")

  if indices.len == 0:
    return err("No indices specified")
  if indices.anyIt(it == 0.GeneralizedIndex):
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

  # Populate data structure with all leaves.
  # This data structure only scales with the number of `leaves`,
  # in contrast to the spec one that also scales with the number of `proof`
  # items and the number of all intermediate roots, potentially the entire tree.
  let capacity = nextPowerOfTwo(leaves.len)
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

  # The merkle tree is processed from bottom to top, pulling in helper
  # indices from `proof` as needed. During processing, the `keys` list
  # may temporarily end up being split into two parts, sorted individually.
  # An additional index tracks the current maximum element of the list.
  var
    completed = 0         # All key indices before this are fully processed.
    maxIndex = completed  # Index of the list's largest key.
    helper = 0            # Helper index from `proof` to be pulled next.

  # Processing is done when there are no more keys to process.
  while completed < keys.len:
    let
      k = keys[maxIndex]
      sibling = generalized_index_sibling(k)
      left = generalized_index_sibling_left(k)
      right = generalized_index_sibling_right(k)
      parent = generalized_index_parent(k)
      parentRight = generalized_index_sibling_right(parent)

    # Keys need to be processed in descending order to ensure that intermediate
    # roots remain available until they are no longer needed. This ensures that
    # conflicting roots are detected in all cases.
    keys[maxIndex] =
      if not objects.hasKey(k):
        # A previous computation did already merge this key with its sibling.
        0.GeneralizedIndex
      else:
        # Compute expected root for parent. This deletes child roots.
        # Because the list is sorted in descending order, they are not needed.
        let root = computeDigest:
          if helper < helper_indices.len and helper_indices[helper] == sibling:
            # The next proof item is required to form the parent hash.
            if sibling == left:
              h.update proof[helper].data
              h.update objects.getExisting(right).data; objects.del right
            else:
              h.update objects.getExisting(left).data;  objects.del left
              h.update proof[helper].data
            inc helper
          else:
            # Both siblings are already known.
            h.update objects.getExisting(left).data;  objects.del left
            h.update objects.getExisting(right).data; objects.del right

        # Store parent root, and replace the current list entry with its parent.
        if objects.hasKeyOrPut(parent, root):
          if objects.getExisting(parent) != root:
            return err("Conflicting roots for same index")
          0.GeneralizedIndex
        elif parent > 1.GeneralizedIndex:
          # Note that the list may contain further nodes that are on a layer
          # beneath the parent, so this may break the strictly descending order
          # of the list. For example, given [12, 9], this will lead to [6, 9].
          # This will resolve itself after the additional nodes are processed,
          # i.e., [6, 9] -> [6, 4] -> [3, 4] -> [3, 2] -> [1].
          parent
        else:
          0.GeneralizedIndex
    if keys[maxIndex] != 0.GeneralizedIndex:
      # The list may have been temporarily split up into two parts that are
      # individually sorted in descending order. Have to first process further
      # nodes until the list is sorted once more.
      inc maxIndex

    # Determine whether descending sort order has been restored.
    let isSorted =
      if maxIndex == completed: true
      else:
        while maxIndex < keys.len and keys[maxIndex] == 0.GeneralizedIndex:
          inc maxIndex
        maxIndex >= keys.len or keys[maxIndex] <= parentRight
    if isSorted:
      # List is sorted once more. Reset `maxIndex` to its start.
      while completed < keys.len and keys[completed] == 0.GeneralizedIndex:
        inc completed
      maxIndex = completed

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
  calculate_multi_merkle_root_impl(
    leaves, proof, indices, helper_indices)

func calculate_multi_merkle_root*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex]): Result[Digest, string] =
  if leaves.len != indices.len:
    return err("Length mismatch for leaves and indices")
  ? check_multiproof_acceptable(indices)
  calculate_multi_merkle_root_impl(
    leaves, proof, indices, get_helper_indices(indices))

# https://github.com/ethereum/consensus-specs/blob/v1.1.6/ssz/merkle-proofs.md#merkle-multiproofs
func verify_merkle_multiproof*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex],
    helper_indices: openArray[GeneralizedIndex],
    root: Digest): bool =
  let calc = calculate_multi_merkle_root(leaves, proof, indices, helper_indices)
  if calc.isErr: return false
  calc.get == root

func verify_merkle_multiproof*(
    leaves: openArray[Digest],
    proof: openArray[Digest],
    indices: openArray[GeneralizedIndex],
    root: Digest): bool =
  let calc = calculate_multi_merkle_root(leaves, proof, indices)
  if calc.isErr: return false
  calc.get == root

# https://github.com/ethereum/consensus-specs/blob/v1.1.6/specs/phase0/beacon-chain.md#is_valid_merkle_branch
func is_valid_merkle_branch*(leaf: Digest, branch: openArray[Digest],
                             depth: int, index: uint64,
                             root: Digest): bool =
  ## Check if ``leaf`` at ``index`` verifies against the Merkle ``root`` and
  ## ``branch``.
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
  value == root

# https://github.com/ethereum/consensus-specs/blob/v1.1.6/tests/core/pyspec/eth2spec/test/helpers/merkle.py#L4-L21
func build_proof_impl(anchor: object, leaf_index: uint64,
                      proof: var openArray[Digest]) =
  let
    bottom_length = nextPow2(typeof(anchor).totalSerializedFields.uint64)
    tree_depth = log2trunc(bottom_length)
    parent_index =
      if leaf_index < bottom_length shl 1:
        0'u64
      else:
        var i = leaf_index
        while i >= bottom_length shl 1:
          i = i shr 1
        i

  var
    prefix_len = 0
    proof_len = log2trunc(leaf_index)
    cache = newSeq[Digest](bottom_length shl 1)
  block:
    var i = bottom_length
    anchor.enumInstanceSerializedFields(fieldNameVar, fieldVar):
      if i == parent_index:
        when fieldVar is object:
          prefix_len = log2trunc(leaf_index) - tree_depth
          proof_len -= prefix_len
          let
            bottom_bits = leaf_index and not (uint64.high shl prefix_len)
            prefix_leaf_index = (1'u64 shl prefix_len) + bottom_bits
          build_proof_impl(fieldVar, prefix_leaf_index, proof)
        else: raiseAssert "Invalid leaf_index"
      cache[i] = hash_tree_root(fieldVar)
      i += 1
    for i in countdown(bottom_length - 1, 1):
      cache[i] = computeDigest:
        h.update cache[i shl 1].data
        h.update cache[i shl 1 + 1].data

  var i = if parent_index != 0: parent_index
          else: leaf_index
  doAssert i > 0 and i < bottom_length shl 1
  for proof_index in prefix_len ..< prefix_len + proof_len:
    let b = (i and 1) != 0
    i = i shr 1
    proof[proof_index] = if b: cache[i shl 1]
                         else: cache[i shl 1 + 1]

func build_proof*(anchor: object, leaf_index: uint64,
                  proof: var openArray[Digest]) =
  doAssert leaf_index > 0
  doAssert proof.len == log2trunc(leaf_index)
  build_proof_impl(anchor, leaf_index, proof)
