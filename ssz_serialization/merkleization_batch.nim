# ssz_serialization
# Copyright (c) 2018-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  std/algorithm,
  results,
  stew/byteutils,
  ./types

type
  BatchIndexRef = uint8
    ## Refers to an individual entry within `DynamicBatchRequest.indices`,
    ## and implies maximum number of indices that can be queried at a time.

  BatchRequest*[Q: static[int]] = object
    when Q > 0:
      indices*: array[Q, GeneralizedIndex]
        ## Up through `BatchIndexRef.high` entries that each contain a
        ## `GeneralizedIndex` for which the corresponding `Digest` is queried.
      loopOrder*: array[2 * Q, BatchIndexRef]
        ## Order in which `indices` will be visited while fulfilling queries.
        ## Refers to index of indices, e.g., `indices[loopOrder[i]]` for access.
    elif Q == -1:
      indices*: seq[GeneralizedIndex]
        ## Up through `BatchIndexRef.high` entries that each contain a
        ## `GeneralizedIndex` for which the corresponding `Digest` is queried.
      loopOrder*: seq[BatchIndexRef]
        ## Order in which `indices` will be visited while fulfilling queries.
        ## Refers to index of indices, e.g., `indices[loopOrder[i]]` for access.

func merkleizationCmp(x, y: tuple[idx: GeneralizedIndex, down: bool]): int =
  # GeneralizedIndex is 1-based.
  # Looking at their bit patterns, from MSB to LSB, they:
  # - Start with a 1 bit.
  # - Continue with a 0 bit when going left or 1 bit when going right,
  #   from the tree root down to the leaf.
  # e.g., 0b1_110 is the node after picking right branch twice, then left.
  #
  #     1      Order: Parent -> Left -> Right -> Parent (each idx emitted twice)
  #    / \     - Left/Right must be available to compute Parent (post-order).
  #   2   3    - Parent must be available to know covered leaves (pre-order);
  #  / \         `enumAllSerializedFields` requires disjunct requests to be
  # 4   5        served left to right, so we cannot simply use ^1 of post-order.
  let xBeforeY =
    if x.idx == y.idx:
      x.down  # First go down then up
    else:
      let
        xZeros = x.idx.leadingZeros()
        yZeros = y.idx.leadingZeros()
      if xZeros == yZeros:  # Same layer
        x < y
      elif xZeros < yZeros:  # `x` deeper than `y`
        let xAtLayerOfY = (x.idx shr (yZeros - xZeros))
        if xAtLayerOfY != y.idx:
          # No shared ancestry
          xAtLayerOfY < y.idx
        elif x.down != y.down:
          # `x` descends from `y` -> going down has priority
          x.down
        elif x.down:
          # `x` descends from `y` and going down --> parent before children
          false
        else:
          # `x` descends from `y` and going up --> children before parent
          true
      else:  # `y` deeper than `x`
        let yAtLayerOfX = (y.idx shr (xZeros - yZeros))
        if yAtLayerOfX != x.idx:
          # No shared ancestry
          x.idx < yAtLayerOfX
        elif x.down != y.down:
          # `y` descends from `x` -> going down has priority
          x.down
        elif x.down:
          # `y` descends from `x` and going down --> parent before children
          true
        else:
          # `y` descends from `x` and going up --> children before parent
          false
  if xBeforeY:
    -1
  else:
    1

func computeMerkleizationLoopOrder(
    indices: auto,
    loopOrder: var openArray[BatchIndexRef],
    sortOrder: var openArray[tuple[i: BatchIndexRef, down: bool]]) =
  for i in 0 ..< indices.len:
    sortOrder[2 * i + 0] = (i: i.BatchIndexRef, down: true)
    sortOrder[2 * i + 1] = (i: i.BatchIndexRef, down: false)
  sortOrder.sort do (x, y: auto) -> int:
    merkleizationCmp(
      (idx: indices[x.i], down: x.down),
      (idx: indices[y.i], down: y.down))
  for i in 0 ..< sortOrder.len:
    loopOrder[i] = sortOrder[i].i

func init*[N](
    T: typedesc[BatchRequest],
    indices: static array[N, GeneralizedIndex]): T {.compileTime.} =
  const Q = indices.len
  doAssert Q < BatchIndexRef.high.int, "Too many indices requested in one batch"
  var
    loopOrder: array[2 * Q, BatchIndexRef]
    sortOrder: array[2 * Q, tuple[i: BatchIndexRef, down: bool]]
  indices.computeMerkleizationLoopOrder(loopOrder, sortOrder)
  T[Q](indices: indices, loopOrder: loopOrder)

func init*(
    T: typedesc[BatchRequest],
    indices: seq[GeneralizedIndex]): Result[BatchRequest[-1], string] =
  if indices.len >= BatchIndexRef.high.int:
    return err("Too many indices requested in one batch")
  var
    loopOrder = newSeq[BatchIndexRef](2 * indices.len)
    sortOrder = newSeq[tuple[i: BatchIndexRef, down: bool]](2 * indices.len)
  indices.computeMerkleizationLoopOrder(loopOrder, sortOrder)
  ok T[-1](indices: indices, loopOrder: loopOrder)

template BatchResult(Q: static[int]): typedesc =
  # List of `Digest` items corresponding to requested `indices`.
  when Q > 0:
    typedesc[array[Q, Digest]]
  elif Q == -1:
    typedesc[seq[Digest]]
  else:
    typedesc[void]

type BatchQuery*[Q: static[int]] = object
  ## State for fulfilling auxiliary `GeneralizedIndex` queries.
  when Q != 0:
    req: BatchRequest[Q]
      ## Readonly / potentially statically computable request.
    roots: ptr BatchResult(Q)
      ## Writeonly result with correct length allocated by constructor.
    pos: int
      ## `query.loopOrder[pos]` is the current query being processed.
    pivot: GeneralizedIndex
      ## Top level `GeneralizedIndex` of current disjunct subtree.
    atLayer: int
      ## Global layer at which we currently are.

func init*[Q: static[int]](
    T: typedesc[BatchQuery],
    req: BatchRequest[Q],
    roots: ptr #[BatchResult(Q)]#): T =
  T[Q](req: req, roots: roots)

func init*[N](
    T: typedesc[BatchQuery],
    indices: static array[N, GeneralizedIndex],
    roots: ptr array[N, Digest]): T =
  const
    Q = indices.len
    req = BatchRequest.init(indices)
  T.init(req, roots)

func init*(
    T: typedesc[BatchQuery],
    indices: seq[GeneralizedIndex],
    roots: ptr seq[Digest]): Result[T, string] =
  let req = BatchRequest.init(indices)
  T.init(req, roots)

func `[]=`*(batch: BatchQuery, gindex: GeneralizedIndex, root: Digest) =
  debugEcho "----> [", $gindex, "] = ", $toHex(root.data)
