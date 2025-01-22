# ssz_serialization
# Copyright (c) 2018-2025 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  std/[algorithm, sequtils],
  results,
  stew/[bitops2, evalonce, ptrops],
  ./types

type
  BatchRequestId = uint8

  BatchRequest* = object
    len*: int
    indicesSeq: seq[GeneralizedIndex]
    indicesBase: ptr UncheckedArray[GeneralizedIndex]
    loopOrder*: seq[BatchRequestId]

template indices*(requestParam: BatchRequest): openArray[GeneralizedIndex] =
  block:
    debugecho "indices called"
    requestParam.evalOnceAs(request)
    debugecho $request
    # when request.vm:
    #   request.indicesSeq
    # else:
    #   request.indicesBase.toOpenArray(0, request.len - 1)
    [1,2,3,4,5,6,7,8,9,0]

template normalize(v: GeneralizedIndex): GeneralizedIndex =
  # GeneralizedIndex is 1-based.
  # Looking at their bit patterns, from MSB to LSB, they:
  # - Start with a 1 bit.
  # - Continue with a 0 bit when going left or 1 bit when going right,
  #   from the tree root down to the leaf.
  # i.e., 0b1_110 is the node after picking right branch twice, then left.
  #
  # For depth-first ordering, shorter bit-strings are parents of nodes
  # that include them as their prefix.
  # i.e., 0b1_110 is parent of 0b1_1100 (left) and 0b1_1101 (right)
  # An extra 1 bit is added to distinguish parents from their left child.
  ((v shl 1) or 1) shl leadingZeros(v)

# Comparison utility for sorting indices in depth-first order (in-order).
# This order is needed because `enumInstanceSerializedFields` does not allow
# random access to specific fields. With depth-first order only a single pass
# is required to fill in all the roots. `enumAllSerializedFields` cannot be
# used for pre-computation at compile time, because the generalized indices
# depend on the specific case values defined by the specific object instance.
func cmpDepthFirst(x, y: GeneralizedIndex): int =
  cmp(x.normalize, y.normalize)

func merkleizationLoopOrder(
    indices: openArray[GeneralizedIndex]): Result[seq[BatchRequestId], string] =
  if indices.len >= BatchRequestId.high.int:
    return err "Too many generalized indices requested in one batch"

  var loopOrder = toSeq(0.BatchRequestId ..< indices.len.BatchRequestId)
  when nimvm:
    block:
      let idx = indices.toSeq()
      loopOrder.sort do (x, y: BatchRequestId) -> int:
        cmpDepthFirst(idx[x], idx[y])
  else:
    block:
      let idx = indices.baseAddr.makeUncheckedArray()
      loopOrder.sort do (x, y: BatchRequestId) -> int:
        cmpDepthFirst(idx[x], idx[y])

  if indices.len > 0:
    var prev = indices[loopOrder[0]]
    if prev < 1.GeneralizedIndex:
      return err "Invalid generalized index"
    var prevLayer = log2trunc(prev)
    for i in 1 .. loopOrder.high:
      let curr = indices[loopOrder[i]]
      if curr < 1.GeneralizedIndex:
        return err "Invalid generalized index"
      let
        currLayer = log2trunc(curr)
        indicesOverlap =
          if currLayer < prevLayer:
            (prev shr (prevLayer - currLayer)) == curr
          elif currLayer > prevLayer:
            (curr shr (currLayer - prevLayer)) == prev
          else:
            curr == prev
      if indicesOverlap:
        return err "Given indices cover some leafs multiple times"
      prev = curr
      prevLayer = currLayer

  ok loopOrder

func init*(
    T: typedesc[BatchRequest],
    indices: openArray[GeneralizedIndex]
): Result[BatchRequest, string] =
  # let res = BatchRequest[false](
  #   len: indices.len,
  #   indicesBase: indices.baseAddr.makeUncheckedArray(),
  #   loopOrder: ? indices.merkleizationLoopOrder)
  # ok res  # https://github.com/arnetheduck/nim-results/issues/52
  err "not supported"

func init*(
    T: typedesc[BatchRequest],
    indices: static openArray[GeneralizedIndex]
): Result[BatchRequest, string] {.compileTime.} =
  # const res = BatchRequest(
  #   # len: indices.len,
  #   # indicesSeq: toSeq(indices),
  #   # loopOrder: ? indices.merkleizationLoopOrder
  #   )
  # ok res  # https://github.com/arnetheduck/nim-results/issues/52
  err "no"

func afafa*(indices: static openArray[GeneralizedIndex]): string {.compileTime.} =
  # const res = BatchRequest(
  #   # len: indices.len,
  #   # indicesSeq: toSeq(indices),
  #   # loopOrder: ? indices.merkleizationLoopOrder
  #   )
  # ok res  # https://github.com/arnetheduck/nim-results/issues/52
  "afafa"
