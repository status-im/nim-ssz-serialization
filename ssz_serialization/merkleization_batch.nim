# ssz_serialization
# Copyright (c) 2018-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.push raises: [].}

import
  stew/byteutils,
  ./types

type
  BatchIndexRef = uint8
    ## Refers to an individual entry within `DynamicBatchRequest.indices`,
    ## and implies maximum number of indices that can be queried at a time.

  BatchRequest[Q: static[int]] = object
    when Q > 0:
      indices: array[Q, GeneralizedIndex]
        ## Up through `BatchIndexRef.high` entries that each contain a
        ## `GeneralizedIndex` for which the corresponding `Digest` is queried.
      loopOrder: array[2 * Q, BatchIndexRef]
        ## Order in which `indices` will be visited while fulfilling queries.
        ## Refers to index of indices, e.g., `indices[loopOrder[i]]` for access.
    elif Q != 0:
      indices: seq[GeneralizedIndex]
        ## Up through `BatchIndexRef.high` entries that each contain a
        ## `GeneralizedIndex` for which the corresponding `Digest` is queried.
      loopOrder: seq[BatchIndexRef]
        ## Order in which `indices` will be visited while fulfilling queries.
        ## Refers to index of indices, e.g., `indices[loopOrder[i]]` for access.
    else:
      discard

template BatchResult(Q: static[int]): typedesc =
  # List of `Digest` items corresponding to requested `indices`.
  when Q > 0:
    array[Q, Digest]
  elif Q != 0:
    seq[Digest]
  else:
    void

type BatchQuery*[Q: static[int]] = object
  ## State for fulfilling auxiliary `GeneralizedIndex` queries.
  when Q != 0:
    query: ref BatchRequest[Q]
    res: ref BatchResult(Q)
    pos: int
      # `query.loopOrder[pos]` is the current query being processed.
    atLayer: int

func `[]=`*(batch: BatchQuery, gindex: GeneralizedIndex, root: Digest) =
  debugEcho "----> [", $gindex, "] = ", $toHex(root.data)
