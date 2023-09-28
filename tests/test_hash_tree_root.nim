{.used.}

import
  ../ssz_serialization/merkleization

type
  Eth2Digest = object
    data: array[32, byte]

  ExecutionAddress = object
    data: array[20, byte]

  BloomLogs = object
    data: array[256, byte]

  UInt256 = object
    data: array[32, byte]

  ExecutionPayload* = object
    # Execution block header fields
    parent_hash*: Eth2Digest
    fee_recipient*: ExecutionAddress
      ## 'beneficiary' in the yellow paper
    state_root*: Eth2Digest
    receipts_root*: Eth2Digest
    logs_bloom*: BloomLogs
    prev_randao*: Eth2Digest
      ## 'difficulty' in the yellow paper
    block_number*: uint64
      ## 'number' in the yellow paper
    gas_limit*: uint64
    gas_used*: uint64
    timestamp*: uint64
    extra_data*: List[byte, 32]
    base_fee_per_gas*: UInt256

    # Extra payload fields
    block_hash*: Eth2Digest
      ## Hash of execution block

proc main() =
  var h: ExecutionPayload
  # under nim 1.6.12, hash_tree_root failed to compile
  # but the bug fixed in nim > 1.6.14
  let z {.used.} = hash_tree_root(h)

main()
