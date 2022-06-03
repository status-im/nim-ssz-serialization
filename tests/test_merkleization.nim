# ssz_serialization
# Copyright (c) 2021-2022 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  std/sequtils,
  unittest2,
  stew/endians2,
  ../ssz_serialization/merkleization

func h(a, b: openArray[byte]): seq[byte] =
  let digest =
    computeDigest:
      h.update a
      h.update b

  digest.data.toSeq()

func e(v: uint32): seq[byte] =
  let elem: uint8 = 255
  newSeqWith(28, elem) & v.toBytesLE().toSeq()

func z(i: int): seq[byte] =
  zeroHashes[i].data.toSeq()

type TestData[limit: static int64] = object
  count: uint32
  expectedRoot: seq[byte]

# Cases from:
# https://github.com/ethereum/consensus-specs/blob/dev/tests/core/pyspec/eth2spec/utils/test_merkle_minimal.py
# Only the happy cases as our merkleizer will accept more chunks than the limit.
let cases = (
  TestData[0](count: 0, expectedRoot: z(0)),
  # TestData[1](count: 0, expectedRoot: None), # cut-off due to limit
  # TestData[2](count: 0, expectedRoot: None), # cut-off due to limit
  TestData[1](count: 0, expectedRoot: z(0)),
  TestData[1](count: 1, expectedRoot: e(0)),
  # TestData[1](count: 2, expectedRoot: None), # cut-off due to limit
  TestData[2](count: 0, expectedRoot: h(z(0), z(0))),
  TestData[2](count: 1, expectedRoot: h(e(0), z(0))),
  TestData[2](count: 2, expectedRoot: h(e(0), e(1))),
  # TestData[2](count: 3, expectedRoot: None), # cut-off due to limit
  # TestData[2](count: 16, expectedRoot: None), # bigger cut-off due to limit
  TestData[4](count: 0, expectedRoot: h(h(z(0), z(0)), z(1))),
  TestData[4](count: 1, expectedRoot: h(h(e(0), z(0)), z(1))),
  TestData[4](count: 2, expectedRoot: h(h(e(0), e(1)), z(1))),
  TestData[4](count: 3, expectedRoot: h(h(e(0), e(1)), h(e(2), z(0)))),
  TestData[4](count: 4, expectedRoot: h(h(e(0), e(1)), h(e(2), e(3)))),
  # TestData[4](count: 5, expectedRoot: None), # cut-off due to limit
  TestData[8](count: 0, expectedRoot: h(h(h(z(0), z(0)), z(1)), z(2))),
  TestData[8](count: 1, expectedRoot: h(h(h(e(0), z(0)), z(1)), z(2))),
  TestData[8](count: 2, expectedRoot: h(h(h(e(0), e(1)), z(1)), z(2))),
  TestData[8](count: 3, expectedRoot: h(h(h(e(0), e(1)), h(e(2), z(0))), z(2))),
  TestData[8](count: 4, expectedRoot: h(h(h(e(0), e(1)), h(e(2), e(3))), z(2))),
  TestData[8](count: 5, expectedRoot: h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), z(0)), z(1)))),
  TestData[8](count: 6, expectedRoot: h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), e(5)), h(z(0), z(0))))),
  TestData[8](count: 7, expectedRoot: h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), e(5)), h(e(6), z(0))))),
  TestData[8](count: 8, expectedRoot: h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), e(5)), h(e(6), e(7))))),
  # TestData[8](count: 9, expectedRoot: None), # cut-off due to limit
  TestData[16](count: 0, expectedRoot: h(h(h(h(z(0), z(0)), z(1)), z(2)), z(3))),
  TestData[16](count: 1, expectedRoot: h(h(h(h(e(0), z(0)), z(1)), z(2)), z(3))),
  TestData[16](count: 2, expectedRoot: h(h(h(h(e(0), e(1)), z(1)), z(2)), z(3))),
  TestData[16](count: 3, expectedRoot: h(h(h(h(e(0), e(1)), h(e(2), z(0))), z(2)), z(3))),
  TestData[16](count: 4, expectedRoot: h(h(h(h(e(0), e(1)), h(e(2), e(3))), z(2)), z(3))),
  TestData[16](count: 5, expectedRoot: h(h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), z(0)), z(1))), z(3))),
  TestData[16](count: 6, expectedRoot: h(h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), e(5)), h(z(0), z(0)))), z(3))),
  TestData[16](count: 7, expectedRoot: h(h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), e(5)), h(e(6), z(0)))), z(3))),
  TestData[16](count: 8, expectedRoot: h(h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), e(5)), h(e(6), e(7)))), z(3))),
  TestData[16](count: 9, expectedRoot: h(h(h(h(e(0), e(1)), h(e(2), e(3))), h(h(e(4), e(5)), h(e(6), e(7)))), h(h(h(e(8), z(0)), z(1)), z(2))))
)

suite "Merkleization":
  test "Calculate correct root from provided chunks":
    for testCase in cases.fields:
      var merk = createMerkleizer(testCase.limit)
      var i: uint32 = 0

      while i < testCase.count:
        let elem = e(i)
        merk.addChunk(elem)
        i.inc()

      let calculatedRoot = merk.getFinalHash()

      check calculatedRoot.data.toSeq() == testCase.expectedRoot
