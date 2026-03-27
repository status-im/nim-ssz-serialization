# ssz_serialization
# Copyright (c) 2026 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.used.}

import
  unittest2,
  nimcrypto/[hash, sha2],
  ../ssz_serialization/[digest, types]

suite "Digest":
  test "Single input":
    var buf: array[64, byte]
    for i in 0 ..< buf.len:
      buf[i] = (i * 7 + 13).byte
    check digest(buf) == sha256.digest(buf)

  test "Various sizes":
    for aLen in [1, 7, 16, 31, 32, 33, 48]:
      for bLen in [1, 7, 16, 31, 32, 33, 48]:
        var
          a = newSeq[byte](aLen)
          b = newSeq[byte](bLen)
        for i in 0 ..< aLen:
          a[i] = (i * 3 + 1).byte
        for i in 0 ..< bLen:
          b[i] = (i * 5 + 7).byte
        check digest(a, b) == sha256.digest(a & b)

  test "Adjacent":
    var buf: array[64, byte]
    for i in 0 ..< buf.len:
      buf[i] = i.byte
    check:
      digest(buf.toOpenArray(0, 31), buf.toOpenArray(32, 63)) ==
        sha256.digest(buf)
      digest(buf.toOpenArray(0, 15), buf.toOpenArray(16, 47)) ==
        sha256.digest(buf.toOpenArray(0, 47))

  test "Empty inputs":
    var
      a = newSeq[byte](0)
      b = newSeq[byte](32)
    for i in 0 ..< 32:
      b[i] = i.byte
    check:
      digest(a, b) == sha256.digest(b)
      digest(b, a) == sha256.digest(b)
      digest(a, a) == sha256.digest(newSeq[byte](0))
