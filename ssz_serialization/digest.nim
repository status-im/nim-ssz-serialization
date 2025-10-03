# ssz_serialization
# Copyright (c) 2018-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

import std/strutils, nimcrypto/[hash, sha2], stew/[ptrops,importops], ./types

# Depending on platform, we have several SHA256 implementations to choose from:
# * nimcrypto is pure nim and used for compile-time evaluation and fallback
# * blst has CPU-specific optimisations and can be used for all hashing on those
#   platforms and is generally faster than nimcrypto
# * hashtree is specialized for hashing 64-byte chunks as happens in a merkle
#   tree - it has limited hardware and compiler support but is faster than
#   blst for the cases it supports
#
# Depending on the below preference flags, we'll enable the faster backends
# the faster backends will be used where they are supported

const PREFER_BLST_SHA256* {.booldefine.} = true
# TODO https://github.com/prysmaticlabs/hashtree/issues/28
const PREFER_HASHTREE_SHA256* {.booldefine.} = true

when PREFER_BLST_SHA256:
  import blscurve
  when BLS_BACKEND == BLST:
    const USE_BLST_SHA256 = true
  else:
    const USE_BLST_SHA256 = false
else:
  const USE_BLST_SHA256 = false

when USE_BLST_SHA256:
  {.hint: "BLST SHA256 backend enabled".}
  type DigestCtx* = BLST_SHA256_CTX
else:
  {.hint: "nimcrypto SHA256 backend enabled".}
  type DigestCtx* = sha2.sha256

when PREFER_HASHTREE_SHA256 and (defined(arm64) or defined(amd64)) and (
  (defined(linux) and defined(gcc)) or
  # llvm-mingw doesn't support hashtree well even with "-fno-integrated-as"
  # this is true with clang-17(19th June 2024).
  (defined(windows) and defined(gcc) and "clang" notin staticExec("gcc --version")) or
  (defined(linux) and defined(clang)) or
  (defined(macosx) and defined(clang) and defined(arm64))
):
  {.hint: "Hashtree SHA256 backend enabled".}

  when tryImport ../vendor/hashtree/hashtree_abi:
    {.hint: "hashtree_abi found in vendor(nimbus build system)".}
    # import hashtree_abi from vendor
    const USE_HASHTREE_SHA256 = true
  elif tryImport hashtree_abi:
    {.hint: "hashtree_abi nimble package found".}
    # import hashtree_abi from nimble package
    const USE_HASHTREE_SHA256 = true
  else:
    {.hint: "hashtree_abi not found, disabling hashtree backend".}
    const USE_HASHTREE_SHA256 = false

template computeDigest*(body: untyped): Digest =
  ## This little helper will init the hash function and return the sliced
  ## hash:
  ## let hashOfData = computeDigest: h.update(data)
  when nimvm:
    block:
      var h {.inject, noinit.}: sha256
      h.init()
      body
      h.finish()
  else:
    when USE_BLST_SHA256:
      block:
        var h {.inject, noinit.}: DigestCtx
        init(h)
        body
        var res {.noinit.}: Digest
        finalize(res.data, h)
        res
    else:
      block:
        var h {.inject, noinit.}: DigestCtx
        init(h)
        body
        finish(h)

func digest*(a: openArray[byte], res: var Digest) =
  when nimvm:
    res = block:
      var h: sha256
      h.init()
      h.update(a)
      h.finish()
  else:
    when USE_HASHTREE_SHA256:
      if a.len() == 64:
        hashtree_hash(baseAddr res.data, baseAddr a, 1)
        return

    when USE_BLST_SHA256:
      # BLST has a fast assembly optimized SHA256
      res.data.bls_sha256_digest(a)
    else:
      res = block:
        # We use the init-update-finish interface to avoid
        # the expensive burning/clearing memory (20~30% perf)
        var h {.noinit.}: DigestCtx
        h.init()
        h.update(a)
        h.finish()

func digest*(a: openArray[byte]): Digest {.noinit.} =
  digest(a, result)

func digest*(a, b: openArray[byte], res: var Digest) =
  when nimvm:
    res = block:
      var h: sha256
      h.init()
      h.update(a)
      h.update(b)
      h.finish()
  else:
    if distance(baseAddr a, baseAddr b) == a.len:
      # Adjacent in memory, make a single call (avoids copies inside the
      # digester)
      digest(makeOpenArray(baseAddr a, a.len + b.len), res)
    elif a.len + b.len == 64:
      # Single call to digester
      var buf {.noinit.}: array[64, byte]
      if a.len > 0:
        copyMem(addr buf[0], unsafeAddr a[0], a.len)
      # b.len > 0 per above..
      if b.len > 0:
        copyMem(addr buf[a.len], unsafeAddr b[0], b.len)
      digest(buf, res)
    else:
      when USE_BLST_SHA256:
        # BLST has a fast assembly optimized SHA256
        res.data.bls_sha256_digest(a)
      else:
        res = block:
          # We use the init-update-finish interface to avoid
          # the expensive burning/clearing memory (20~30% perf)
          var h {.noinit.}: DigestCtx
          h.init()
          h.update(a)
          h.update(b)
          h.finish()

func digest*(a, b: openArray[byte]): Digest {.noinit.} =
  digest(a, b, result)
