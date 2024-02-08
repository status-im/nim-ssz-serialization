# ssz_serialization
# Copyright (c) 2018-2024 Status Research & Development GmbH
# Licensed and distributed under either of
#   * MIT license (license terms in the root directory or at https://opensource.org/licenses/MIT).
#   * Apache v2 license (license terms in the root directory or at https://www.apache.org/licenses/LICENSE-2.0).
# at your option. This file may not be copied, modified, or distributed except according to those terms.

{.compile: "../vendor/hashtree/src/hashtree.c".}

when defined(arm64):
  {.compile: "../vendor/hashtree/src/sha256_armv8_neon_x1.S".}
  {.compile: "../vendor/hashtree/src/sha256_armv8_neon_x4.S".}

elif defined(amd64):
  {.compile: "../vendor/hashtree/src/sha256_avx_x1.S".}
  {.compile: "../vendor/hashtree/src/sha256_avx_x4.S".}
  {.compile: "../vendor/hashtree/src/sha256_avx_x8.S".}
  {.compile: "../vendor/hashtree/src/sha256_avx_x16.S".}
  {.compile: "../vendor/hashtree/src/sha256_shani.S".}
  {.compile: "../vendor/hashtree/src/sha256_sse_x1.S".}

type HashFcn* = proc(output: pointer, input: pointer, count: uint64) {.cdecl, noSideEffect, gcsafe, raises: [].}

proc hashtree_init*(override: HashFcn): cint {.importc, gcsafe, raises: [].}
func hashtree_hash*(output: pointer, input: pointer, count: uint64) {.importc, gcsafe, raises: [].}
