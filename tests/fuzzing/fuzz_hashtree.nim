import system/ansi_c, stew/[importops, ptrops], blscurve

when not tryImport ../vendor/hashtree/hashtree_abi:
  import hashtree_abi

proc testOneInput(
    data: ptr UncheckedArray[byte], len: csize_t
): cint {.exportc: "LLVMFuzzerTestOneInput", raises: [].} =
  if len mod 64 != 0 or len == 0:
    return -1

  let
    o0 = c_malloc(len div 2) # We haven't initialized the nim allocator..
    o1 = c_malloc(len div 2)

  hashtree_hash(o0, addr data[0], len.uint64 div 64)

  for i in 0 ..< len.int div 64:
    bls_sha256_digest(
      cast[ptr array[32, byte]](o1.offset(i * 32))[],
      data.toOpenArray(i * 64, (i + 1) * 64 - 1),
    )

  if not equalMem(o0, o1, len div 2):
    quit 1

  c_free(o0)
  c_free(o1)
