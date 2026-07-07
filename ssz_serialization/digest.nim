import std/strutils, nimcrypto/[hash, sha2], stew/ptrops, ./types

const PREFER_HASHTREE_SHA256 {.booldefine.} = true

{.hint: "nimcrypto SHA256 backend enabled".}
type DigestCtx = sha2.sha256

when PREFER_HASHTREE_SHA256 and (defined(arm64) or defined(amd64)) and (
  (defined(linux) and defined(gcc)) or
  (defined(windows) and defined(gcc) and "clang" notin staticExec("gcc --version")) or
  (defined(linux) and defined(clang)) or
  (defined(macosx) and defined(clang) and defined(arm64))
):
  import stew/importops
  when tryImport ../vendor/hashtree/hashtree_abi:
    {.hint: "Hashtree SHA256 backend enabled via vendor directory import".}
  else:
    import hashtree_abi
    {.hint: "Hashtree SHA256 backend enabled via search path import".}
  const USE_HASHTREE_SHA256 = true
else:
  const USE_HASHTREE_SHA256 = false

template computeDigest(body: untyped): Digest =
  when nimvm:
    block:
      var h {.inject, noinit.}: sha256
      h.init()
      body
      h.finish()
  else:
    block:
      var h {.inject, noinit.}: DigestCtx
      init(h)
      body
      finish(h)

func digest(a: openArray[byte], res: var Digest) =
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

    res = block:
      var h {.noinit.}: DigestCtx
      h.init()
      h.update(a)
      h.finish()

func digest(a: openArray[byte]): Digest {.noinit.} =
  digest(a, result)

func digest(a, b: openArray[byte], res: var Digest) =
  when nimvm:
    res = block:
      var h: sha256
      h.init()
      h.update(a)
      h.update(b)
      h.finish()
  else:
    if distance(baseAddr a, baseAddr b) == a.len:
      digest(makeOpenArray(baseAddr a, a.len + b.len), res)
    elif a.len + b.len == 64:
      var buf {.noinit.}: array[64, byte]
      if a.len > 0:
        copyMem(addr buf[0], unsafeAddr a[0], a.len)
      if b.len > 0:
        copyMem(addr buf[a.len], unsafeAddr b[0], b.len)
      digest(buf, res)
    else:
      res = block:
        var h {.noinit.}: DigestCtx
        h.init()
        h.update(a)
        h.update(b)
        h.finish()

func digest(a, b: openArray[byte]): Digest {.noinit.} =
  digest(a, b, result)

var buf: array[64, byte]
for i in 0 ..< buf.len:
  buf[i] = (i * 7 + 13).byte
let a = digest(buf)
echo "a = ", $a
echo "buf = ", buf
doAssert $a == "3A38AED112131D75FC0E636437F5B675C83C01ADE88D99F6B6C54B0D6129174F"
