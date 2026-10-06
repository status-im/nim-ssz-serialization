mode = ScriptMode.Verbose

packageName   = "ssz_serialization"
version       = "0.1.1"
author        = "Status Research & Development GmbH"
description   = "Simple Serialize (SSZ) serialization and merkleization"
license       = "Apache License 2.0"
skipDirs      = @["tests"]

requires "nim >= 2.2.10",
         "serialization >= 0.5.0",
         "json_serialization",
         "stew >= 0.6.0",
         "stint >= 0.8.2",
         "nimcrypto",
         "blscurve",
         "results",
         "unittest2",
         "testutils",
         "hashtree_abi"

let nimc = getEnv("NIMC", "nim") # Which nim compiler to use
let lang = getEnv("NIMLANG", "c") # Which backend (c/cpp/js)
let flags = getEnv("NIMFLAGS", "") # Extra flags for the compiler
let verbose = getEnv("V", "") notin ["", "0"]
let platform = getEnv("PLATFORM", "")

from std/os import quoteShell

let cfg =
  " --styleCheck:usages --styleCheck:error" &
  (if verbose: "" else: " --verbosity:0") &
  " --skipParentCfg --skipUserCfg --outdir:build -f " &
  quoteShell("--nimcache:build/nimcache/$projectName")

proc build(args, path: string) =
  exec nimc & " " & lang & " " & cfg & " " & flags & " " & args & " " & path

proc run(args, path: string) =
  build args & " -r", path

proc runTests(args: string) =
  for blst in [false, true]:
    for hashtree in [false, true]:
      var opts = "--threads:on -d:PREFER_BLST_SHA256=" & $blst & " -d:PREFER_HASHTREE_SHA256=" & $hashtree
      if blst and hashtree:
        opts = opts & " -d:SSZ_DEBUG_COUNT_HASHES=1 -d:release"
      run opts & args, "tests/test_all"

task test, "Run all tests":
  runTests " --mm:refc"
  runTests " --mm:orc"

task test_asan, "Run all tests with ASAN":
  if platform != "x86":
    # https://clang.llvm.org/docs/AddressSanitizer.html
    putEnv("ASAN_OPTIONS", "detect_leaks=0:detect_stack_use_after_return=1")
    # https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html
    putEnv("UBSAN_OPTIONS", "print_stacktrace=1")
    let asanArgs =
      " --mm:orc -d:useMalloc --cc:clang --debugger:native" &
      " --passC:-fsanitize=address,undefined" &
      " --passL:-fsanitize=address,undefined" &
      " --passC:-fno-sanitize-recover=undefined" &
      " --passC:-fno-sanitize-merge" &
      " --passC:-fno-omit-frame-pointer"
    runTests asanArgs

let
  fuzzSeconds = getEnv("FUZZ_SECONDS", "100")
  fuzzTime =
    if fuzzSeconds == "": " "
    else: " --duration=" & fuzzSeconds & " "

proc fuzz(format: string) =
  for fuzzer in ["libFuzzer", "honggfuzz", "afl"]:
    when defined(macosx):
      if fuzzer == "honggfuzz":
        continue

    exec "ntu fuzz --fuzzer=" & fuzzer & fuzzTime &
      "tests/fuzzing/fuzz_" & format

task fuzzHashtree, "Run fuzzing test":
  fuzz("hashtree")
