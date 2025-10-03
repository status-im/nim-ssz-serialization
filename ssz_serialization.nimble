mode = ScriptMode.Verbose

packageName   = "ssz_serialization"
version       = "0.1.0"
author        = "Status Research & Development GmbH"
description   = "Simple Serialize (SSZ) serialization and merkleization"
license       = "Apache License 2.0"
skipDirs      = @["tests"]

requires "nim >= 2.0.10",
         "serialization",
         "json_serialization",
         "stew",
         "stint >= 0.8.2",
         "nimcrypto",
         "blscurve",
         "results",
         "unittest2",
         "hashtree_abi"

let nimc = getEnv("NIMC", "nim") # Which nim compiler to use
let lang = getEnv("NIMLANG", "c") # Which backend (c/cpp/js)
let flags = getEnv("NIMFLAGS", "") # Extra flags for the compiler
let verbose = getEnv("V", "") notin ["", "0"]

from os import quoteShell

let cfg =
  " --styleCheck:usages --styleCheck:error" &
  (if verbose: "" else: " --verbosity:0") &
  " --skipParentCfg --skipUserCfg --outdir:build " &
  quoteShell("--nimcache:build/nimcache/$projectName")

proc build(args, path: string) =
  exec nimc & " " & lang & " " & cfg & " " & flags & " " & args & " " & path

proc run(args, path: string) =
  build args & " --mm:refc -r", path
  build args & " --mm:orc -r", path

task test, "Run all tests":
  for blst in [false, true]:
    for hashtree in [false, true]:
      let opts = "--threads:on -d:PREFER_BLST_SHA256=" & $blst & " -d:PREFER_HASHTREE_SHA256=" & $hashtree
      run opts, "tests/test_all"

task fuzzHashtree, "Run fuzzing test":
  # TODO We don't run because the timeout parameter doesn't seem to work so
  # this takes too long
  build "-d:release", "tests/fuzzing/fuzz_hashtree"
