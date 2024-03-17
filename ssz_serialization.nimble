mode = ScriptMode.Verbose

packageName   = "ssz_serialization"
version       = "0.1.0"
author        = "Status Research & Development GmbH"
description   = "Simple Serialize (SSZ) serialization and merkleization"
license       = "Apache License 2.0"
skipDirs      = @["tests"]

requires "nim >= 1.6.0",
         "serialization",
         "json_serialization",
         "stew",
         "stint",
         "nimcrypto",
         "blscurve",
         "unittest2"

let nimc = getEnv("NIMC", "nim") # Which nim compiler to use
let lang = getEnv("NIMLANG", "c") # Which backend (c/cpp/js)
let flags = getEnv("NIMFLAGS", "") # Extra flags for the compiler
let verbose = getEnv("V", "") notin ["", "0"]

from os import quoteShell

let cfg =
  " --styleCheck:usages --styleCheck:error" &
  (if verbose: "" else: " --verbosity:0 --hints:off") &
  " --skipParentCfg --skipUserCfg --outdir:build " &
  quoteShell("--nimcache:build/nimcache/$projectName")

proc build(args, path: string) =
  exec nimc & " " & lang & " " & cfg & " " & flags & " " & args & " " & path

proc run(args, path: string) =
  build args & " -r", path
  if (NimMajor, NimMinor) > (1, 6):
    build args & " --mm:refc -r", path

task test, "Run all tests":
  run "--threads:off -d:PREFER_BLST_SHA256=false", "tests/test_all"
  run "--threads:on -d:PREFER_BLST_SHA256=false", "tests/test_all"
