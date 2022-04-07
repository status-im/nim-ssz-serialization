mode = ScriptMode.Verbose

packageName   = "ssz_serialization"
version       = "0.1.0"
author        = "Status Research & Development GmbH"
description   = "Simple Serialize (SSZ) serialization and merkleization"
license       = "Apache License 2.0"
skipDirs      = @["tests"]

requires "nim >= 1.2.0",
         "serialization",
         "json_serialization",
         "stew",
         "stint",
         "nimcrypto",
         "blscurve",
         "unittest2"

proc test(args, path: string) =
  if not dirExists "build":
    mkDir "build"
  exec "nim " & getEnv("TEST_LANG", "c") & " " & getEnv("NIMFLAGS") & " " & args &
    " -r --skipParentCfg" &
    " --styleCheck:usages --styleCheck:hint" &
    " --hint[XDeclaredButNotUsed]:off --hint[Processing]:off " &
    path

task test, "Run all tests":
  test "--threads:off -d:PREFER_BLST_SHA256=false", "tests/test_all"
  test "--threads:on -d:PREFER_BLST_SHA256=false", "tests/test_all"
