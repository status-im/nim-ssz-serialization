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
         "https://github.com/markspanbroek/nim-blscurve#94ea0bf"

proc test(env, path: string) =
  # Compilation language is controlled by TEST_LANG
  var lang = "c"
  if existsEnv"TEST_LANG":
    lang = getEnv"TEST_LANG"

  if not dirExists "build":
    mkDir "build"
  exec "nim " & lang & " " & env &
    " -r --hints:off --warnings:off " & path

task test, "Run all tests":
  test "--threads:off", "tests/test_all"
  test "--threads:on", "tests/test_all"
