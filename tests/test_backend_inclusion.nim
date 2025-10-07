import unittest2
import ../ssz_serialization/digest

suite "Hashtree backend":

  test "preference + support implies USE == ABI_FOUND":
    when PREFER_HASHTREE_SHA256 and HASHTREE_SUPPORTED:
      check USE_HASHTREE_SHA256 == HASHTREE_ABI_FOUND

    test "constants are consistent":
      when USE_HASHTREE_SHA256:
        check PREFER_HASHTREE_SHA256
        check HASHTREE_SUPPORTED
        check HASHTREE_ABI_FOUND
