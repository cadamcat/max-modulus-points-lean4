#!/usr/bin/env python3
"""The vendor check must fail by name when a vendored file changes."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
NAMED_FILE = "OAI/Analysis/Crouzeix/Hurwitz.lean"


class VendorCheckTest(unittest.TestCase):
    def test_one_byte_mutation_fails_for_named_vendored_file(self):
        with tempfile.TemporaryDirectory(prefix="vendor-control-") as directory:
            clone = Path(directory) / "repo"
            subprocess.run(
                ["git", "clone", "--local", "--quiet", str(REPO), str(clone)],
                check=True,
            )
            target = clone / NAMED_FILE
            original = target.read_bytes()
            mutated = original[:-1] + (b"Y" if original.endswith(b"X") else b"X")
            self.assertEqual(len(mutated), len(original))
            self.assertNotEqual(mutated, original)
            target.write_bytes(mutated)
            result = subprocess.run(
                [sys.executable, "scripts/check_vendor.py"],
                cwd=clone,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(NAMED_FILE, result.stderr)
            self.assertIn("vendor_reproduction_mismatch", result.stderr)


if __name__ == "__main__":
    unittest.main()
