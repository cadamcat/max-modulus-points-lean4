#!/usr/bin/env python3
"""Check that each vendored file is the recorded baseline plus the recorded patch.

The baseline commit is the snapshot copied from upstream. The patch is the
Mathlib and module-system port. An edit that is not in the patch fails, and
the message names the file.
"""

import gzip
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOTS = ("OAI", "TauCeti", "FixedPointTheorems")


def _git_bytes(repo, spec):
    result = subprocess.run(
        ["git", "-C", str(repo), "cat-file", "blob", spec],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode:
        raise ValueError("vendor_baseline_read_failed: " + spec)
    return result.stdout


def _present(repo, spec):
    result = subprocess.run(
        ["git", "-C", str(repo), "cat-file", "-e", spec],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.returncode == 0


def _inventory(repo):
    found = set()
    for top in ROOTS:
        root = repo / top
        if not root.is_dir():
            raise ValueError("vendor_root_missing: " + top)
        for path in root.rglob("*"):
            if not path.is_file():
                continue
            if path.suffix != ".lean" and path.name != "LICENSE":
                continue
            if path.is_symlink():
                raise ValueError("vendor_symlink_rejected: " + path.relative_to(repo).as_posix())
            found.add(path.relative_to(repo).as_posix())
    return found


def check(repo):
    repo = repo.resolve()
    manifest = json.loads((repo / "scripts" / "vendor_sources.json").read_text())
    entries = manifest["files"]
    listed = [entry["path"] for entry in entries]
    if len(listed) != len(set(listed)):
        raise ValueError("vendor_inventory_duplicate")
    actual = _inventory(repo)
    if actual != set(listed):
        missing = sorted(actual - set(listed))
        extra = sorted(set(listed) - actual)
        detail = (missing or extra)[:3]
        raise ValueError("vendor_inventory_mismatch: " + ", ".join(detail))

    patch_rel = manifest["patch"]
    if Path(patch_rel).is_absolute() or ".." in Path(patch_rel).parts:
        raise ValueError("vendor_patch_path_escape")
    patch_path = repo / patch_rel
    patch_gz = patch_path.read_bytes()
    if hashlib.sha256(patch_gz).hexdigest() != manifest["patchSha256"]:
        raise ValueError("vendor_patch_hash_mismatch: " + patch_rel)
    try:
        patch = gzip.decompress(patch_gz)
    except OSError as exc:
        raise ValueError("vendor_patch_decode_failed: " + patch_rel) from exc

    baseline = manifest["baselineCommit"]
    with tempfile.TemporaryDirectory(prefix="vendor-reconstruction-") as directory:
        rebuilt = Path(directory)
        for entry in entries:
            rel = entry["path"]
            if entry["library"] not in ROOTS or not rel.startswith(entry["library"] + "/"):
                raise ValueError("vendor_provenance_mismatch: " + rel)
            if entry["inBaseline"] != _present(repo, baseline + ":" + rel):
                raise ValueError("vendor_baseline_flag_mismatch: " + rel)
            if entry["inBaseline"]:
                destination = rebuilt / rel
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(_git_bytes(repo, baseline + ":" + rel))
        apply = subprocess.run(
            ["git", "apply", "--whitespace=nowarn"],
            input=patch,
            cwd=rebuilt,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if apply.returncode:
            detail = apply.stderr.decode(errors="replace").strip()
            raise ValueError("vendor_patch_apply_failed: " + detail)
        for entry in entries:
            rel = entry["path"]
            got = (rebuilt / rel).read_bytes()
            current = (repo / rel).read_bytes()
            if got != current:
                raise ValueError("vendor_reproduction_mismatch: " + rel)
    return len(entries)


if __name__ == "__main__":
    try:
        count = check(Path(__file__).resolve().parents[1])
    except (ValueError, OSError, KeyError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
    print(f"Reconstructed and verified {count} vendored sources.")
