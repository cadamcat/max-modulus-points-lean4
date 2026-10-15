#!/usr/bin/env bash
# Build the release library and check the axioms of its assembled theorem.
set -euo pipefail
cd "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build MaxModulusPoints
out=$(lake env lean Verification/Axioms.lean 2>&1)
printf '%s\n' "$out"
flat=$(printf '%s' "$out" | tr '\n' ' ' | sed -E 's/[[:space:]]+/ /g')
reports=$(printf '%s' "$flat" | grep -oE 'depends on axioms: \[[^]]*\]|does not depend on any axioms' || true)
n=$(printf '%s\n' "$reports" | grep -c . || true)
[ "$n" -eq 1 ] || { echo "verify: expected one axiom report, got $n" >&2; exit 2; }
case "$reports" in
  'depends on axioms: [propext, Classical.choice, Quot.sound]') ;;
  *) echo "verify: unexpected axiom report" >&2; exit 2 ;;
esac
echo "verify: OK"
