# Verification record

The two maximum-modulus counting answers for non-monomial entire functions, release `v1.0.0`, commit `4b089f1574ec25620e69668d1c49fe163b1e8c84`.

| Check | Command or setup | Result |
| --- | --- | --- |
| Build | `lake build MaxModulusPoints` | Exit 0; 9,372 jobs. |
| Axioms | `./scripts/verify.sh` | Exit 0; `MaxModulusPoints.Blueprint.main` depends exactly on `[propext, Classical.choice, Quot.sound]`. |
| Kernel replay | `lake env leanchecker --fresh MaxModulusPoints.Blueprint.Main` | Exit 0. |
| Comparator | Challenge module `MaxModulusPoints.ComparatorChallenge` copied the definitions from `MaxModulusPoints/Challenge.lean` and added `MaxModulusPoints.Blueprint.main : MaxModulusPoints.Statement` as `sorry`; solution module `MaxModulusPoints.Blueprint.Main`; `definition_names` empty; nanoda enabled. | Exit 0; nanoda and Lean's default kernel accepted the solution, and Comparator reported `Your solution is okay!`. |

Comparator checked the theorem with `definition_names` empty, so the challenge definitions were compared by body. It ran with the development `fake-landrun.sh`, not a Landrun sandbox.

Tool versions: target Lean `4.34.1`; Comparator `ca04cfc72b550331658ec314bf47685281bfd4bf`; lean4export `076e8e57707e813375e8f9da8bf989799ace9680`; nanoda_lib `3a2407216ee84a75f9e1aead6803d0578be06ae7`.

## Lean v4.35.0

The checks below are for the module-system port. Release `v1.0.0` is unchanged.

| Check | Command or setup | Result |
| --- | --- | --- |
| Vendored sources | `python3 scripts/check_vendor.py` | Exit 0; 174 files reconstructed from `b69b82f04a5c17b46532cfb15e4e48005a28bf11` plus `scripts/vendor.patch.gz`. |
| Vendor control | One byte changed in `OAI/Analysis/Crouzeix/Hurwitz.lean` in a disposable clone | Exit 1; `vendor_reproduction_mismatch: OAI/Analysis/Crouzeix/Hurwitz.lean`. |
| Build | `lake build MaxModulusPoints OAI TauCeti FixedPointTheorems Challenge Solution`, after removing `.lake/build` and keeping the Mathlib cache. `LEAN_NUM_THREADS=4`. | Exit 0; 9,503 jobs. Wall 401.05 s; maximum resident set size 3,030,908,928 bytes. |
| Axioms | `./scripts/verify.sh` | Exit 0; `MaxModulusPoints.Blueprint.main` depends exactly on `[propext, Classical.choice, Quot.sound]`. |
| Kernel replay | `lake env leanchecker --fresh MaxModulusPoints` | Exit 0. Wall 1048.72 s; maximum resident set size 6,524,649,472 bytes. |
| Comparator | Challenge module `Challenge`; solution module `Solution`; theorem `MaxModulusPoints.Blueprint.main`; `definition_names` empty; nanoda enabled. `fake-landrun.sh`, not a Landrun sandbox. | Exit 0; nanoda and Lean's default kernel accepted the solution, and Comparator reported `Your solution is okay!`. Wall 189.60 s; maximum resident set size 6,035,308,544 bytes. |

Tool versions: Lean `v4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Comparator `865edc14486c3388e9225daa971da8e157488c3e` with its lean4export requirement set to tag `v4.35.0`; lean4export `5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`; nanoda_lib `8de7e0c4ed3052745a7f8725164efd9e76d84c56`.

### Controls

- Comparator rejected a challenge changing `UnboundedCounts` from `∀ N` to `∃ N` (exit 1): `Const does not match between challenge and target 'MaxModulusPoints.UnboundedCounts'`.

## Controls

- Comparator rejected a challenge changing `UnboundedCounts` from `∀ N` to `∃ N` (exit 1): `Const does not match between challenge and target 'MaxModulusPoints.UnboundedCounts'`.
- Nanoda rejected a proof by `sorry` (exit 1): the export declares the unpermitted axiom `sorryAx`.
- The release gate rejected a deliberately corrupted axiom audit in a disposable copy (exit 2): the report included the unpermitted axiom `VerifyControl.untrusted`.
