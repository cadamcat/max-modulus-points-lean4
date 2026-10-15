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

## Controls

- Comparator rejected a challenge changing `UnboundedCounts` from `∀ N` to `∃ N` (exit 1): `Const does not match between challenge and target 'MaxModulusPoints.UnboundedCounts'`.
- Nanoda rejected a proof by `sorry` (exit 1): the export declares the unpermitted axiom `sorryAx`.
- The release gate rejected a deliberately corrupted axiom audit in a disposable copy (exit 2): the report included the unpermitted axiom `VerifyControl.untrusted`.
