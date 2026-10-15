import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Challenge
import MaxModulusPoints.Liminf.Packages

/-!
# `normalize`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Remove the zero at the origin. Li, §2:
li-v2.txt:67–74. -/
theorem normalize (f : ℂ → ℂ) (hf : Entire f) (hn : ¬ IsMonomial f) :
    Nonempty (NormalizedFunction f) := by apply (config := {allowSynthFailures := true}) @_root_.MaxModulusPoints.Blueprint.Packages.normalize_proof <;> assumption
