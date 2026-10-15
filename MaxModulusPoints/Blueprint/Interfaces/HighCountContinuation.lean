import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.FiberContinuation.Continuation

/-!
# `high_count_continuation`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Continue the closure of regular high-count targets at ordinary, omitted and
infinite spherical values; its product projection is open.
Li, §§4–8: li-v2.txt:147–374. The finite local covers must count physical
pairs and cover the whole local actual image. -/
theorem high_count_continuation {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ)
    (hsmall : SmallCoordinateBound d L) (hnonconstant : NonconstantProducts d) :
    IsOpen (Prod.fst '' closure (highRegularTargets d L)) := by apply @_root_.MaxModulusPoints.Blueprint.Packages.high_count_continuation_proof <;> assumption
