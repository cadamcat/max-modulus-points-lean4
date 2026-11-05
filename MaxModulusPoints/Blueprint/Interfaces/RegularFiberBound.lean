module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.RegularBound

/-!
# `regular_fiber_bound`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Compactness of the sphere makes the same projection closed. The excluded
small-product cylinder then rules out every regular high-count target.
Li, Proposition 5 and its proof: li-v2.txt:368–377. -/
theorem regular_fiber_bound {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ)
    (hsmall : SmallCoordinateBound d L)
    (hopen : IsOpen (Prod.fst '' closure (highRegularTargets d L))) :
    RegularFiberBound d L := by apply @_root_.MaxModulusPoints.Blueprint.Packages.regular_fiber_bound_proof <;> assumption
