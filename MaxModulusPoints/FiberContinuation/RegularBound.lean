module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.Basic

/-!
# Bounding regular physical fibers

The open product projection, compactness of the spherical value space and
the excluded small-product cylinder give the regular-fiber bound.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint.Packages

open Set

/-- The compact-sphere argument for the bound on every regular finite fiber. -/
theorem regular_fiber_bound_proof {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ)
    (hsmall : SmallCoordinateBound d L)
    (hopen : IsOpen (Prod.fst '' closure (highRegularTargets d L))) :
    RegularFiberBound d L := by
  intro s q hs hq hregular
  by_contra hbound
  have hhigh : (s, (q : OnePoint ℂ)) ∈ highRegularTargets d L :=
    ⟨hs, q, rfl, hq, hregular, lt_of_not_ge hbound⟩
  rw [FiberContinuation.high_regular_targets_eq_empty d L hsmall hopen] at hhigh
  exact hhigh

end MaxModulusPoints.Blueprint.Packages
