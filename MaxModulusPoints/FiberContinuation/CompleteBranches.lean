import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.FiberContinuation.Basic
import MaxModulusPoints.FiberContinuation.ClosedBranches
import MaxModulusPoints.FiberContinuation.ExactCovers
import MaxModulusPoints.FiberContinuation.HighBranches
import MaxModulusPoints.FiberContinuation.LocalFamilies
import MaxModulusPoints.FiberContinuation.StabilizedCovers
import MaxModulusPoints.FiberContinuation.ValueCoordinates
/-!
# Complete branches in the high-count closure

A selected branch has an analytic physical parametrization on a full disk.
Its common spherical value is a positive power in a centered value chart.
Every point of the high-count closure away from the omitted value lies on
such a branch, including points over infinity.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Metric
open MaxModulusPoints.Blueprint

/-- A full analytic physical branch through a target, contained in the
high-count closure, with a nonconstant common-value parameter. -/
structure CompleteHighBranch {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ)
    (s : ℂ) (p : OnePoint ℂ) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  radius : ℝ
  radius_pos : 0 < radius
  pair : ℂ → ℂ × ℂ
  analytic_pair : AnalyticOnNhd ℂ pair (ball 0 radius)
  central_pair : pair 0 ∈ physicalFiber d s p
  forward : ∀ t ∈ ball 0 radius,
    pair t ∈ physicalFiber d ((pair t).1 * (pair t).2)
      (centeredValue p (t ^ exponent))
  high : ∀ t ∈ ball 0 radius,
    ((pair t).1 * (pair t).2, centeredValue p (t ^ exponent)) ∈
      closure (highRegularTargets d L)

/-- Away from the omitted value, the local selected-branch identity supplies
a complete branch through every point of the high-count closure. -/
theorem exists_complete_high_branch_of_value_ne {f : ℂ → ℂ}
    (d : NormalizedFunction f) (L : ℕ) (hsmall : SmallCoordinateBound d L)
    {s : ℂ} {p : OnePoint ℂ} (hy : (s, p) ∈ closure (highRegularTargets d L))
    (hp : p ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)) :
    Nonempty (CompleteHighBranch d L s p) := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_product_norm_lower_bound d L hsmall
  have hs : s ≠ 0 := by
    intro hs
    have hnorm := hbound (s, p) hy
    simpa only [hs, norm_zero, not_le_of_gt hρ] using hnorm
  obtain ⟨C⟩ := exists_common_power_family d hs p hp
  obtain ⟨D⟩ := C.exists_stabilized_cover hs hp
  have hselected : (s, p) ∈ C.rawBranchUnion (D.selectedIndices L) D.radius := by
    rw [← D.high_closure_inter_window L]
    exact ⟨hy, D.center_mem⟩
  obtain ⟨i, _⟩ := mem_iUnion.mp hselected
  refine ⟨{
    exponent := C.exponent
    exponent_pos := C.exponent_pos
    radius := D.radius
    radius_pos := D.radius_pos
    pair := C.pair i.val
    analytic_pair := D.analytic_pair i.val
    central_pair := C.central_pair i.val
    forward := fun t ht => C.forward i.val t (ball_subset_ball D.radius_le ht)
    high := ?_ }⟩
  intro t ht
  exact D.selected_union_subset_high_closure L
    (mem_iUnion.mpr ⟨i, t, ht, rfl⟩)

end MaxModulusPoints.FiberContinuation
