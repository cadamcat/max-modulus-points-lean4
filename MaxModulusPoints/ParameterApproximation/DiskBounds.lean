import Mathlib.Analysis.Complex.AbsMax
import MaxModulusPoints.Challenge
import MaxModulusPoints.ParameterApproximation.Uniqueness
/-!
# Disk bounds from a logarithmic slice

A bound for the real part of the conformal map on one vertical slice bounds
the entire approximant on the corresponding circle. The maximum modulus
principle transfers this bound to its enclosed disk, including the origin.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Metric
open scoped Topology

universe u

/-- A real upper bound on a single logarithmic slice bounds the entire
approximant on the enclosed planar disk. -/
theorem norm_approximant_le_of_slice_bound {V : Set ℂ} {G f : ℂ → ℂ}
    {M R C : ℝ} (hf : Entire f) (hb : ApproximationBounds V G M f)
    (hM : 0 ≤ M) (hR : 0 < R)
    (hG : ∀ z ∈ V, z.re = R → (G z).re ≤ C)
    {w : ℂ} (hw : ‖w‖ ≤ Real.exp R) : ‖f w‖ ≤ Real.exp C + M := by
  have hr : 0 < Real.exp R := Real.exp_pos R
  have hr1 : 1 < Real.exp R := Real.one_lt_exp_iff.mpr hR
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball (x := (0 : ℂ)) (r := Real.exp R)) hf.diffContOnCl
  · intro z hz
    have hnorm : ‖z‖ = Real.exp R := by
      simpa only [frontier_ball _ hr.ne', mem_sphere, dist_zero_right] using hz
    have hz1 : 1 < ‖z‖ := by rwa [hnorm]
    have herror : M / ‖z‖ ≤ M := div_le_self hM hz1.le
    by_cases hmem : z ∈ Complex.exp '' V
    · obtain ⟨v, hv, rfl⟩ := hmem
      have hvR : v.re = R := Real.exp_injective (by
        simpa only [Complex.norm_exp] using hnorm)
      have hgv : ‖Complex.exp (G v)‖ ≤ Real.exp C := by
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hG v hv hvR)
      calc
        ‖f (Complex.exp v)‖ ≤ ‖f (Complex.exp v) - Complex.exp (G v)‖ +
            ‖Complex.exp (G v)‖ := norm_le_norm_sub_add _ _
        _ ≤ M + Real.exp C := add_le_add ((hb.1 v hv hz1).trans herror) hgv
        _ = Real.exp C + M := add_comm _ _
    · exact (hb.2 z hmem hz1).trans
        (herror.trans (le_add_of_nonneg_left (Real.exp_pos C).le))
  · rw [closure_ball _ hr.ne']
    exact mem_closedBall_zero_iff.mpr hw

/-- Eventual upper bounds on one logarithmic slice give eventual uniform
bounds on its entire enclosed disk. -/
theorem eventually_disk_bound_of_slice_bound {ι : Type u} {l : Filter ι}
    {V : ι → Set ℂ} {G F : ι → ℂ → ℂ} {M R C : ℝ}
    (hF : ∀ i, Entire (F i)) (hb : ∀ i, ApproximationBounds (V i) (G i) M (F i))
    (hM : 0 ≤ M) (hR : 0 < R)
    (hG : ∀ᶠ i in l, ∀ z ∈ V i, z.re = R → (G i z).re ≤ C) :
    ∀ᶠ i in l, ∀ w : ℂ, ‖w‖ ≤ Real.exp R → ‖F i w‖ ≤ Real.exp C + M := by
  filter_upwards [hG] with i hi w hw
  exact norm_approximant_le_of_slice_bound (hF i) (hb i) hM hR hi hw

#print axioms norm_approximant_le_of_slice_bound
#print axioms eventually_disk_bound_of_slice_bound

end MaxModulusPoints.ParameterApproximation
