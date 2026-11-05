module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Tactic.Linarith
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge

/-!
# Uniqueness of entire approximants with decaying error

The interior and exterior bounds of the conformal approximation determine the
entire function uniquely, even when the two error constants differ.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter
open scoped Topology

/-- The two decaying error bounds, without an existence or regularity claim. -/
def ApproximationBounds (V : Set ℂ) (G : ℂ → ℂ) (M : ℝ) (f : ℂ → ℂ) : Prop :=
  (∀ z ∈ V, 1 < ‖Complex.exp z‖ →
    ‖f (Complex.exp z) - Complex.exp (G z)‖ ≤ M / ‖Complex.exp z‖) ∧
  (∀ z, z ∉ Complex.exp '' V → 1 < ‖z‖ → ‖f z‖ ≤ M / ‖z‖)

/-- An entire function that decays at infinity is zero. -/
theorem entire_eq_zero_of_decay {f : ℂ → ℂ} (hf : Entire f) (C : ℝ)
    (hdecay : ∀ z, 1 < ‖z‖ → ‖f z‖ ≤ C / ‖z‖) : f = 0 := by
  have hlim : Tendsto f (cocompact ℂ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_gt_atTop (max 1 (C / ε)))] with z hz
    have hnorm : 1 < ‖z‖ := (le_max_left _ _).trans_lt hz
    have hquot : C / ε < ‖z‖ := (le_max_right _ _).trans_lt hz
    have hC : C < ‖z‖ * ε := (div_lt_iff₀ hε).mp hquot
    have hbound : C / ‖z‖ < ε :=
      (div_lt_iff₀ (lt_trans zero_lt_one hnorm)).mpr (by nlinarith)
    simpa [dist_zero_right] using (hdecay z hnorm).trans_lt hbound
  exact (show Differentiable ℂ f from hf).eq_const_of_tendsto_cocompact hlim

/-- Interior and exterior decaying bounds determine the entire approximant. -/
theorem approximation_unique {V : Set ℂ} {G : ℂ → ℂ} {M₁ M₂ : ℝ}
    {f₁ f₂ : ℂ → ℂ} (hf₁ : Entire f₁) (hf₂ : Entire f₂)
    (h₁ : ApproximationBounds V G M₁ f₁)
    (h₂ : ApproximationBounds V G M₂ f₂) : f₁ = f₂ := by
  have hzero : (fun z => f₁ z - f₂ z) = 0 := by
    apply entire_eq_zero_of_decay (hf₁.sub hf₂) (M₁ + M₂)
    intro z hz
    by_cases hmem : z ∈ Complex.exp '' V
    · obtain ⟨w, hw, rfl⟩ := hmem
      calc
        ‖f₁ (Complex.exp w) - f₂ (Complex.exp w)‖ =
            ‖(f₁ (Complex.exp w) - Complex.exp (G w)) -
              (f₂ (Complex.exp w) - Complex.exp (G w))‖ := by
                rw [sub_sub_sub_cancel_right]
        _ ≤ ‖f₁ (Complex.exp w) - Complex.exp (G w)‖ +
            ‖f₂ (Complex.exp w) - Complex.exp (G w)‖ := norm_sub_le _ _
        _ ≤ M₁ / ‖Complex.exp w‖ + M₂ / ‖Complex.exp w‖ :=
          add_le_add (h₁.1 w hw hz) (h₂.1 w hw hz)
        _ = (M₁ + M₂) / ‖Complex.exp w‖ := (add_div _ _ _).symm
    · exact (norm_sub_le _ _).trans
        ((add_le_add (h₁.2 z hmem hz) (h₂.2 z hmem hz)).trans_eq
          (add_div _ _ _).symm)
  funext z
  exact sub_eq_zero.mp (congrFun hzero z)

#print axioms entire_eq_zero_of_decay
#print axioms approximation_unique

end MaxModulusPoints.ParameterApproximation
