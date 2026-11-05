module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral

/-!
# Holomorphy of improper Cauchy integrals off the contour

A proper curve has closed image. A small ball about an off-contour point is
therefore uniformly separated from the whole curve, including its infinite
tails. This separation supplies an integrable bound for the derivative kernel.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Differentiation under an absolutely convergent improper Cauchy integral,
with the usual squared-denominator formula. -/
theorem hasDerivAt_cauchyIntegral {γ ρ : ℝ → ℂ} (hγ : IsProperMap γ)
    (hρ : Integrable ρ) {z : ℂ} (hz : z ∉ range γ) :
    HasDerivAt (cauchyIntegral γ ρ)
      ((2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t : ℝ, ρ t / (γ t - z) ^ 2) z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hγ.isClosed_range.isOpen_compl z hz
  have hsep₀ (t : ℝ) : ε ≤ ‖γ t - z‖ := by
    by_contra! h
    exact hball (by simpa [Metric.mem_ball, dist_eq_norm] using h) ⟨t, rfl⟩
  have hsep (t : ℝ) (w : ℂ) (hw : w ∈ Metric.ball z (ε / 2)) :
      ε / 2 ≤ ‖γ t - w‖ := by
    have hw' : ‖w - z‖ < ε / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have htri : ‖γ t - z‖ ≤ ‖γ t - w‖ + ‖w - z‖ := by
      simpa only [dist_eq_norm] using dist_triangle (γ t) w z
    linarith [hsep₀ t]
  have hne (t : ℝ) (w : ℂ) (hw : w ∈ Metric.ball z (ε / 2)) : γ t - w ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (half_pos hε) (hsep t w hw))
  have hmeas (w : ℂ) : AEStronglyMeasurable (fun t : ℝ ↦ ρ t / (γ t - w)) :=
    hρ.aestronglyMeasurable.div₀ ((hγ.continuous.sub continuous_const).aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable (fun t : ℝ ↦ ρ t / (γ t - z) ^ 2) :=
    hρ.aestronglyMeasurable.div₀
      (((hγ.continuous.sub continuous_const).pow 2).aestronglyMeasurable)
  have hbound : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z (ε / 2),
      ‖ρ t / (γ t - w) ^ 2‖ ≤ ‖ρ t‖ / (ε / 2) ^ 2 := by
    refine ae_of_all _ fun t w hw ↦ ?_
    rw [norm_div, norm_pow]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos (half_pos hε))
      (pow_le_pow_left₀ (half_pos hε).le (hsep t w hw) 2)
  have hdiff : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z (ε / 2),
      HasDerivAt (fun x : ℂ ↦ ρ t / (γ t - x)) (ρ t / (γ t - w) ^ 2) w := by
    refine ae_of_all _ fun t w hw ↦ ?_
    convert! (hasDerivAt_const w (ρ t)).fun_div
      ((hasDerivAt_id w).const_sub (γ t)) (hne t w hw) using 1 <;> simp
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t ↦ ρ t / (γ t - w))
    (F' := fun w t ↦ ρ t / (γ t - w) ^ 2)
    (bound := fun t ↦ ‖ρ t‖ / (ε / 2) ^ 2)
    (Metric.ball_mem_nhds z (half_pos hε)) (Eventually.of_forall hmeas)
    (cauchyIntegral_converges_of_integrable hγ hρ hz).1 hmeas' hbound
    (hρ.norm.div_const ((ε / 2) ^ 2)) hdiff
  exact hint.2.const_mul _

#print axioms hasDerivAt_cauchyIntegral

end MaxModulusPoints.CauchyApproximation
