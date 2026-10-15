import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
/-!
# Integrability from polynomial bounds on a contour density

The cancellation of the derivative-growth exponent against the decay exponent
is the estimate preceding equation (2.2) in Rempe-Gillen's Theorem 2.1.
-/

open MeasureTheory Real

namespace MaxModulusPoints.CauchyApproximation

/-- The polynomial estimates on the function and contour derivative imply
absolute integrability of their product. -/
theorem integrable_density_of_polynomial_bounds {f v : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) (hv : AEStronglyMeasurable v)
    {C₂ C₃ δ₁ δ₂ : ℝ} (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hδ₂ : 0 ≤ δ₂)
    (hfb : ∀ t, ‖f t‖ ≤ C₃ * (max |t| 1) ^ (-(2 + δ₁ + δ₂)))
    (hvb : ∀ t, ‖v t‖ ≤ C₂ * (max |t| 1) ^ δ₁) :
    Integrable (fun t ↦ f t * v t) := by
  apply ((integrable_inv_one_add_sq.const_mul 2).const_mul (C₂ * C₃)).mono' (hf.mul hv)
  refine ae_of_all _ fun t ↦ ?_
  have hr : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hprod : ‖f t * v t‖ ≤ (C₂ * C₃) * (max |t| 1) ^ (-(2 + δ₂)) := by
    calc
      ‖f t * v t‖ = ‖f t‖ * ‖v t‖ := norm_mul _ _
      _ ≤ (C₃ * (max |t| 1) ^ (-(2 + δ₁ + δ₂))) *
          (C₂ * (max |t| 1) ^ δ₁) :=
        mul_le_mul (hfb t) (hvb t) (norm_nonneg _) (by positivity)
      _ = (C₂ * C₃) * (max |t| 1) ^ (-(2 + δ₂)) := by
        rw [mul_mul_mul_comm, ← Real.rpow_add hr]
        congr 1 <;> ring
  have hexp : (max |t| 1) ^ (-(2 + δ₂)) ≤ (max |t| 1) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) (by linarith)
  have hsq : t ^ 2 ≤ (max |t| 1) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) (le_max_left |t| 1) 2
  have henv : (max |t| 1) ^ (-2 : ℝ) ≤ 2 * (1 + t ^ 2)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_two]
    have hpos : 0 < (max |t| 1) ^ 2 := sq_pos_of_pos hr
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hpos (by positivity)]
    nlinarith [le_max_right |t| 1]
  exact hprod.trans (mul_le_mul_of_nonneg_left (hexp.trans henv) (mul_nonneg hC₂ hC₃))

#print axioms integrable_density_of_polynomial_bounds

end MaxModulusPoints.CauchyApproximation
