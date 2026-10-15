import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz
import MaxModulusPoints.CauchyApproximation.CanonicalDensity
import MaxModulusPoints.CauchyApproximation.EntireExtension
import MaxModulusPoints.CauchyApproximation.Model
/-!
# The derivative of the canonical interior contour

The image curve is globally Lipschitz with constant fourteen. The conformal
inverse identities give the chain rule even at parameters where the curve
is not differentiable, since both derivatives then vanish by definition.
Thus a bound for the inverse derivative along the fixed curve gives a bound
for the actual contour derivative, as in Rempe-Gillen's Corollary 4.4.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The positive logarithm of the absolute value is globally one-Lipschitz. -/
theorem lipschitzWith_posLog_abs : LipschitzWith 1 (fun t : ℝ ↦ Real.posLog |t|) := by
  have hlog : LipschitzOnWith 1 Real.log (Ici (1 : ℝ)) := by
    apply (convex_Ici (1 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun x ↦ x⁻¹)
    · intro x hx
      exact (Real.hasDerivAt_log (ne_of_gt (zero_lt_one.trans_le hx))).hasDerivWithinAt
    · intro x hx
      change ‖x⁻¹‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (zero_le_one.trans hx))]
      exact (inv_le_one₀ (zero_lt_one.trans_le hx)).2 hx
  have habs : LipschitzWith 1 (fun t : ℝ ↦ |t|) := by
    apply LipschitzWith.mk_one
    intro x y
    simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  have hclamp := habs.const_max 1
  apply LipschitzWith.mk_one
  intro x y
  rw [Real.posLog_eq_log_max_one (abs_nonneg x),
    Real.posLog_eq_log_max_one (abs_nonneg y)]
  have hx : max 1 |x| ∈ Ici (1 : ℝ) := le_max_left 1 |x|
  have hy : max 1 |y| ∈ Ici (1 : ℝ) := le_max_left 1 |y|
  have h := hlog.dist_le_mul (max 1 |x|) hx (max 1 |y|) hy
  simp only [NNReal.coe_one, one_mul] at h
  exact h.trans (by simpa only [NNReal.coe_one, one_mul] using hclamp.dist_le_mul x y)

/-- The fixed image curve is globally Lipschitz, including across its two corners. -/
theorem lipschitzWith_imageContour : LipschitzWith 14 imageContour := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_eq_norm, Real.norm_eq_abs]
  norm_num only
  have heq : imageContour s - imageContour t =
      ((-13 * (Real.posLog |s| - Real.posLog |t|) : ℝ) : ℂ) +
        ((s - t : ℝ) : ℂ) * I := by
    simp only [imageContour, ofReal_sub, ofReal_one, ofReal_mul, ofReal_neg,
      ofReal_ofNat]
    ring
  rw [heq]
  calc
    _ ≤ ‖((-13 * (Real.posLog |s| - Real.posLog |t|) : ℝ) : ℂ)‖ +
        ‖((s - t : ℝ) : ℂ) * I‖ := norm_add_le _ _
    _ = 13 * |Real.posLog (|s|) - Real.posLog (|t|)| + |s - t| := by
      simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, norm_I, mul_one]
      norm_num
    _ ≤ 14 * |s - t| := by
      have h := lipschitzWith_posLog_abs.dist_le_mul s t
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      linarith

/-- The fixed image curve has derivative norm at most fourteen everywhere. -/
theorem norm_deriv_imageContour_le (t : ℝ) : ‖deriv imageContour t‖ ≤ 14 :=
  norm_deriv_le_of_lipschitz lipschitzWith_imageContour

/-- The conformal inverse chain rule for the actual contour, including its corners. -/
theorem NormalizedModel.deriv_contour (m : NormalizedModel) (t : ℝ) :
    deriv m.contour t = deriv m.inverse (imageContour t) * deriv imageContour t := by
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hi : DifferentiableAt ℂ m.inverse (imageContour t) :=
    m.holomorphic_inverse.differentiableAt
      (hH.mem_nhds (imageContour_mem_modelHalfPlane t))
  by_cases hα : DifferentiableAt ℝ imageContour t
  · exact deriv_comp t hi hα
  · have hγ : ¬ DifferentiableAt ℝ m.contour t := by
      intro hγ
      have hf : DifferentiableAt ℂ m.forward (m.contour t) :=
        m.holomorphic_forward.differentiableAt
          (m.isOpen_domain.mem_nhds (m.inverse_mem (imageContour_mem_modelHalfPlane t)))
      have heq : m.forward ∘ m.contour = imageContour := by
        funext u
        exact m.right_inverse _ (imageContour_mem_modelHalfPlane u)
      apply hα
      rw [← heq]
      exact (hf.restrictScalars ℝ).comp t hγ
    rw [deriv_zero_of_not_differentiableAt hγ, deriv_zero_of_not_differentiableAt hα,
      mul_zero]

/-- The inverse derivative is the remaining analytic factor in the contour estimate. -/
theorem NormalizedModel.norm_deriv_contour_le (m : NormalizedModel) (t : ℝ) :
    ‖deriv m.contour t‖ ≤ 14 * ‖deriv m.inverse (imageContour t)‖ := by
  rw [m.deriv_contour, norm_mul, mul_comm (14 : ℝ)]
  exact mul_le_mul_of_nonneg_left (norm_deriv_imageContour_le t) (norm_nonneg _)

/-- A polynomial bound for the inverse derivative yields integrability of the
canonical density and the unique entire canonical extension. -/
theorem NormalizedModel.entire_canonical_of_inverse_deriv_bound (m : NormalizedModel)
    {C p : ℝ} (hC : 0 ≤ C) (hp : p ≤ 11)
    (hderiv : ∀ t, ‖deriv m.inverse (imageContour t)‖ ≤ C * (max |t| 1) ^ p) :
    Integrable m.density ∧
      ∃! f : ℂ → ℂ, Differentiable ℂ f ∧ IsCanonicalApproximation m f := by
  have hb (t : ℝ) : ‖deriv m.contour t‖ ≤ (14 * C) * (max |t| 1) ^ p := by
    calc
      _ ≤ 14 * ‖deriv m.inverse (imageContour t)‖ := m.norm_deriv_contour_le t
      _ ≤ 14 * (C * (max |t| 1) ^ p) := mul_le_mul_of_nonneg_left (hderiv t) (by norm_num)
      _ = _ := by ring
  have hρ := m.integrable_density_of_deriv_bound (mul_nonneg (by norm_num) hC) hp hb
  exact ⟨hρ, m.existsUnique_entire_canonical_of_integrable hρ⟩

#print axioms lipschitzWith_posLog_abs
#print axioms lipschitzWith_imageContour
#print axioms norm_deriv_imageContour_le
#print axioms NormalizedModel.deriv_contour
#print axioms NormalizedModel.norm_deriv_contour_le
#print axioms NormalizedModel.entire_canonical_of_inverse_deriv_bound

end MaxModulusPoints.CauchyApproximation
