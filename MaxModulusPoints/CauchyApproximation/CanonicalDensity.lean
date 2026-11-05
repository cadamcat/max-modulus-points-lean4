module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import MaxModulusPoints.CauchyApproximation.DensityBounds
public import MaxModulusPoints.CauchyApproximation.EntireExtension
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# Decay of the canonical contour density

On the fixed interior contour, the function to be approximated has exact
decay of order thirteen. Consequently any polynomial bound of degree at most
eleven for the contour derivative makes the Cauchy density integrable.
Rempe-Gillen's Corollary 4.4 supplies a derivative bound of degree four;
the reduction here isolates the remaining conformal estimate.
-/


@[expose] public section

open Complex MeasureTheory Set

namespace MaxModulusPoints.CauchyApproximation

/-- The fixed image contour lies strictly inside the enlarged half-plane. -/
theorem imageContour_mem_modelHalfPlane (t : ℝ) : imageContour t ∈ modelHalfPlane := by
  change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
  simp only [imageContour, add_im, ofReal_im, mul_im, ofReal_re, mul_re,
    I_im, I_re, mul_one, mul_zero, add_zero, zero_add, add_re, sub_zero]
  linarith [Real.posLog_nonneg (x := |t|)]

/-- The values on the canonical contour are fixed by the conformal inverse identities. -/
theorem NormalizedModel.modelFunction_contour (m : NormalizedModel) (t : ℝ) :
    m.modelFunction (m.contour t) = Complex.exp (imageContour t) := by
  change Complex.exp (m.forward (m.inverse (imageContour t))) = _
  rw [m.right_inverse _ (imageContour_mem_modelHalfPlane t)]

/-- The exact decay of the function to be approximated along its interior contour. -/
theorem NormalizedModel.norm_modelFunction_contour (m : NormalizedModel) (t : ℝ) :
    ‖m.modelFunction (m.contour t)‖ = Real.exp 1 * (max |t| 1) ^ (-13 : ℝ) := by
  rw [m.modelFunction_contour, Complex.norm_exp]
  have hr : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlog : Real.posLog |t| = Real.log (max |t| 1) := by
    rw [Real.posLog_eq_log_max_one (abs_nonneg t), max_comm]
  simp only [imageContour, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  rw [hlog, Real.rpow_def_of_pos hr, ← Real.exp_add]
  congr 1
  ring

/-- A polynomial derivative bound of degree at most eleven suffices for the
integrability of the actual canonical density. -/
theorem NormalizedModel.integrable_density_of_deriv_bound (m : NormalizedModel)
    {C p : ℝ} (hC : 0 ≤ C) (hp : p ≤ 11)
    (hderiv : ∀ t, ‖deriv m.contour t‖ ≤ C * (max |t| 1) ^ p) :
    Integrable m.density := by
  have hα : Continuous imageContour := by
    unfold imageContour
    fun_prop
  have hf : Continuous (fun t ↦ m.modelFunction (m.contour t)) := by
    exact (Complex.continuous_exp.comp hα).congr
      (fun t ↦ (m.modelFunction_contour t).symm)
  apply integrable_density_of_polynomial_bounds hf.aestronglyMeasurable
    (aestronglyMeasurable_deriv m.contour volume) hC (Real.exp_pos 1).le
    (show 0 ≤ 11 - p by linarith) (δ₁ := p)
  · intro t
    rw [m.norm_modelFunction_contour]
    have he : -(2 + p + (11 - p)) = (-13 : ℝ) := by ring
    rw [he]
  · exact hderiv

/-- The polynomial derivative estimate discharges the integrability input in
the construction of the unique entire canonical extension. -/
theorem NormalizedModel.existsUnique_entire_canonical_of_deriv_bound (m : NormalizedModel)
    {C p : ℝ} (hC : 0 ≤ C) (hp : p ≤ 11)
    (hderiv : ∀ t, ‖deriv m.contour t‖ ≤ C * (max |t| 1) ^ p) :
    ∃! f : ℂ → ℂ, Differentiable ℂ f ∧ IsCanonicalApproximation m f :=
  m.existsUnique_entire_canonical_of_integrable (m.integrable_density_of_deriv_bound hC hp hderiv)

#print axioms imageContour_mem_modelHalfPlane
#print axioms NormalizedModel.modelFunction_contour
#print axioms NormalizedModel.norm_modelFunction_contour
#print axioms NormalizedModel.integrable_density_of_deriv_bound
#print axioms NormalizedModel.existsUnique_entire_canonical_of_deriv_bound

end MaxModulusPoints.CauchyApproximation
