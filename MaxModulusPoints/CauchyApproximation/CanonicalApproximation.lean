import MaxModulusPoints.CauchyApproximation.CanonicalDensity
import MaxModulusPoints.CauchyApproximation.ContourDerivative
import MaxModulusPoints.CauchyApproximation.ContourDistortion
import MaxModulusPoints.CauchyApproximation.EntireExtension
import MaxModulusPoints.CauchyApproximation.Model
/-!
# The canonical entire approximation

The inverse derivative has degree-four growth on the contour tails and is
bounded on every compact parameter interval. The resulting global bound
makes the actual Cauchy density integrable. The contour gluing therefore
determines a unique entire function, without an additional growth or
integrability hypothesis.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Compactness completes the degree-four inverse derivative bound on the
whole interior contour. The constant here may depend on the conformal map. -/
theorem NormalizedModel.exists_inverse_deriv_contour_bound (m : NormalizedModel) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖deriv m.inverse (imageContour t)‖ ≤ C * (max |t| 1) ^ 4 := by
  obtain ⟨T, hT, htail⟩ := exists_uniform_inverse_deriv_contour_tail_bound
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hcont : Continuous (deriv m.inverse ∘ imageContour) :=
    (m.holomorphic_inverse.deriv hH).continuousOn.comp_continuous
      lipschitzWith_imageContour.continuous imageContour_mem_modelHalfPlane
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-T) T)).exists_bound_of_continuousOn
    hcont.continuousOn
  let C : ℝ := max (3936600 * Real.exp (-1)) B
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro t
  by_cases ht : T ≤ |t|
  · exact (htail m t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hmid : t ∈ Icc (-T) T := abs_le.1 (le_of_lt (lt_of_not_ge ht))
    have hp : 1 ≤ (max |t| 1) ^ 4 := one_le_pow₀ (le_max_right _ _)
    calc
      _ ≤ B := hB t hmid
      _ ≤ C := le_max_right _ _
      _ ≤ C * (max |t| 1) ^ 4 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hC.le

/-- The actual canonical contour density is integrable for every normalized
conformal map. -/
theorem NormalizedModel.integrable_density (m : NormalizedModel) : Integrable m.density := by
  obtain ⟨C, hC, hb⟩ := m.exists_inverse_deriv_contour_bound
  have hbr (t : ℝ) : ‖deriv m.inverse (imageContour t)‖ ≤
      C * (max |t| 1) ^ (4 : ℝ) := by
    simpa only [Real.rpow_ofNat] using hb t
  exact (m.entire_canonical_of_inverse_deriv_bound hC.le (by norm_num) hbr).1

/-- The canonical improper Cauchy gluing has exactly one entire extension. -/
theorem NormalizedModel.existsUnique_entire_canonical (m : NormalizedModel) :
    ∃! f : ℂ → ℂ, Differentiable ℂ f ∧ IsCanonicalApproximation m f :=
  m.existsUnique_entire_canonical_of_integrable m.integrable_density

/-- The entire function uniquely determined by the canonical Cauchy gluing. -/
noncomputable def NormalizedModel.canonicalEntire (m : NormalizedModel) : ℂ → ℂ :=
  Classical.choose m.existsUnique_entire_canonical

/-- The canonical entire function is holomorphic everywhere and has the
prescribed actual Cauchy-integral values off the contour. -/
theorem NormalizedModel.canonicalEntire_spec (m : NormalizedModel) :
    Differentiable ℂ m.canonicalEntire ∧ IsCanonicalApproximation m m.canonicalEntire :=
  (Classical.choose_spec m.existsUnique_entire_canonical).1

/-- Every entire function agreeing with the canonical gluing equals the
canonical entire function. -/
theorem NormalizedModel.eq_canonicalEntire_of_entire_canonical (m : NormalizedModel)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hcanonical : IsCanonicalApproximation m f) :
    f = m.canonicalEntire :=
  (Classical.choose_spec m.existsUnique_entire_canonical).2 f ⟨hf, hcanonical⟩

#print axioms NormalizedModel.exists_inverse_deriv_contour_bound
#print axioms NormalizedModel.integrable_density
#print axioms NormalizedModel.existsUnique_entire_canonical
#print axioms NormalizedModel.canonicalEntire
#print axioms NormalizedModel.canonicalEntire_spec
#print axioms NormalizedModel.eq_canonicalEntire_of_entire_canonical

end MaxModulusPoints.CauchyApproximation
