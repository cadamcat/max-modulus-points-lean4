import MaxModulusPoints.CauchyApproximation.CanonicalApproximation
import MaxModulusPoints.CauchyApproximation.ContourGrowth
import MaxModulusPoints.CauchyApproximation.ContourTube
import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
import MaxModulusPoints.CauchyApproximation.InverseDistortion
import MaxModulusPoints.CauchyApproximation.LocalDetour
import MaxModulusPoints.CauchyApproximation.Model
import MaxModulusPoints.CauchyApproximation.SeparatedDecay
/-!
# Uniform decay of the canonical integral away from its contour tube

The actual canonical contours satisfy uniform quartic position growth and
scaled density decay. Their positive normalization scale is bounded above,
so the separated-kernel estimate gives one inverse-norm constant for all
normalized conformal maps. The canonical entire extension inherits this
bound on the two branches of its gluing wherever the separation holds.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Every positive scaled separation coefficient gives one uniform decay
constant for the actual canonical improper Cauchy integrals. -/
theorem exists_uniform_separated_cauchy_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (z : ℂ),
      0 < ‖z‖ →
      (∀ t, ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4 ≤ ‖m.contour t - z‖) →
      ‖cauchyIntegral m.contour m.density z‖ ≤ C / ‖z‖ := by
  obtain ⟨A, hA, hpos⟩ := exists_uniform_contour_position_bound
  obtain ⟨D, hD, hdensity⟩ := exists_scaled_density_bound
  let S : ℝ := 4 * Real.exp (-1)
  let B : ℝ := 4 * Real.pi * D * S + (4 * Real.pi + 1) * (A * D / ε)
  let K : ℝ := ‖(2 * (Real.pi : ℂ) * I)⁻¹‖
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hB : 0 ≤ B := by dsimp only [B, S]; positivity
  have hK : 0 ≤ K := norm_nonneg _
  refine ⟨K * B + 1, by positivity, ?_⟩
  intro m z hz hsep
  have h := norm_cauchyIntegral_le_of_quartic_growth
    m.proper_contour_and_localDetour_holomorphy.1 m.integrable_density hA hD.le
    m.norm_inverse_deriv_one_pos m.norm_inverse_deriv_one_le hε (hpos m)
    (hdensity m) hz hsep
  change ‖cauchyIntegral m.contour m.density z‖ ≤ K * (B / ‖z‖) at h
  calc
    _ ≤ K * (B / ‖z‖) := h
    _ = (K * B) / ‖z‖ := by ring
    _ ≤ (K * B + 1) / ‖z‖ := div_le_div_of_nonneg_right (by linarith) hz.le

/-- On the separated region, the actual entire extension has controlled error
inside the core and controlled value outside the core. -/
theorem exists_uniform_separated_canonical_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (z : ℂ),
      0 < ‖z‖ →
      (∀ t, ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4 ≤ ‖m.contour t - z‖) →
      (z ∈ m.core → ‖m.canonicalEntire z - m.modelFunction z‖ ≤ C / ‖z‖) ∧
      (z ∉ m.core → ‖m.canonicalEntire z‖ ≤ C / ‖z‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_separated_cauchy_bound hε
  refine ⟨C, hC, ?_⟩
  intro m z hz hsep
  have hscale := m.norm_inverse_deriv_one_pos
  have havoid : z ∉ range m.contour := by
    rintro ⟨t, rfl⟩
    have h := hsep t
    have hp : 0 < ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4 := by positivity
    simp only [sub_self, norm_zero] at h
    linarith
  have hcanonical := m.canonicalEntire_spec.2 z havoid
  constructor
  · intro hcore
    rw [hcanonical.1 hcore, add_sub_cancel_right]
    exact hbound m z hz hsep
  · intro hcore
    rw [hcanonical.2 hcore]
    exact hbound m z hz hsep

#print axioms exists_uniform_separated_cauchy_bound
#print axioms exists_uniform_separated_canonical_bound

end MaxModulusPoints.CauchyApproximation
