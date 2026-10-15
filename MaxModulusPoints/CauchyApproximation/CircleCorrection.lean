import MaxModulusPoints.CauchyApproximation.ContourTube
import MaxModulusPoints.CauchyApproximation.Model
import MaxModulusPoints.CauchyApproximation.SeparatedDecay
/-!
# The finite-circle contribution to controlled Cauchy approximation

For an evaluation point in the half-radius disk, the Cauchy denominator on
the circle is bounded below by half the radius. Integrating the resulting
bound controls the normalized circle contribution by twice the boundary
function bound. The scaled tract tube supplies such circles and boundary
bounds for the canonical conformal function.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The circle stays half a radius away from every point in its half-radius disk. -/
theorem half_radius_le_norm_sub_of_mem_sphere {a z ζ : ℂ} {r : ℝ}
    (hz : ‖z - a‖ ≤ r / 2) (hζ : ζ ∈ Metric.sphere a r) :
    r / 2 ≤ ‖ζ - z‖ := by
  have heq : ‖ζ - a‖ = r := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hζ
  have h : ‖ζ - a‖ ≤ ‖ζ - z‖ + ‖z - a‖ := by
    simpa only [dist_eq_norm] using dist_triangle ζ z a
  rw [heq] at h
  linarith

/-- The normalized Cauchy integral on a circle is bounded by twice the function
bound, and its kernel is integrable when the boundary data are continuous. -/
theorem circle_cauchy_bound {g : ℂ → ℂ} {a z : ℂ} {r B : ℝ}
    (hr : 0 < r) (hg : ContinuousOn g (Metric.sphere a r)) (hB : 0 ≤ B)
    (hbound : ∀ ζ ∈ Metric.sphere a r, ‖g ζ‖ ≤ B)
    (hz : ‖z - a‖ ≤ r / 2) :
    CircleIntegrable (fun ζ ↦ g ζ / (ζ - z)) a r ∧
      ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        circleIntegral (fun ζ ↦ g ζ / (ζ - z)) a r‖ ≤ 2 * B := by
  have hsep (ζ : ℂ) (hζ : ζ ∈ Metric.sphere a r) : r / 2 ≤ ‖ζ - z‖ :=
    half_radius_le_norm_sub_of_mem_sphere hz hζ
  have hne (ζ : ℂ) (hζ : ζ ∈ Metric.sphere a r) : ζ - z ≠ 0 :=
    norm_pos_iff.1 (lt_of_lt_of_le (by positivity : 0 < r / 2) (hsep ζ hζ))
  refine ⟨(hg.div (continuousOn_id.sub continuousOn_const) hne).circleIntegrable hr.le, ?_⟩
  have hkernel (ζ : ℂ) (hζ : ζ ∈ Metric.sphere a r) :
      ‖g ζ / (ζ - z)‖ ≤ B / (r / 2) := by
    rw [norm_div]
    exact div_le_div₀ hB (hbound ζ hζ) (by positivity) (hsep ζ hζ)
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hkernel
  change ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
    circleIntegral (fun ζ ↦ g ζ / (ζ - z)) a r‖ ≤ r * (B / (r / 2)) at h
  calc
    _ ≤ r * (B / (r / 2)) := h
    _ = 2 * B := by field_simp

/-- The actual scaled tract tube supplies integrable finite-circle corrections
with order-thirteen bounds, uniformly over the normalized conformal maps. -/
theorem exists_scaled_circle_correction :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : NormalizedModel) (t : ℝ) (z : ℂ),
      let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
      ‖z - m.contour t‖ ≤ r / 2 →
        CircleIntegrable (fun ζ ↦ m.modelFunction ζ / (ζ - z)) (m.contour t) r ∧
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
            circleIntegral (fun ζ ↦ m.modelFunction ζ / (ζ - z)) (m.contour t) r‖ ≤
              2 * Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ) := by
  obtain ⟨ε, hε, htube⟩ := exists_scaled_contour_tube
  refine ⟨ε, hε, ?_⟩
  intro m t z
  dsimp only
  let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
  intro hz
  have hscale := m.norm_inverse_deriv_one_pos
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsphere (ζ : ℂ) (hζ : ζ ∈ Metric.sphere (m.contour t) r) :
      ζ ∈ m.domain ∧
        ‖m.modelFunction ζ‖ ≤ Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ) := by
    apply htube m t ζ
    exact le_of_eq (by simpa only [Metric.mem_sphere, dist_eq_norm] using hζ)
  have hcont : ContinuousOn m.modelFunction (Metric.sphere (m.contour t) r) :=
    m.holomorphic_forward.cexp.continuousOn.mono (fun ζ hζ ↦ (hsphere ζ hζ).1)
  simpa only [mul_assoc] using circle_cauchy_bound hr hcont
    (by positivity : 0 ≤ Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ))
    (fun ζ hζ ↦ (hsphere ζ hζ).2) hz

#print axioms half_radius_le_norm_sub_of_mem_sphere
#print axioms circle_cauchy_bound
#print axioms exists_scaled_circle_correction

end MaxModulusPoints.CauchyApproximation
