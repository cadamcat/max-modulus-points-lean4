import MaxModulusPoints.CauchyApproximation.CanonicalDecay
import MaxModulusPoints.CauchyApproximation.CircleCorrection
import MaxModulusPoints.CauchyApproximation.ContourTube
import MaxModulusPoints.CauchyApproximation.Model
/-!
# Bounds for the Cauchy integral on a circle arc

The parametrized Cauchy kernel is continuous on every bounded angular
interval when the boundary data are continuous and the evaluation point
lies in the half-radius disk. Its pointwise norm bound controls every
arc of angular length at most a full turn. The scaled tract tube supplies
such bounds for the actual canonical conformal function.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The normalized Cauchy integral along the oriented angular interval of a circle. -/
noncomputable def circleArcCauchyIntegral (g : ℂ → ℂ) (a : ℂ) (r u v : ℝ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∫ θ : ℝ in u..v, deriv (circleMap a r) θ *
      (g (circleMap a r θ) / (circleMap a r θ - z))

/-- Continuous circle data give an integrable arc kernel and a normalized bound
of twice the boundary bound, for either orientation and at most one full turn. -/
theorem circle_arc_cauchy_bound {g : ℂ → ℂ} {a z : ℂ} {r B u v : ℝ}
    (hr : 0 < r) (hg : ContinuousOn g (Metric.sphere a r)) (hB : 0 ≤ B)
    (hbound : ∀ ζ ∈ Metric.sphere a r, ‖g ζ‖ ≤ B)
    (hz : ‖z - a‖ ≤ r / 2) (hlength : |v - u| ≤ 2 * Real.pi) :
    IntervalIntegrable (fun θ : ℝ ↦ deriv (circleMap a r) θ *
      (g (circleMap a r θ) / (circleMap a r θ - z))) volume u v ∧
      ‖circleArcCauchyIntegral g a r u v z‖ ≤ 2 * B := by
  have hsphere (θ : ℝ) : circleMap a r θ ∈ Metric.sphere a r :=
    circleMap_mem_sphere a hr.le θ
  have hsep (θ : ℝ) : r / 2 ≤ ‖circleMap a r θ - z‖ :=
    half_radius_le_norm_sub_of_mem_sphere hz (hsphere θ)
  have hne (θ : ℝ) : circleMap a r θ - z ≠ 0 :=
    norm_pos_iff.1 (lt_of_lt_of_le (by positivity : 0 < r / 2) (hsep θ))
  have hcont : Continuous (fun θ : ℝ ↦
      g (circleMap a r θ) / (circleMap a r θ - z)) :=
    (hg.comp_continuous (continuous_circleMap a r) hsphere).div
      ((continuous_circleMap a r).sub continuous_const) hne
  have hderiv : Continuous (deriv (circleMap a r)) := by
    rw [funext (deriv_circleMap a r)]
    exact (continuous_circleMap 0 r).mul_const I
  refine ⟨(hderiv.mul hcont).intervalIntegrable u v, ?_⟩
  have hpoint (θ : ℝ) :
      ‖deriv (circleMap a r) θ *
        (g (circleMap a r θ) / (circleMap a r θ - z))‖ ≤ 2 * B := by
    have hkernel : ‖g (circleMap a r θ) / (circleMap a r θ - z)‖ ≤ B / (r / 2) := by
      rw [norm_div]
      exact div_le_div₀ hB (hbound _ (hsphere θ)) (by positivity) (hsep θ)
    have hdnorm : ‖deriv (circleMap a r) θ‖ = r := by
      simp only [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one,
        abs_of_pos hr]
    calc
      _ = r * ‖g (circleMap a r θ) / (circleMap a r θ - z)‖ := by rw [norm_mul, hdnorm]
      _ ≤ r * (B / (r / 2)) := mul_le_mul_of_nonneg_left hkernel hr.le
      _ = 2 * B := by field_simp
  have hb : ‖∫ θ : ℝ in u..v, deriv (circleMap a r) θ *
      (g (circleMap a r θ) / (circleMap a r θ - z))‖ ≤ 4 * Real.pi * B := by
    calc
      _ ≤ (2 * B) * |v - u| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ ↦ hpoint θ)
      _ ≤ (2 * B) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = _ := by ring
  unfold circleArcCauchyIntegral
  rw [norm_mul]
  have hK : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by simp
  rw [hK]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (4 * Real.pi * B) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * B := by field_simp; ring

/-- One scaled tube coefficient controls every arc of at most a full turn,
with actual kernel integrability and order-thirteen normalized decay. -/
theorem exists_scaled_arc_correction :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : NormalizedModel) (t : ℝ) (z : ℂ) (u v : ℝ),
      let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
      ‖z - m.contour t‖ ≤ r / 2 → |v - u| ≤ 2 * Real.pi →
        IntervalIntegrable (fun θ : ℝ ↦ deriv (circleMap (m.contour t) r) θ *
          (m.modelFunction (circleMap (m.contour t) r θ) /
            (circleMap (m.contour t) r θ - z))) volume u v ∧
          ‖circleArcCauchyIntegral m.modelFunction (m.contour t) r u v z‖ ≤
            2 * Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ) := by
  obtain ⟨ε, hε, htube⟩ := exists_scaled_contour_tube
  refine ⟨ε, hε, ?_⟩
  intro m t z u v
  dsimp only
  let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
  intro hz hlength
  have hscale := m.norm_inverse_deriv_one_pos
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsphere (ζ : ℂ) (hζ : ζ ∈ Metric.sphere (m.contour t) r) :
      ζ ∈ m.domain ∧
        ‖m.modelFunction ζ‖ ≤ Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ) := by
    apply htube m t ζ
    exact le_of_eq (by simpa only [Metric.mem_sphere, dist_eq_norm] using hζ)
  have hcont : ContinuousOn m.modelFunction (Metric.sphere (m.contour t) r) :=
    m.holomorphic_forward.cexp.continuousOn.mono (fun ζ hζ ↦ (hsphere ζ hζ).1)
  simpa only [mul_assoc] using circle_arc_cauchy_bound hr hcont
    (by positivity : 0 ≤ Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ))
    (fun ζ hζ ↦ (hsphere ζ hζ).2) hz hlength

#print axioms circle_arc_cauchy_bound
#print axioms exists_scaled_arc_correction

end MaxModulusPoints.CauchyApproximation
