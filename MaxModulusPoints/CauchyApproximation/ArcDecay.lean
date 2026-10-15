import MaxModulusPoints.CauchyApproximation.ArcCorrection
import MaxModulusPoints.CauchyApproximation.ContourGrowth
import MaxModulusPoints.CauchyApproximation.ContourTube
import MaxModulusPoints.CauchyApproximation.InverseDistortion
import MaxModulusPoints.CauchyApproximation.Model
/-!
# Uniform inverse-norm decay of the finite arc correction

The normalization scale is bounded above, so the controlled contour tube
can be chosen with radius at most one. Its model bound and the contour's
quartic position growth then convert the order-thirteen arc estimate into
inverse evaluation-norm decay. The same tube coefficient is retained in
the geometric inclusion and integral bound.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- One actual scaled tube has radii at most one while retaining its tract
inclusion and order-thirteen model bound. -/
theorem exists_bounded_scaled_contour_tube :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : NormalizedModel) (t : ℝ),
      let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
      0 < r ∧ r ≤ 1 ∧ ∀ z : ℂ, ‖z - m.contour t‖ ≤ r →
        z ∈ m.domain ∧
          ‖m.modelFunction z‖ ≤ Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ) := by
  obtain ⟨ε₀, hε₀, htube⟩ := exists_scaled_contour_tube
  let S : ℝ := 4 * Real.exp (-1)
  have hS : 0 < S := by dsimp only [S]; positivity
  let ε : ℝ := min ε₀ (1 / S)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  refine ⟨ε, hε, ?_⟩
  intro m t
  dsimp only
  let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
  have hscale := m.norm_inverse_deriv_one_pos
  have hscaleS : ‖deriv m.inverse 1‖ ≤ S := m.norm_inverse_deriv_one_le
  have hnum : ε * ‖deriv m.inverse 1‖ ≤ 1 := by
    calc
      _ ≤ ε * S := mul_le_mul_of_nonneg_left hscaleS hε.le
      _ ≤ (1 / S) * S := mul_le_mul_of_nonneg_right (min_le_right _ _) hS.le
      _ = 1 := by field_simp
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrone : r ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (max |t| 1) ^ 4)).2
    exact hnum.trans (one_le_pow₀ (le_max_right _ _))
  refine ⟨hr, hrone, ?_⟩
  intro z hz
  apply htube m t z
  apply hz.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)) (by positivity)

/-- The same bounded tube and one common constant control the actual arc
correction by the inverse evaluation norm, with actual kernel integrability. -/
theorem exists_uniform_arc_inverse_norm_bound :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      (∀ (m : NormalizedModel) (t : ℝ),
        let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
        0 < r ∧ r ≤ 1 ∧ ∀ w : ℂ, ‖w - m.contour t‖ ≤ r →
          w ∈ m.domain ∧
            ‖m.modelFunction w‖ ≤ Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ)) ∧
      ∀ (m : NormalizedModel) (t : ℝ) (z : ℂ) (u v : ℝ),
        let r : ℝ := ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
        0 < ‖z‖ → ‖z - m.contour t‖ ≤ r / 2 → |v - u| ≤ 2 * Real.pi →
          IntervalIntegrable (fun θ : ℝ ↦ deriv (circleMap (m.contour t) r) θ *
            (m.modelFunction (circleMap (m.contour t) r θ) /
              (circleMap (m.contour t) r θ - z))) volume u v ∧
            ‖circleArcCauchyIntegral m.modelFunction (m.contour t) r u v z‖ ≤ C / ‖z‖ := by
  obtain ⟨ε, hε, htube⟩ := exists_bounded_scaled_contour_tube
  obtain ⟨A, hA, hposition⟩ := exists_uniform_contour_position_bound
  have hApos : 0 < A := zero_lt_one.trans_le hA
  let C : ℝ := 2 * Real.exp (31 / 30) * (A + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨ε, C, hε, hC, htube, ?_⟩
  intro m t z u v
  dsimp only
  let s : ℝ := max |t| 1
  let r : ℝ := ε * ‖deriv m.inverse 1‖ / s ^ 4
  intro hz hnear hlength
  obtain ⟨hr, hrone, hmodel⟩ := htube m t
  have hs : 1 ≤ s := le_max_right _ _
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs
  have hsphere (w : ℂ) (hw : w ∈ Metric.sphere (m.contour t) r) :
      w ∈ m.domain ∧ ‖m.modelFunction w‖ ≤ Real.exp (31 / 30) * s ^ (-13 : ℝ) := by
    apply hmodel w
    exact le_of_eq (by simpa only [Metric.mem_sphere, dist_eq_norm] using hw)
  have hcont : ContinuousOn m.modelFunction (Metric.sphere (m.contour t) r) :=
    m.holomorphic_forward.cexp.continuousOn.mono (fun w hw ↦ (hsphere w hw).1)
  have harc := circle_arc_cauchy_bound hr hcont
    (by positivity : 0 ≤ Real.exp (31 / 30) * s ^ (-13 : ℝ))
    (fun w hw ↦ (hsphere w hw).2) hnear hlength
  refine ⟨harc.1, ?_⟩
  have hnormz : ‖z‖ ≤ (A + 1) * s ^ 4 := by
    have ht := norm_add_le (z - m.contour t) (m.contour t)
    rw [sub_add_cancel] at ht
    have hp := hposition m t
    change ‖m.contour t‖ ≤ A * s ^ 4 at hp
    change ‖z - m.contour t‖ ≤ r / 2 at hnear
    change r ≤ 1 at hrone
    nlinarith
  have hweight : s ^ (-13 : ℝ) * s ^ (4 : ℕ) = s ^ (-9 : ℝ) := by
    rw [← Real.rpow_natCast s 4, ← Real.rpow_add hspos]
    norm_num
  have htail : s ^ (-9 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by norm_num)
  have hbound : ‖circleArcCauchyIntegral m.modelFunction (m.contour t) r u v z‖ ≤
      2 * Real.exp (31 / 30) * s ^ (-13 : ℝ) := by
    simpa only [mul_assoc] using harc.2
  apply (le_div_iff₀ hz).2
  calc
    _ ≤ (2 * Real.exp (31 / 30) * s ^ (-13 : ℝ)) * ((A + 1) * s ^ 4) :=
      mul_le_mul hbound hnormz (norm_nonneg _) (by positivity)
    _ = C * (s ^ (-13 : ℝ) * s ^ (4 : ℕ)) := by dsimp only [C]; ring
    _ = C * s ^ (-9 : ℝ) := by rw [hweight]
    _ ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left htail hC.le

#print axioms exists_bounded_scaled_contour_tube
#print axioms exists_uniform_arc_inverse_norm_bound

end MaxModulusPoints.CauchyApproximation
