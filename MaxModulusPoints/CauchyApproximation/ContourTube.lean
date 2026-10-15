import MaxModulusPoints.CauchyApproximation.CanonicalDensity
import MaxModulusPoints.CauchyApproximation.ContourDerivative
import MaxModulusPoints.CauchyApproximation.InverseDistortion
import MaxModulusPoints.CauchyApproximation.Model
import MaxModulusPoints.CauchyApproximation.RealSymmetry
import MaxModulusPoints.CauchyApproximation.ScaledDistortion
/-!
# A controlled tube about the canonical contour

The fixed image contour has a uniform interior disk in the enlarged
half-plane. The quarter theorem and lower derivative distortion give a
tube in the original tract whose radius retains the normalization scale.
Every point in this tube has a nearby conformal preimage, giving decay of
order thirteen for the exponential model. The actual contour density has
the matching scale and decay of order nine.
-/

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The fixed image contour admits the same interior disk at every parameter. -/
theorem imageContour_ball_subset_modelHalfPlane (t : ℝ) :
    Metric.ball (imageContour t) (1 / 30) ⊆ modelHalfPlane := by
  intro w hw
  have hdist : ‖w - imageContour t‖ < (1 / 30 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have him : |w.im - t| < (1 / 30 : ℝ) := by
    have h := (Complex.abs_im_le_norm (w - imageContour t)).trans_lt hdist
    simpa only [sub_im, imageContour, add_im, ofReal_im, mul_im, ofReal_re,
      I_im, I_re, mul_one, mul_zero, zero_add, add_zero] using h
  have hre : 1 - 13 * Real.posLog |t| - (1 / 30) < w.re := by
    have h := ((neg_le_abs (w - imageContour t).re).trans
      (Complex.abs_re_le_norm (w - imageContour t))).trans_lt hdist
    simp only [sub_re, imageContour, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
    linarith
  have hlog := lipschitzWith_posLog_abs.dist_le_mul w.im t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlog
  have hlow : Real.posLog |t| - (1 / 30) < Real.posLog |w.im| := by
    linarith [neg_le_abs (Real.posLog |w.im| - Real.posLog |t|)]
  change -14 * Real.posLog |w.im| < w.re
  linarith [Real.posLog_nonneg (x := |t|)]

/-- The actual normalization derivative is positive in norm. -/
theorem NormalizedModel.norm_inverse_deriv_one_pos (m : NormalizedModel) :
    0 < ‖deriv m.inverse 1‖ := by
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hone : (1 : ℂ) ∈ modelHalfPlane := by
    simp [modelHalfPlane, Real.posLog_zero]
  exact norm_pos_iff.2 (univalent_deriv_ne_zero hH m.univalentOn_inverse hone)

/-- Real-part displacement from the fixed contour controls the exponential. -/
theorem norm_exp_le_of_dist_imageContour_le {t r : ℝ} {w : ℂ}
    (hw : ‖w - imageContour t‖ ≤ r) :
    ‖Complex.exp w‖ ≤ Real.exp (1 + r) * (max |t| 1) ^ (-13 : ℝ) := by
  have hre : w.re ≤ 1 - 13 * Real.posLog |t| + r := by
    have h := ((le_abs_self (w - imageContour t).re).trans
      (Complex.abs_re_le_norm (w - imageContour t))).trans hw
    simp only [sub_re, imageContour, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
    linarith
  have hs : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlog : Real.posLog |t| = Real.log (max |t| 1) := by
    rw [Real.posLog_eq_log_max_one (abs_nonneg t), max_comm]
  calc
    _ = Real.exp w.re := Complex.norm_exp w
    _ ≤ Real.exp (1 - 13 * Real.posLog |t| + r) := Real.exp_le_exp.2 hre
    _ = _ := by
      rw [hlog, Real.rpow_def_of_pos hs, ← Real.exp_add]
      congr 1
      ring

/-- A universal coefficient gives an actual tract tube after retaining the
normalization derivative scale, with order-thirteen decay throughout it. -/
theorem exists_scaled_contour_tube :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : NormalizedModel) (t : ℝ) (z : ℂ),
      ‖z - m.contour t‖ ≤ ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4 →
        z ∈ m.domain ∧
          ‖m.modelFunction z‖ ≤ Real.exp (31 / 30) * (max |t| 1) ^ (-13 : ℝ) := by
  obtain ⟨C, hC, hbounds⟩ := exists_scaled_inverse_deriv_contour_bounds
  let ε : ℝ := 1 / (240 * C)
  refine ⟨ε, by positivity, ?_⟩
  intro m t z hz
  have hscale : 0 < ‖deriv m.inverse 1‖ := m.norm_inverse_deriv_one_pos
  have hs : 0 < (max |t| 1) ^ 4 := by positivity
  have hlow : ‖deriv m.inverse 1‖ / (C * (max |t| 1) ^ 4) ≤
      ‖deriv m.inverse (imageContour t)‖ := by
    apply (div_le_iff₀ (mul_pos hC hs)).2
    simpa only [mul_comm] using (hbounds m t).1
  have hrad : ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4 <
      (1 / 30) * ‖deriv m.inverse (imageContour t)‖ / 4 := by
    calc
      _ = (1 / 240) * (‖deriv m.inverse 1‖ / (C * (max |t| 1) ^ 4)) := by
        dsimp only [ε]
        ring
      _ < (1 / 120) * (‖deriv m.inverse 1‖ / (C * (max |t| 1) ^ 4)) :=
        mul_lt_mul_of_pos_right (by norm_num) (div_pos hscale (mul_pos hC hs))
      _ ≤ (1 / 120) * ‖deriv m.inverse (imageContour t)‖ :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)
      _ = _ := by ring
  have hball := imageContour_ball_subset_modelHalfPlane t
  have hu : UnivalentOn m.inverse (Metric.ball (imageContour t) (1 / 30)) :=
    ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
  have hzin : z ∈ Metric.ball (m.inverse (imageContour t))
      ((1 / 30) * ‖deriv m.inverse (imageContour t)‖ / 4) := by
    simpa only [Metric.mem_ball, dist_eq_norm, NormalizedModel.contour,
      Function.comp_def] using hz.trans_lt hrad
  obtain ⟨w, hw, he⟩ := univalent_ball_quarter (by norm_num : (0 : ℝ) < 1 / 30) hu hzin
  have hwH : w ∈ modelHalfPlane := hball hw
  refine ⟨he ▸ m.inverse_mem hwH, ?_⟩
  have hzforward : m.forward z = w := by
    rw [← he, m.right_inverse w hwH]
  change ‖Complex.exp (m.forward z)‖ ≤ _
  rw [hzforward]
  have hwdist : ‖w - imageContour t‖ ≤ (1 / 30 : ℝ) := by
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hw)
  simpa only [show (1 + (1 / 30) : ℝ) = 31 / 30 by norm_num] using
    norm_exp_le_of_dist_imageContour_le hwdist

/-- The actual density has order-nine decay with the same derivative scale
that occurs in the controlled tract tube. -/
theorem exists_scaled_density_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : NormalizedModel) (t : ℝ),
      ‖m.density t‖ ≤ D * ‖deriv m.inverse 1‖ * (max |t| 1) ^ (-9 : ℝ) := by
  obtain ⟨C, hC, hbounds⟩ := exists_scaled_inverse_deriv_contour_bounds
  refine ⟨14 * C * Real.exp 1, by positivity, ?_⟩
  intro m t
  have hs : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hd : ‖deriv m.contour t‖ ≤
      14 * ((C * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖) :=
    (m.norm_deriv_contour_le t).trans
      (mul_le_mul_of_nonneg_left (hbounds m t).2 (by norm_num))
  have hp : (max |t| 1) ^ (-13 : ℝ) * (max |t| 1) ^ (4 : ℕ) =
      (max |t| 1) ^ (-9 : ℝ) := by
    rw [← Real.rpow_natCast (max |t| 1) 4, ← Real.rpow_add hs]
    norm_num
  calc
    _ = (Real.exp 1 * (max |t| 1) ^ (-13 : ℝ)) * ‖deriv m.contour t‖ := by
      rw [NormalizedModel.density, norm_mul, m.norm_modelFunction_contour]
    _ ≤ (Real.exp 1 * (max |t| 1) ^ (-13 : ℝ)) *
        (14 * ((C * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (14 * C * Real.exp 1) * ‖deriv m.inverse 1‖ *
        ((max |t| 1) ^ (-13 : ℝ) * (max |t| 1) ^ (4 : ℕ)) := by ring
    _ = _ := by rw [hp]

#print axioms imageContour_ball_subset_modelHalfPlane
#print axioms NormalizedModel.norm_inverse_deriv_one_pos
#print axioms norm_exp_le_of_dist_imageContour_le
#print axioms exists_scaled_contour_tube
#print axioms exists_scaled_density_bound

end MaxModulusPoints.CauchyApproximation
