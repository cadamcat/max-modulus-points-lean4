import MaxModulusPoints.CauchyApproximation.InverseDistortion
import MaxModulusPoints.CauchyApproximation.Model
/-!
# Distortion from the vertical line to the interior contour

On the tails, disks centered on the line of real part one contain the
interior contour with a fixed relative margin and remain in the enlarged
half-plane. Disk distortion transfers the degree-four inverse derivative
bound to the actual interior contour.
-/

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The interior curve lies at a fixed relative radius in disks contained
in the target domain, for all sufficiently large absolute parameters. -/
theorem imageContour_tail_disks :
    ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ |t| →
      let R : ℝ := (27 / 2) * Real.posLog |t|
      0 < R ∧ Metric.ball (1 + (t : ℂ) * I) R ⊆ modelHalfPlane ∧
        ‖imageContour t - (1 + (t : ℂ) * I)‖ ≤ (26 / 27) * R := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 27)
  have hevent : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ (27 / 2) * Real.log x ≤ x / 2 ∧
        14 * Real.log 2 ≤ 1 + Real.log x / 2 ∧ 0 < Real.log x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hsmall,
      Real.tendsto_log_atTop.eventually_ge_atTop (28 * Real.log 2 + 2)] with x hx hxs hxl
    have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hs : Real.log x ≤ (1 / 27) * x := by
      simpa only [Real.norm_eq_abs, id_eq, abs_of_pos hxlog,
        abs_of_nonneg (by linarith : 0 ≤ x)] using hxs
    exact ⟨hx, by linarith, by linarith, hxlog⟩
  obtain ⟨A, hA⟩ := eventually_atTop.1 hevent
  refine ⟨max A 2, by linarith [le_max_right A 2], ?_⟩
  intro t ht
  obtain ⟨hx, hRhalf, hloglarge, hlogpos⟩ := hA |t| ((le_max_left A 2).trans ht)
  have hL : Real.posLog |t| = Real.log |t| :=
    Real.posLog_eq_log (by simpa only [abs_abs] using (by linarith : 1 ≤ |t|))
  dsimp only
  rw [hL]
  refine ⟨by positivity, ?_, ?_⟩
  · intro u hu
    have hunorm : ‖u - (1 + (t : ℂ) * I)‖ < (27 / 2) * Real.log |t| := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hu
    have him : |u.im - t| < (27 / 2) * Real.log |t| := by
      have h := (Complex.abs_im_le_norm (u - (1 + (t : ℂ) * I))).trans_lt hunorm
      simpa only [sub_im, add_im, one_im, mul_im, ofReal_re, ofReal_im,
        I_re, I_im, mul_one, mul_zero, zero_add, add_zero] using h
    have htri : |t| ≤ |u.im - t| + |u.im| := by
      simpa only [Real.norm_eq_abs, sub_add_cancel, abs_sub_comm] using
        norm_add_le (t - u.im) u.im
    have hlow : |t| / 2 ≤ |u.im| := by linarith
    have hlogu : Real.log |t| - Real.log 2 ≤ Real.posLog |u.im| := by
      calc
        _ = Real.log (|t| / 2) := (Real.log_div (by linarith) (by norm_num)).symm
        _ ≤ Real.log |u.im| := Real.log_le_log (by linarith) hlow
        _ ≤ Real.posLog |u.im| := le_max_right _ _
    have hre := ((neg_le_abs (u - (1 + (t : ℂ) * I)).re).trans
      (Complex.abs_re_le_norm (u - (1 + (t : ℂ) * I)))).trans_lt hunorm
    simp only [sub_re, add_re, one_re, mul_re, ofReal_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
    change -14 * Real.posLog |u.im| < u.re
    linarith
  · have heq : imageContour t - (1 + (t : ℂ) * I) =
        ((-13 * Real.posLog |t| : ℝ) : ℂ) := by
      simp only [imageContour, ofReal_sub, ofReal_one, ofReal_mul, ofReal_neg, ofReal_ofNat]
      ring
    calc
      _ = 13 * Real.log |t| := by
        rw [heq, norm_real, Real.norm_eq_abs, abs_mul, hL, abs_of_pos hlogpos]
        norm_num
      _ ≤ (26 / 27) * ((27 / 2) * Real.log |t|) := le_of_eq (by ring)

/-- Disk normalization turns the Koebe derivative bound into a comparison
with the derivative at the center of any disk of univalence. -/
theorem norm_deriv_le_of_univalent_ball {f : ℂ → ℂ} {a z : ℂ} {R q : ℝ}
    (hR : 0 < R) (hf : UnivalentOn f (Metric.ball a R)) (hq : q < 1)
    (hz : ‖z - a‖ ≤ q * R) :
    ‖deriv f z‖ ≤ (2 / (1 - q) ^ 3) * ‖deriv f a‖ := by
  let u : ℂ := (z - a) / (R : ℂ)
  have hu : ‖u‖ ≤ q := by
    dsimp only [u]
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (div_le_iff₀ hR).2 hz
  have hudisk : u ∈ disk := by
    simpa only [disk, Metric.mem_ball, dist_zero_right] using hu.trans_lt hq
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf (Metric.mem_ball_self hR)
  have h := schlicht_deriv_compact_bound (ballNormalize_schlicht hR hf hn) hq hu
  rw [(ballNormalize_deriv hR hf.1 hudisk).deriv] at h
  have heq : a + (R : ℂ) * u = z := by
    dsimp only [u]
    have hRc : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR.ne'
    field_simp
    ring
  rw [heq, norm_div] at h
  exact (div_le_iff₀ (norm_pos_iff.2 hn)).1 h

/-- A uniform degree-four inverse derivative bound holds on both tails of
the actual interior contour. -/
theorem exists_uniform_inverse_deriv_contour_tail_bound :
    ∃ T : ℝ, 0 < T ∧ ∀ (m : NormalizedModel) (t : ℝ), T ≤ |t| →
      ‖deriv m.inverse (imageContour t)‖ ≤
        3936600 * Real.exp (-1) * (max |t| 1) ^ 4 := by
  obtain ⟨T, hT, hdisks⟩ := imageContour_tail_disks
  refine ⟨T, by linarith, ?_⟩
  intro m t ht
  obtain ⟨hR, hball, hrelative⟩ := hdisks t ht
  have hf : UnivalentOn m.inverse
      (Metric.ball (1 + (t : ℂ) * I) ((27 / 2) * Real.posLog |t|)) :=
    ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
  have h := norm_deriv_le_of_univalent_ball hR hf
    (by norm_num : (26 / 27 : ℝ) < 1) hrelative
  norm_num at h
  calc
    _ ≤ 39366 * ‖deriv m.inverse (1 + (t : ℂ) * I)‖ := h
    _ ≤ 39366 * (100 * Real.exp (-1) * (max |t| 1) ^ 4) :=
      mul_le_mul_of_nonneg_left (m.norm_inverse_deriv_vertical_le t) (by norm_num)
    _ = _ := by ring

#print axioms imageContour_tail_disks
#print axioms norm_deriv_le_of_univalent_ball
#print axioms exists_uniform_inverse_deriv_contour_tail_bound

end MaxModulusPoints.CauchyApproximation
