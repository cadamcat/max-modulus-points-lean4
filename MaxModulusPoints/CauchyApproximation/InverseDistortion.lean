module

public import OAI.Analysis.IntegralMeans.HalfPlane
public import MaxModulusPoints.CauchyApproximation.ContourDerivative
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# Inverse derivative bounds on a vertical line

Koebe distortion on the disk, transported by a Cayley map, gives a
degree-four derivative bound on the line of real part one. The omitted
origin and the prescribed value at one control the normalization constant
by the quarter theorem. These estimates provide the first part of the
conformal distortion argument for the canonical interior contour.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Cayley transport of disk distortion bounds the derivative of a normalized
univalent map on the upper half-plane. -/
theorem halfPlaneSchlicht_norm_deriv_le {f : ℂ → ℂ} (hf : HalfPlaneSchlicht f)
    {z : ℂ} (hz : z ∈ halfPlane) :
    ‖deriv f z‖ ≤ ‖z + I‖ ^ 4 / z.im ^ 3 := by
  let F := halfToDisk f
  have hF : Schlicht F := halfToDisk_schlicht hf
  let r : ℝ := ‖diskCayley z‖
  let D : ℝ := ‖z + I‖ ^ 2
  let a : ℝ := ‖deriv F (diskCayley z)‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := by
    simpa only [r, disk, Metric.mem_ball, dist_zero_right] using (diskCayley_maps hz)
  have hD : 0 < D := sq_pos_of_ne_zero (norm_ne_zero_iff.2 (cayley_den_ne_zero hz))
  have hy : 0 < z.im := hz
  have he : (1 - r ^ 2) * D = 4 * z.im := by
    dsimp only [r, D]
    rw [diskCayley, norm_div, div_pow]
    field_simp [norm_ne_zero_iff.2 (cayley_den_ne_zero hz)]
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im,
      add_zero, sub_zero]
    ring
  have hnorm : ‖deriv f z‖ = 4 * a / D := by
    have heq : EqOn (diskToHalf F) f halfPlane := fun w hw ↦ diskToHalf_halfToDisk hw
    rw [← heq.deriv isOpen_halfPlane hz, (hasDerivAt_diskToHalf hF.1.1 hz).deriv]
    simp only [norm_div, norm_mul, norm_neg, norm_pow, norm_ofNat, a, D]
  have hb : a * (1 - r) ^ 3 ≤ 1 + r := by
    exact (le_div_iff₀ (pow_pos (by linarith : 0 < 1 - r) 3)).1
      (schlicht_deriv_bounds hF (diskCayley_maps hz)).2
  have hc : (1 - r) ^ 3 * (1 + r) ^ 3 * D ^ 3 = 64 * z.im ^ 3 := by
    calc
      _ = ((1 - r ^ 2) * D) ^ 3 := by ring
      _ = (4 * z.im) ^ 3 := by rw [he]
      _ = _ := by ring
  have h16 : (1 + r) ^ 4 ≤ 16 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + r)
      (by linarith : 1 + r ≤ 2) 4
    norm_num at h
    exact h
  have hmul : a * ((1 - r) ^ 3 * (1 + r) ^ 3 * D ^ 3) ≤ (1 + r) ^ 4 * D ^ 3 := by
    calc
      _ = (a * (1 - r) ^ 3) * ((1 + r) ^ 3 * D ^ 3) := by ring
      _ ≤ (1 + r) * ((1 + r) ^ 3 * D ^ 3) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  rw [hc] at hmul
  have hlast := hmul.trans (mul_le_mul_of_nonneg_right h16 (pow_nonneg hD.le 3))
  rw [hnorm]
  rw [show ‖z + I‖ ^ 4 = D ^ 2 by dsimp only [D]; ring]
  rw [div_le_div_iff₀ hD (pow_pos hy 3)]
  nlinarith [hlast]

/-- The derivative bound on the upper half-plane, with its normalization
expressed by the actual derivative at the point `I`. -/
theorem univalent_halfPlane_norm_deriv_le {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) :
    ‖deriv f z‖ ≤ ‖deriv f I‖ * ‖z + I‖ ^ 4 / z.im ^ 3 := by
  have hI : I ∈ halfPlane := by change 0 < (I : ℂ).im; norm_num
  have hn : 0 < ‖deriv f I‖ :=
    norm_pos_iff.2 (univalent_deriv_ne_zero isOpen_halfPlane hf hI)
  have hb := halfPlaneSchlicht_norm_deriv_le (reroot_normalized hf hI) hz
  rw [deriv_reroot hf hI hz, I_affine, norm_div] at hb
  have h := (div_le_iff₀ hn).1 hb
  calc
    _ ≤ (‖z + I‖ ^ 4 / z.im ^ 3) * ‖deriv f I‖ := h
    _ = _ := by ring

/-- The inverse conformal map is univalent on its target domain. -/
theorem NormalizedModel.univalentOn_inverse (m : NormalizedModel) :
    UnivalentOn m.inverse modelHalfPlane := by
  refine ⟨m.holomorphic_inverse, ?_⟩
  intro z hz w hw he
  simpa only [m.right_inverse z hz, m.right_inverse w hw] using congrArg m.forward he

/-- Omission of the origin bounds the derivative at the normalization point. -/
theorem NormalizedModel.norm_inverse_deriv_one_le (m : NormalizedModel) :
    ‖deriv m.inverse 1‖ ≤ 4 * Real.exp (-1) := by
  have hball : Metric.ball (1 : ℂ) 1 ⊆ modelHalfPlane := by
    intro w hw
    have hw' : ‖w - 1‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hneg := ((neg_le_abs (w - 1).re).trans (Complex.abs_re_le_norm (w - 1))).trans_lt hw'
    change -14 * Real.posLog |w.im| < w.re
    simp only [sub_re, one_re] at hneg
    nlinarith [Real.posLog_nonneg (x := |w.im|)]
  have hu : UnivalentOn m.inverse (Metric.ball 1 1) :=
    ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
  have hquarter := univalent_ball_quarter (by norm_num : (0 : ℝ) < 1) hu
  have hnorm : ‖m.inverse 1‖ = Real.exp (-1) := by
    have hi : m.inverse 1 = Complex.exp (-1) := by
      simpa only [m.base_value] using m.left_inverse _ m.base_mem
    rw [hi, Complex.norm_exp]
    norm_num
  have hb : ‖deriv m.inverse 1‖ / 4 ≤ ‖m.inverse 1‖ := by
    by_contra! h
    have hz : (0 : ℂ) ∈ Metric.ball (m.inverse 1) (1 * ‖deriv m.inverse 1‖ / 4) := by
      simpa only [Metric.mem_ball, dist_zero_left, one_mul] using h
    obtain ⟨w, hw, he⟩ := hquarter hz
    exact m.zero_not_mem (he ▸ m.inverse_mem (hball hw))
  rw [hnorm] at hb
  linarith

/-- A uniform degree-four inverse derivative bound on the line of real part one. -/
theorem NormalizedModel.norm_inverse_deriv_vertical_le (m : NormalizedModel) (t : ℝ) :
    ‖deriv m.inverse (1 + (t : ℂ) * I)‖ ≤
      100 * Real.exp (-1) * (max |t| 1) ^ 4 := by
  let f : ℂ → ℂ := fun w ↦ m.inverse (-I * w)
  have hmem {w : ℂ} (hw : w ∈ halfPlane) : -I * w ∈ modelHalfPlane := by
    change -14 * Real.posLog |(-I * w).im| < (-I * w).re
    simp only [mul_re, mul_im, neg_re, neg_im, I_re, I_im, zero_mul,
      neg_mul, one_mul, zero_sub, zero_add, neg_neg, abs_neg]
    have hw' : 0 < w.im := hw
    nlinarith [Real.posLog_nonneg (x := |w.re|)]
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hd {w : ℂ} (hw : w ∈ halfPlane) :
      HasDerivAt f (deriv m.inverse (-I * w) * (-I)) w := by
    have hlin : HasDerivAt (fun w : ℂ ↦ -I * w) (-I) w := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id w).const_mul (-I)
    exact (m.holomorphic_inverse.differentiableAt (hH.mem_nhds (hmem hw))).hasDerivAt.comp w
      hlin
  have hu : UnivalentOn f halfPlane := by
    refine ⟨fun w hw ↦ (hd hw).differentiableAt.differentiableWithinAt, ?_⟩
    intro w hw v hv he
    exact mul_left_cancel₀ (by simp : (-I : ℂ) ≠ 0)
      (m.univalentOn_inverse.2 (hmem hw) (hmem hv) he)
  let z : ℂ := -(t : ℂ) + I
  have hz : z ∈ halfPlane := by simp [z, halfPlane]
  have hI : I ∈ halfPlane := by simp [halfPlane]
  have hzval : -I * z = 1 + (t : ℂ) * I := by
    dsimp only [z]
    ring_nf
    simp only [I_sq]
    ring
  have hnorm (w : ℂ) (hw : w ∈ halfPlane) :
      ‖deriv f w‖ = ‖deriv m.inverse (-I * w)‖ := by
    rw [(hd hw).deriv, norm_mul]
    simp only [norm_neg, norm_I, mul_one]
  have hb := univalent_halfPlane_norm_deriv_le hu hz
  rw [hnorm z hz, hnorm I hI, hzval] at hb
  have hsq : ‖z + I‖ ^ 2 = t ^ 2 + 4 := by
    rw [Complex.sq_norm]
    simp only [z, Complex.normSq_apply, add_re, add_im, neg_re, neg_im,
      ofReal_re, ofReal_im, I_re, I_im, add_zero, zero_add, neg_zero]
    ring
  have hfour : ‖z + I‖ ^ 4 = (t ^ 2 + 4) ^ 2 := by
    calc
      _ = (‖z + I‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  simp only [neg_mul, I_mul_I, neg_neg, z, add_im, neg_im, ofReal_im, neg_zero,
    I_im, zero_add, one_pow, div_one] at hb
  rw [show ‖-(t : ℂ) + I + I‖ ^ 4 = (t ^ 2 + 4) ^ 2 from hfour] at hb
  have hr : 1 ≤ max |t| 1 := le_max_right _ _
  have htsq : t ^ 2 ≤ (max |t| 1) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) (le_max_left |t| 1) 2
  have hr2 : 1 ≤ (max |t| 1) ^ 2 := one_le_pow₀ hr
  have hp : (t ^ 2 + 4) ^ 2 ≤ 25 * (max |t| 1) ^ 4 := by
    calc
      _ ≤ (5 * (max |t| 1) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = _ := by ring
  calc
    _ ≤ ‖deriv m.inverse 1‖ * (t ^ 2 + 4) ^ 2 := hb
    _ ≤ (4 * Real.exp (-1)) * (25 * (max |t| 1) ^ 4) :=
      mul_le_mul m.norm_inverse_deriv_one_le hp (by positivity) (by positivity)
    _ = _ := by ring

#print axioms halfPlaneSchlicht_norm_deriv_le
#print axioms univalent_halfPlane_norm_deriv_le
#print axioms NormalizedModel.univalentOn_inverse
#print axioms NormalizedModel.norm_inverse_deriv_one_le
#print axioms NormalizedModel.norm_inverse_deriv_vertical_le

end MaxModulusPoints.CauchyApproximation
