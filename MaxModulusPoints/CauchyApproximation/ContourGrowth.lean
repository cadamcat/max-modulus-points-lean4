module

public import OAI.Analysis.IntegralMeans.TraceBounds
public import MaxModulusPoints.CauchyApproximation.CanonicalDensity
public import MaxModulusPoints.CauchyApproximation.CircleCorrection
public import MaxModulusPoints.CauchyApproximation.ContourDerivative
public import MaxModulusPoints.CauchyApproximation.ContourDistortion
public import MaxModulusPoints.CauchyApproximation.InverseDistortion
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.UniformBounds

/-!
# Quartic position growth of the canonical contour

Sharp disk value growth, transported by a Cayley map, bounds inverse values
on the line of real part one. Omission of zero gives a relative-radius value
comparison on the disks joining that line to the canonical contour. Together
with compact bounds on the remaining interval, these estimates give one
quartic position bound for all normalized inverse conformal maps.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Sharp disk growth gives a quartic value bound after Cayley transport. -/
theorem halfPlaneSchlicht_norm_value_le {f : ℂ → ℂ} (hf : HalfPlaneSchlicht f)
    {z : ℂ} (hz : z ∈ halfPlane) :
    ‖f z‖ ≤ ‖z + I‖ ^ 4 / z.im ^ 2 := by
  let F := halfToDisk f
  have hF : Schlicht F := halfToDisk_schlicht hf
  let r : ℝ := ‖diskCayley z‖
  let D : ℝ := ‖z + I‖ ^ 2
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := by
    simpa only [r, disk, Metric.mem_ball, dist_zero_right] using diskCayley_maps hz
  have hy : 0 < z.im := hz
  have hnorm : ‖f z‖ = 2 * ‖F (diskCayley z)‖ := by
    rw [← diskToHalf_halfToDisk (f := f) hz]
    simp only [diskToHalf, norm_mul, norm_ofNat, norm_I, mul_one, F]
  have hb : ‖f z‖ * (1 - r) ^ 2 ≤ 2 := by
    have h := (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - r))).1
      (schlicht_growth_upper hF (diskCayley_maps hz))
    change ‖F (diskCayley z)‖ * (1 - r) ^ 2 ≤ r at h
    rw [hnorm]
    nlinarith
  have he : (1 - r ^ 2) * D = 4 * z.im := by
    dsimp only [r, D]
    rw [diskCayley, norm_div, div_pow]
    field_simp [norm_ne_zero_iff.2 (cayley_den_ne_zero hz)]
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im,
      add_zero, sub_zero]
    ring
  have hc : (1 - r) ^ 2 * (1 + r) ^ 2 * D ^ 2 = 16 * z.im ^ 2 := by
    calc
      _ = ((1 - r ^ 2) * D) ^ 2 := by ring
      _ = (4 * z.im) ^ 2 := by rw [he]
      _ = _ := by ring
  have hfour : (1 + r) ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + r)
      (by linarith : 1 + r ≤ 2) 2
    norm_num at h
    exact h
  have hmul : ‖f z‖ * ((1 - r) ^ 2 * (1 + r) ^ 2 * D ^ 2) ≤ 8 * D ^ 2 := by
    calc
      _ = (‖f z‖ * (1 - r) ^ 2) * ((1 + r) ^ 2 * D ^ 2) := by ring
      _ ≤ 2 * ((1 + r) ^ 2 * D ^ 2) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ 8 * D ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hfour (sq_nonneg D)]
  rw [hc] at hmul
  rw [le_div_iff₀ (sq_pos_of_pos hy)]
  rw [show ‖z + I‖ ^ 4 = D ^ 2 by dsimp only [D]; ring]
  nlinarith [sq_nonneg D]

/-- Undoing the half-plane normalization retains the center derivative. -/
theorem univalent_halfPlane_norm_sub_value_le {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {z : ℂ} (hz : z ∈ halfPlane) :
    ‖f z - f I‖ ≤ ‖deriv f I‖ * ‖z + I‖ ^ 4 / z.im ^ 2 := by
  have hI : I ∈ halfPlane := by simp [halfPlane]
  have hn : 0 < ‖deriv f I‖ :=
    norm_pos_iff.2 (univalent_deriv_ne_zero isOpen_halfPlane hf hI)
  have hb := halfPlaneSchlicht_norm_value_le (reroot_normalized hf hI) hz
  simp only [reroot, I_affine, I_im, ofReal_one, one_mul, norm_div] at hb
  have h := (div_le_iff₀ hn).1 hb
  calc
    _ ≤ (‖z + I‖ ^ 4 / z.im ^ 2) * ‖deriv f I‖ := h
    _ = _ := by ring

/-- The normalized inverse maps have one quartic value bound on the vertical line. -/
theorem NormalizedModel.norm_inverse_vertical_le (m : NormalizedModel) (t : ℝ) :
    ‖m.inverse (1 + (t : ℂ) * I)‖ ≤
      101 * Real.exp (-1) * (max |t| 1) ^ 4 := by
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
    exact (m.holomorphic_inverse.differentiableAt (hH.mem_nhds (hmem hw))).hasDerivAt.comp w hlin
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
  have hdf : ‖deriv f I‖ = ‖deriv m.inverse 1‖ := by
    rw [(hd hI).deriv, norm_mul]
    simp only [neg_mul, I_mul_I, neg_neg, norm_neg, norm_I, mul_one]
  have hbase : ‖m.inverse 1‖ = Real.exp (-1) := by
    have hi : m.inverse 1 = Complex.exp (-1) := by
      simpa only [m.base_value] using m.left_inverse _ m.base_mem
    rw [hi, Complex.norm_exp]
    norm_num
  have hb := univalent_halfPlane_norm_sub_value_le hu hz
  change ‖m.inverse (-I * z) - m.inverse (-I * I)‖ ≤ _ at hb
  rw [hzval, hdf] at hb
  have hfour : ‖z + I‖ ^ 4 = (t ^ 2 + 4) ^ 2 := by
    have hsq : ‖z + I‖ ^ 2 = t ^ 2 + 4 := by
      rw [Complex.sq_norm]
      simp only [z, Complex.normSq_apply, add_re, add_im, neg_re, neg_im,
        ofReal_re, ofReal_im, I_re, I_im, add_zero, zero_add, neg_zero]
      ring
    calc
      _ = (‖z + I‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [hfour] at hb
  simp only [neg_mul, I_mul_I, neg_neg, z, add_im, neg_im, ofReal_im, neg_zero,
    I_im, zero_add, one_pow, div_one] at hb
  have htsq : t ^ 2 ≤ (max |t| 1) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) (le_max_left |t| 1) 2
  have hr2 : 1 ≤ (max |t| 1) ^ 2 := one_le_pow₀ (le_max_right _ _)
  have hp : (t ^ 2 + 4) ^ 2 ≤ 25 * (max |t| 1) ^ 4 := by
    calc
      _ ≤ (5 * (max |t| 1) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = _ := by ring
  have hsub : ‖m.inverse (1 + (t : ℂ) * I) - m.inverse 1‖ ≤
      100 * Real.exp (-1) * (max |t| 1) ^ 4 := by
    calc
      _ ≤ ‖deriv m.inverse 1‖ * (t ^ 2 + 4) ^ 2 := hb
      _ ≤ (4 * Real.exp (-1)) * (25 * (max |t| 1) ^ 4) :=
        mul_le_mul m.norm_inverse_deriv_one_le hp (by positivity) (by positivity)
      _ = _ := by ring
  have ht := norm_add_le (m.inverse (1 + (t : ℂ) * I) - m.inverse 1) (m.inverse 1)
  rw [sub_add_cancel, hbase] at ht
  have hr4 : 1 ≤ (max |t| 1) ^ 4 := one_le_pow₀ (le_max_right _ _)
  nlinarith [mul_le_mul_of_nonneg_left hr4 (Real.exp_pos (-1)).le]

/-- At any fixed relative radius, omission of zero compares values uniformly. -/
theorem norm_value_le_of_univalent_ball_omit_zero_relative {f : ℂ → ℂ}
    {a z : ℂ} {R q : ℝ} (hR : 0 < R) (hf : UnivalentOn f (Metric.ball a R))
    (hzero : ∀ w ∈ Metric.ball a R, f w ≠ 0) (hq : q < 1)
    (hz : ‖z - a‖ ≤ q * R) :
    ‖f z‖ ≤ (1 + 8 * q / (1 - q) ^ 3) * ‖f a‖ := by
  let u : ℂ := (z - a) / (R : ℂ)
  have hu : ‖u‖ ≤ q := by
    dsimp only [u]
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (div_le_iff₀ hR).2 hz
  have hq0 : 0 ≤ q := (norm_nonneg u).trans hu
  have hqpos : 0 < 1 - q := sub_pos.2 hq
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf (Metric.mem_ball_self hR)
  let K : ℝ := (2 / (1 - q) ^ 3) * q
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hb := schlicht_local_bound (ballNormalize_schlicht hR hf hn) hq hu
  have heq : a + (R : ℂ) * u = z := by
    dsimp only [u]
    field_simp [ofReal_ne_zero.2 hR.ne']
    ring
  change ‖(f (a + (R : ℂ) * u) - f a) / ((R : ℂ) * deriv f a)‖ ≤ K at hb
  rw [heq, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hR] at hb
  have hdist := (div_le_iff₀ (mul_pos hR (norm_pos_iff.2 hn))).1 hb
  have hd := (le_div_iff₀ hR).1 (norm_deriv_le_of_univalent_ball_omit_zero hR hf hzero)
  have ht := norm_add_le (f z - f a) (f a)
  rw [sub_add_cancel] at ht
  have hd' : R * ‖deriv f a‖ ≤ 4 * ‖f a‖ := by nlinarith [hd]
  have hk := mul_le_mul_of_nonneg_left hd' hK
  calc
    _ ≤ ‖f z - f a‖ + ‖f a‖ := ht
    _ ≤ K * (4 * ‖f a‖) + ‖f a‖ := add_le_add (hdist.trans hk) le_rfl
    _ = _ := by dsimp only [K]; ring

/-- One quartic coefficient bounds the actual canonical contour for all maps. -/
theorem exists_uniform_contour_position_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m : NormalizedModel) (t : ℝ),
      ‖m.contour t‖ ≤ A * (max |t| 1) ^ 4 := by
  obtain ⟨T, hT, hdisks⟩ := imageContour_tail_disks
  have hK : IsCompact (imageContour '' Icc (-T) T) :=
    isCompact_Icc.image lipschitzWith_imageContour.continuous
  obtain ⟨B, hB, hcompact⟩ := exists_uniform_inverse_bounds_on_compact hK
    (by rintro _ ⟨t, _, rfl⟩; exact imageContour_mem_modelHalfPlane t)
  let C : ℝ := 151633 * (101 * Real.exp (-1))
  let A : ℝ := max 1 (max C B)
  refine ⟨A, le_max_left _ _, ?_⟩
  intro m t
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  by_cases ht : T ≤ |t|
  · obtain ⟨hR, hball, hrelative⟩ := hdisks t ht
    have hf : UnivalentOn m.inverse
        (Metric.ball (1 + (t : ℂ) * I) ((27 / 2) * Real.posLog |t|)) :=
      ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
    have hb := norm_value_le_of_univalent_ball_omit_zero_relative hR hf
      (fun w hw he ↦ m.zero_not_mem (he ▸ m.inverse_mem (hball hw)))
      (by norm_num : (26 / 27 : ℝ) < 1) hrelative
    norm_num at hb
    calc
      _ ≤ 151633 * ‖m.inverse (1 + (t : ℂ) * I)‖ := hb
      _ ≤ 151633 * (101 * Real.exp (-1) * (max |t| 1) ^ 4) :=
        mul_le_mul_of_nonneg_left (m.norm_inverse_vertical_le t) (by norm_num)
      _ = C * (max |t| 1) ^ 4 := by dsimp only [C]; ring
      _ ≤ A * (max |t| 1) ^ 4 := mul_le_mul_of_nonneg_right
        ((le_max_left C B).trans (le_max_right 1 _)) (by positivity)
  · have hmid : t ∈ Icc (-T) T := abs_le.1 (le_of_lt (lt_of_not_ge ht))
    have hp : 1 ≤ (max |t| 1) ^ 4 := one_le_pow₀ (le_max_right _ _)
    calc
      _ ≤ B := (hcompact m (imageContour t) ⟨t, hmid, rfl⟩).1
      _ ≤ A := (le_max_right C B).trans (le_max_right 1 _)
      _ ≤ A * (max |t| 1) ^ 4 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hA.le

#print axioms halfPlaneSchlicht_norm_value_le
#print axioms univalent_halfPlane_norm_sub_value_le
#print axioms NormalizedModel.norm_inverse_vertical_le
#print axioms norm_value_le_of_univalent_ball_omit_zero_relative
#print axioms exists_uniform_contour_position_bound

end MaxModulusPoints.CauchyApproximation
