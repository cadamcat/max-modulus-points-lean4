module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CauchyApproximation.ContourGrowth
public import MaxModulusPoints.CauchyApproximation.ExponentialAdapter
public import MaxModulusPoints.CauchyApproximation.InverseDistortion
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# Quadratic inverse growth on the positive real axis

Upper-half-plane univalent growth and the omitted origin control inverse
values on the positive real axis by a universal quadratic bound. The
exponential correspondence gives the same estimate in logarithmic
coordinates.
-/


@[expose] public section

open Complex Set
open OAI.Brennan

namespace MaxModulusPoints.CauchyApproximation

/-- The normalized planar inverse has at most quadratic growth on the
positive real axis beyond its normalization point. -/
theorem NormalizedModel.norm_inverse_real_le (m : NormalizedModel) {R : ℝ}
    (hR : 1 ≤ R) :
    ‖m.inverse (R : ℂ)‖ ≤ 65 * Real.exp (-1) * R ^ 2 := by
  let f : ℂ → ℂ := fun w => m.inverse (-I * w)
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
    have hlin : HasDerivAt (fun w : ℂ => -I * w) (-I) w := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id w).const_mul (-I)
    exact (m.holomorphic_inverse.differentiableAt
      (hH.mem_nhds (hmem hw))).hasDerivAt.comp w hlin
  have hu : UnivalentOn f halfPlane := by
    refine ⟨fun w hw => (hd hw).differentiableAt.differentiableWithinAt, ?_⟩
    intro w hw v hv he
    exact mul_left_cancel₀ (by simp : (-I : ℂ) ≠ 0)
      (m.univalentOn_inverse.2 (hmem hw) (hmem hv) he)
  have hI : I ∈ halfPlane := by simp [halfPlane]
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let z : ℂ := (R : ℂ) * I
  have hz : z ∈ halfPlane := by simpa [z, halfPlane] using hRpos
  have hzval : -I * z = (R : ℂ) := by simp [z, mul_left_comm]
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
  have hnorm : ‖z + I‖ = R + 1 := by
    have heq : z + I = ((R + 1 : ℝ) : ℂ) * I := by
      dsimp only [z]
      push_cast
      ring
    rw [heq, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have him : z.im = R := by simp [z]
  rw [hnorm, him] at hb
  simp only [neg_mul, I_mul_I, neg_neg] at hb
  have hfour : (R + 1) ^ 4 ≤ 16 * R ^ 4 := by
    calc
      _ ≤ (2 * R) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      _ = _ := by ring
  have hsub : ‖m.inverse (R : ℂ) - m.inverse 1‖ ≤
      64 * Real.exp (-1) * R ^ 2 := by
    apply le_trans hb
    apply (div_le_iff₀ (sq_pos_of_pos hRpos)).mpr
    have hmul := mul_le_mul m.norm_inverse_deriv_one_le hfour
      (by positivity) (by positivity : 0 ≤ 4 * Real.exp (-1))
    nlinarith only [hmul]
  have htri := norm_add_le (m.inverse (R : ℂ) - m.inverse 1) (m.inverse 1)
  rw [sub_add_cancel, hbase] at htri
  have hsq : 1 ≤ R ^ 2 := one_le_pow₀ hR
  nlinarith [mul_le_mul_of_nonneg_left hsq (Real.exp_pos (-1)).le]

/-- One quadratic coefficient controls the exponential of every normalized
logarithmic inverse on positive real target values. -/
theorem logModel_exp_inverse_real_le (V : Set ℂ) (G : Blueprint.LogModel V)
    {R : ℝ} (hR : 1 ≤ R) :
    ‖Complex.exp (G.invFun (R : ℂ))‖ ≤ 65 * Real.exp (-1) * R ^ 2 := by
  obtain ⟨m, _, _, hinverse, _⟩ := logModelAdapter V G
  have hmem : (R : ℂ) ∈ modelHalfPlane := by
    simpa [modelHalfPlane] using (zero_lt_one.trans_le hR)
  rw [← hinverse _ hmem]
  exact m.norm_inverse_real_le hR

#print axioms NormalizedModel.norm_inverse_real_le
#print axioms logModel_exp_inverse_real_le

end MaxModulusPoints.CauchyApproximation
