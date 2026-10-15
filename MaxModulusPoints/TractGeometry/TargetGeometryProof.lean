import Mathlib.Analysis.Convex.Contractible
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.TargetGeometry
noncomputable section

namespace MaxModulusPoints.TractGeometry

open Set Blueprint

private theorem positive_log_abs (y : ℝ) :
    max 0 (Real.log |y|) = Real.log (max 1 |y|) := by
  by_cases h : |y| ≤ 1
  · rw [max_eq_left h, Real.log_one,
      max_eq_left (Real.log_nonpos (abs_nonneg y) h)]
  · have h' : 1 ≤ |y| := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h', max_eq_right (Real.log_nonneg h')]

private def boundaryHeight (y : ℝ) : ℝ := 14 * max 0 (Real.log |y|)

private theorem continuous_boundaryHeight : Continuous boundaryHeight := by
  have h : Continuous (fun y : ℝ => Real.log (max 1 |y|)) :=
    (continuous_const.max continuous_abs).log fun y =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 |y|))
  change Continuous (fun y : ℝ => 14 * max 0 (Real.log |y|))
  simp_rw [positive_log_abs]
  exact h.const_mul 14

private def flattenTarget : ℂ ≃ₜ ℂ where
  toFun z := z + (boundaryHeight z.im : ℂ)
  invFun z := z - (boundaryHeight z.im : ℂ)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_id.add
    (Complex.continuous_ofReal.comp (continuous_boundaryHeight.comp Complex.continuous_im))
  continuous_invFun := continuous_id.sub
    (Complex.continuous_ofReal.comp (continuous_boundaryHeight.comp Complex.continuous_im))

private theorem target_eq_preimage :
    target = flattenTarget ⁻¹' {z : ℂ | 0 < z.re} := by
  ext z
  change -14 * max 0 (Real.log |z.im|) < z.re ↔
    0 < (z + (boundaryHeight z.im : ℂ)).re
  simp only [Complex.add_re, Complex.ofReal_re, boundaryHeight]
  constructor <;> intro h <;> linarith

theorem target_geometry : TargetGeometry := by
  have hc : Convex ℝ {z : ℂ | 0 < z.re} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hn : ({z : ℂ | 0 < z.re} : Set ℂ).Nonempty := ⟨1, by norm_num⟩
  have hs : IsSimplyConnected ({z : ℂ | 0 < z.re} : Set ℂ) := by
    let := hc.contractibleSpace hn
    exact SimplyConnectedSpace.ofContractible _
  have ht : IsSimplyConnected target := by
    rw [target_eq_preimage]
    exact flattenTarget.isSimplyConnected_preimage.mpr hs
  refine ⟨?_, ht.isPathConnected.isConnected, ht, ?_, ?_, ?_⟩
  · rw [target_eq_preimage]
    exact (isOpen_lt continuous_const Complex.continuous_re).preimage
      flattenTarget.continuous
  · norm_num [target]
  · norm_num [target]
  · intro z hz
    simpa only [target, mem_ofPred_eq, Complex.star_def, Complex.conj_im,
      Complex.conj_re, abs_neg] using hz

end MaxModulusPoints.TractGeometry
