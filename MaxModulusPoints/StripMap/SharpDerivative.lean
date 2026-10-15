import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.StripMap.ExponentialChart
import MaxModulusPoints.StripMap.Geometry
import MaxModulusPoints.StripMap.Growth
import MaxModulusPoints.StripMap.KernelGeometry
import MaxModulusPoints.StripMap.RealDerivative
import MaxModulusPoints.StripMap.Rescaling
import MaxModulusPoints.StripMap.Symmetry
/-!
# A sharp lower bound for the logarithmic derivative

Every rescaled target contains the right half-plane. Its inverse conformal
map therefore gives a disc self-map fixing the origin. Schwarz's lemma
provides the sharp lower bound π for the real logarithmic derivative.
-/

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

def inverseRescaledMap (e : ConformalEquivalence strip target) (b : ℝ) (w : ℂ) : ℂ :=
  e.invFun (e.toFun b * w) - b

theorem inverseRescaledMap_mapsTo (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℝ) :
    MapsTo (inverseRescaledMap e b) rightHalfPlane strip := by
  intro w hw
  have hp := normalized_equivalence_positive_real e he0 hepos hereal b
  have hv : e.toFun b = ((e.toFun b).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.2)
  have ht : e.toFun b * w ∈ target := by
    rw [hv]
    exact halfPlane_subset_scaledTarget hp.1 hw
  have hs := e.inverse_mapsTo ht
  simpa only [inverseRescaledMap, strip, mem_ofPred_eq, Complex.sub_im,
    Complex.ofReal_im, sub_zero] using hs

theorem inverseRescaledMap_differentiableOn (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℝ) :
    DifferentiableOn ℂ (inverseRescaledMap e b) rightHalfPlane := by
  apply (e.inverse_holomorphic.comp
    (differentiable_const (e.toFun b) |>.mul differentiable_id).differentiableOn ?_).sub_const
  intro w hw
  have hp := normalized_equivalence_positive_real e he0 hepos hereal b
  have hv : e.toFun b = ((e.toFun b).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.2)
  change e.toFun b * w ∈ target
  rw [hv]
  exact halfPlane_subset_scaledTarget hp.1 hw

theorem inverseRescaledMap_one (e : ConformalEquivalence strip target) (b : ℝ) :
    inverseRescaledMap e b 1 = 0 := by
  rw [inverseRescaledMap, mul_one, e.left_inv b (real_mem_strip b), sub_self]

theorem inverseRescaledMap_hasDerivAt_one (e : ConformalEquivalence strip target) (b : ℝ) :
    HasDerivAt (inverseRescaledMap e b) (e.toFun b / deriv e.toFun b) 1 := by
  have hm := inverse_derivative_mul e (real_mem_strip b)
  have hn : deriv e.toFun b ≠ 0 := by intro h; simp only [h, mul_zero, zero_ne_one] at hm
  have hi : deriv e.invFun (e.toFun b) = (deriv e.toFun b)⁻¹ := by
    calc
      deriv e.invFun (e.toFun b) =
          (deriv e.invFun (e.toFun b) * deriv e.toFun b) * (deriv e.toFun b)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
      _ = (deriv e.toFun b)⁻¹ := by rw [hm, one_mul]
  have hd := (e.inverse_holomorphic.differentiableAt
    (isOpen_target.mem_nhds (e.mapsTo (real_mem_strip b)))).hasDerivAt
  have hc : HasDerivAt (fun w : ℂ => e.toFun b * w) (e.toFun b) 1 := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id (1 : ℂ)).const_mul (e.toFun b)
  have hd' : HasDerivAt e.invFun (deriv e.invFun (e.toFun b))
      ((fun w : ℂ => e.toFun b * w) 1) := by simpa only [mul_one] using hd
  have hcomp := (hd'.comp (1 : ℂ) hc).sub_const (b : ℂ)
  change HasDerivAt (fun w : ℂ => e.invFun (e.toFun b * w) - b) _ _
  simpa only [Function.comp_def, hi, div_eq_mul_inv, mul_comm] using hcomp

theorem rescaledMap_hasDerivAt_zero (e : ConformalEquivalence strip target) (b : ℝ) :
    HasDerivAt (rescaledMap e b) (deriv e.toFun b / e.toFun b) 0 := by
  have hd : HasDerivAt e.toFun (deriv e.toFun b) ((b : ℂ) + 0) := by
    simpa only [add_zero] using (e.holomorphic.differentiableAt
      (isOpen_strip.mem_nhds (real_mem_strip b))).hasDerivAt
  have hc := (hasDerivAt_id (0 : ℂ)).const_add (b : ℂ)
  change HasDerivAt (fun z : ℂ => e.toFun ((b : ℂ) + z) / e.toFun b) _ _
  simpa only [Function.comp_def, mul_one, id_eq] using (hd.comp 0 hc).div_const (e.toFun b)

theorem normalized_equivalence_log_derivative_ge_pi (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℝ) :
    Real.pi ≤ (deriv e.toFun b).re / (e.toFun b).re := by
  let h : ℂ → ℂ := fun w => stripToDisc (inverseRescaledMap e b (discToHalf w))
  have hzero : h 0 = 0 := by simp only [h, discToHalf_zero, inverseRescaledMap_one,
    stripToDisc_zero]
  have hmaps : MapsTo h (ball 0 1) (ball 0 1) :=
    stripToDisc_mapsTo.comp
      ((inverseRescaledMap_mapsTo e he0 hepos hereal b).comp discToHalf_mapsTo)
  have hd : DifferentiableOn ℂ h (ball 0 1) :=
    stripToDisc_differentiableOn.comp
      ((inverseRescaledMap_differentiableOn e he0 hepos hereal b).comp
        discToHalf_differentiableOn discToHalf_mapsTo)
      ((inverseRescaledMap_mapsTo e he0 hepos hereal b).comp discToHalf_mapsTo)
  have hbound := Complex.norm_deriv_le_one_of_mapsTo_ball hd
    (by simpa only [hzero] using (hmaps.mono_right ball_subset_closedBall)) (by norm_num)
  have hc : HasDerivAt (fun w => inverseRescaledMap e b (discToHalf w))
      (e.toFun b / deriv e.toFun b * 2) 0 := by
    have hh : HasDerivAt (inverseRescaledMap e b) (e.toFun b / deriv e.toFun b)
        (discToHalf 0) := by rw [discToHalf_zero]; exact inverseRescaledMap_hasDerivAt_one e b
    exact hh.comp 0 discToHalf_hasDerivAt_zero
  have hh : HasDerivAt stripToDisc (Real.pi / 2) (inverseRescaledMap e b (discToHalf 0)) := by
    rw [discToHalf_zero, inverseRescaledMap_one]
    exact stripToDisc_hasDerivAt_zero
  have hdvalue : deriv h 0 = (Real.pi : ℂ) * (e.toFun b / deriv e.toFun b) := by
    convert (hh.comp 0 hc).deriv using 1 <;> first | rfl | ring
  rw [hdvalue, norm_mul, norm_div] at hbound
  have hp := normalized_equivalence_positive_real e he0 hepos hereal b
  have hdp := normalized_equivalence_derivative_positive e he0 hepos hereal b
  have hdr := normalized_equivalence_derivative_real e he0 hepos hereal b
  have hv : e.toFun b = ((e.toFun b).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.2)
  have hdv : deriv e.toFun b = ((deriv e.toFun b).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hdr)
  rw [hv, hdv, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos hp.1, abs_of_pos hdp] at hbound
  apply (le_div_iff₀ hp.1).mpr
  have hb := (div_le_iff₀ hdp).mp (show Real.pi * (e.toFun b).re / (deriv e.toFun b).re ≤ 1 by
    simpa only [mul_div_assoc] using hbound)
  simpa only [one_mul] using hb

end MaxModulusPoints.StripMap
