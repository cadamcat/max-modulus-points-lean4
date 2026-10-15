import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.StripMap.Rescaling
/-!
# Explicit charts for the strip and the right half-plane

The exponential identifies the strip of height one with the right half-plane.
The Cayley transform then supplies a normalized disc chart and its inverse.
-/

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

def rightHalfPlane : Set ℂ := {z | 0 < z.re}

def stripExp (z : ℂ) : ℂ := Complex.exp (Real.pi * z)

def halfLog (w : ℂ) : ℂ := Complex.log w / Real.pi

def halfToDisc (w : ℂ) : ℂ := (w - 1) / (w + 1)

def discToHalf (w : ℂ) : ℂ := (1 + w) / (1 - w)

theorem stripExp_mapsTo : MapsTo stripExp strip rightHalfPlane := by
  intro z hz
  change 0 < (Complex.exp ((Real.pi : ℂ) * z)).re
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have hi := abs_lt.mp (show |z.im| < 1 / 2 from hz)
  simp only [mem_Ioo, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  constructor <;> nlinarith [Real.pi_pos]

theorem halfLog_mapsTo : MapsTo halfLog rightHalfPlane strip := by
  intro w hw
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  change |(Complex.log w / (Real.pi : ℂ)).im| < 1 / 2
  rw [Complex.div_ofReal_im, abs_div, abs_of_pos Real.pi_pos, Complex.log_im]
  exact (div_lt_iff₀ Real.pi_pos).mpr (by linarith)

theorem halfLog_stripExp {z : ℂ} (hz : z ∈ strip) : halfLog (stripExp z) = z := by
  have hi := abs_lt.mp (show |z.im| < 1 / 2 from hz)
  have him : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
  rw [halfLog, stripExp, Complex.log_exp (by rw [him]; nlinarith [Real.pi_pos])
    (by rw [him]; nlinarith [Real.pi_pos])]
  exact mul_div_cancel_left₀ z (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem stripExp_halfLog {w : ℂ} (hw : w ∈ rightHalfPlane) : stripExp (halfLog w) = w := by
  have hn : w ≠ 0 := by intro h; simpa only [h, rightHalfPlane, mem_ofPred_eq,
    Complex.zero_re, lt_self_iff_false] using hw
  rw [stripExp, halfLog, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  exact Complex.exp_log hn

theorem stripExp_hasDerivAt (z : ℂ) :
    HasDerivAt stripExp ((Real.pi : ℂ) * stripExp z) z := by
  change HasDerivAt (fun z : ℂ => Complex.exp (Real.pi * z)) _ z
  simpa only [stripExp, mul_one, mul_comm, id_eq] using
    (((hasDerivAt_id z).const_mul (Real.pi : ℂ)).cexp)

theorem halfLog_differentiableOn : DifferentiableOn ℂ halfLog rightHalfPlane := by
  intro z hz
  exact ((Complex.differentiableAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hz))).div_const
    (Real.pi : ℂ)).differentiableWithinAt

theorem half_add_one_ne_zero {w : ℂ} (hw : w ∈ rightHalfPlane) : w + 1 ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
  change 0 < w.re at hw
  linarith

theorem halfToDisc_mapsTo : MapsTo halfToDisc rightHalfPlane (ball 0 1) := by
  intro w hw
  rw [mem_ball_zero_iff, halfToDisc, norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (half_add_one_ne_zero hw))).mpr
  have hs : ‖w - 1‖ ^ 2 < ‖w + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.add_im, add_zero]
    change 0 < w.re at hw
    nlinarith
  nlinarith [norm_nonneg (w - 1), norm_nonneg (w + 1)]

theorem disc_sub_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simpa only [he, mem_ball_zero_iff, norm_one, lt_self_iff_false] using hw

theorem discToHalf_mapsTo : MapsTo discToHalf (ball 0 1) rightHalfPlane := by
  intro w hw
  have hn : Complex.normSq w < 1 := by
    have := mem_ball_zero_iff.mp hw
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg w]
  change 0 < ((1 + w) / (1 - w)).re
  rw [Complex.div_re, ← add_div]
  apply div_pos ?_ (Complex.normSq_pos.mpr (disc_sub_ne_zero hw))
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im,
    Complex.one_im, zero_add, Complex.sub_im, zero_sub]
  simp only [Complex.normSq_apply] at hn
  nlinarith

theorem discToHalf_halfToDisc {w : ℂ} (hw : w ∈ rightHalfPlane) :
    discToHalf (halfToDisc w) = w := by
  have hn := disc_sub_ne_zero (halfToDisc_mapsTo hw)
  apply (div_eq_iff hn).mpr
  dsimp only [halfToDisc]
  field_simp [half_add_one_ne_zero hw]
  ring

theorem halfToDisc_discToHalf {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    halfToDisc (discToHalf w) = w := by
  have hn := half_add_one_ne_zero (discToHalf_mapsTo hw)
  apply (div_eq_iff hn).mpr
  dsimp only [discToHalf]
  field_simp [disc_sub_ne_zero hw]
  ring

theorem halfToDisc_differentiableOn : DifferentiableOn ℂ halfToDisc rightHalfPlane :=
  (differentiableOn_id.sub_const 1).div (differentiableOn_id.add_const 1)
    (fun _ hw => half_add_one_ne_zero hw)

theorem discToHalf_differentiableOn : DifferentiableOn ℂ discToHalf (ball 0 1) :=
  ((differentiable_const (1 : ℂ)).differentiableOn.add differentiableOn_id).div
    ((differentiable_const (1 : ℂ)).differentiableOn.sub differentiableOn_id)
      (fun _ hw => disc_sub_ne_zero hw)

def stripToDisc (z : ℂ) : ℂ := halfToDisc (stripExp z)

def discToStrip (w : ℂ) : ℂ := halfLog (discToHalf w)

theorem stripToDisc_mapsTo : MapsTo stripToDisc strip (ball 0 1) :=
  halfToDisc_mapsTo.comp stripExp_mapsTo

theorem discToStrip_mapsTo : MapsTo discToStrip (ball 0 1) strip :=
  halfLog_mapsTo.comp discToHalf_mapsTo

theorem discToStrip_stripToDisc {z : ℂ} (hz : z ∈ strip) :
    discToStrip (stripToDisc z) = z := by
  rw [discToStrip, stripToDisc, discToHalf_halfToDisc (stripExp_mapsTo hz), halfLog_stripExp hz]

theorem stripToDisc_discToStrip {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    stripToDisc (discToStrip w) = w := by
  rw [stripToDisc, discToStrip, stripExp_halfLog (discToHalf_mapsTo hw), halfToDisc_discToHalf hw]

theorem stripToDisc_differentiableOn : DifferentiableOn ℂ stripToDisc strip :=
  halfToDisc_differentiableOn.comp
    (fun z _ => (stripExp_hasDerivAt z).differentiableAt.differentiableWithinAt) stripExp_mapsTo

theorem discToStrip_differentiableOn : DifferentiableOn ℂ discToStrip (ball 0 1) :=
  halfLog_differentiableOn.comp discToHalf_differentiableOn discToHalf_mapsTo

theorem stripToDisc_zero : stripToDisc 0 = 0 := by simp [stripToDisc, stripExp, halfToDisc]

theorem discToHalf_zero : discToHalf 0 = 1 := by simp [discToHalf]

theorem discToStrip_zero : discToStrip 0 = 0 := by simp [discToStrip, discToHalf_zero, halfLog]

theorem stripExp_zero : stripExp 0 = 1 := by simp [stripExp]

theorem halfToDisc_hasDerivAt_one : HasDerivAt halfToDisc (1 / 2) 1 := by
  change HasDerivAt (fun w : ℂ => (w - 1) / (w + 1)) _ _
  convert ((hasDerivAt_id (1 : ℂ)).sub_const 1).div
    ((hasDerivAt_id (1 : ℂ)).add_const 1) (by norm_num) using 1 <;> norm_num [halfToDisc]
  rfl

theorem discToHalf_hasDerivAt_zero : HasDerivAt discToHalf 2 0 := by
  change HasDerivAt (fun w : ℂ => (1 + w) / (1 - w)) _ _
  convert ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add (hasDerivAt_id 0)).div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 0)) (by norm_num) using 1 <;>
    norm_num [discToHalf]
  rfl

theorem stripToDisc_hasDerivAt_zero : HasDerivAt stripToDisc (Real.pi / 2) 0 := by
  change HasDerivAt (fun z => halfToDisc (stripExp z)) _ _
  have hh : HasDerivAt halfToDisc (1 / 2) (stripExp 0) := by
    rw [stripExp_zero]
    exact halfToDisc_hasDerivAt_one
  have h := hh.comp 0 (stripExp_hasDerivAt 0)
  simpa only [Function.comp_def, stripExp_zero, mul_one, one_div_mul_eq_div] using h

theorem discToStrip_hasDerivAt_zero : HasDerivAt discToStrip (2 / Real.pi) 0 := by
  change HasDerivAt (fun w => halfLog (discToHalf w)) _ _
  have hh : HasDerivAt halfLog (1 / Real.pi) (discToHalf 0) := by
    rw [discToHalf_zero]
    change HasDerivAt (fun w : ℂ => Complex.log w / Real.pi) _ _
    simpa only [inv_one] using
      ((Complex.hasDerivAt_log (by simp [Complex.mem_slitPlane_iff] :
        (1 : ℂ) ∈ Complex.slitPlane)).div_const (Real.pi : ℂ))
  have h := hh.comp 0 discToHalf_hasDerivAt_zero
  simpa only [Function.comp_def, one_div_mul_eq_div] using h

end MaxModulusPoints.StripMap
