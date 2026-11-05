module

public import Mathlib.Analysis.Complex.SqrtDeriv
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.KernelGeometry
public import MaxModulusPoints.StripMap.Rescaling
public import MaxModulusPoints.StripMap.Symmetry

/-!
# A bounded transform of the rescaled strip maps

The principal square root sends the slit plane into the right half-plane.
The Cayley transform then gives bounded holomorphic maps on the fixed strip.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

def slitToDisc (z : ℂ) : ℂ := (Complex.sqrt z - 1) / (Complex.sqrt z + 1)

def discToSlit (w : ℂ) : ℂ := ((1 + w) / (1 - w)) ^ 2

theorem sqrt_re_pos_of_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  apply div_pos ?_ (by norm_num : (0 : ℝ) < 2)
  rcases Complex.mem_slitPlane_iff.mp hz with hr | hi
  · linarith [norm_nonneg z]
  · have h := Complex.abs_re_lt_norm.mpr hi
    linarith [neg_le_abs z.re]

theorem sqrt_add_one_ne_zero {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.sqrt z + 1 ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
  linarith [sqrt_re_pos_of_slitPlane hz]

theorem slitToDisc_norm_lt_one {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ‖slitToDisc z‖ < 1 := by
  rw [slitToDisc, norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (sqrt_add_one_ne_zero hz))).mpr
  have hs : ‖Complex.sqrt z - 1‖ ^ 2 < ‖Complex.sqrt z + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.add_im, add_zero]
    nlinarith [sqrt_re_pos_of_slitPlane hz]
  nlinarith [norm_nonneg (Complex.sqrt z - 1), norm_nonneg (Complex.sqrt z + 1)]

theorem slitToDisc_differentiableOn : DifferentiableOn ℂ slitToDisc Complex.slitPlane :=
  (Complex.differentiableOn_sqrt.sub_const 1).div
    (Complex.differentiableOn_sqrt.add_const 1) (fun _ hz => sqrt_add_one_ne_zero hz)

theorem slitToDisc_one : slitToDisc 1 = 0 := by simp [slitToDisc]

theorem discToSlit_slitToDisc {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    discToSlit (slitToDisc z) = z := by
  have hden := sqrt_add_one_ne_zero hz
  have hne : 1 - slitToDisc z ≠ 0 := by
    intro h
    have he : slitToDisc z = 1 := (sub_eq_zero.mp h).symm
    have hn := slitToDisc_norm_lt_one hz
    simp only [he, norm_one, lt_self_iff_false] at hn
  have hid : (1 + slitToDisc z) / (1 - slitToDisc z) = Complex.sqrt z := by
    apply (div_eq_iff hne).mpr
    dsimp only [slitToDisc]
    field_simp
    ring
  rw [discToSlit, hid]
  simp only [Complex.sqrt, Complex.cpow_ofNat_inv_pow]

theorem rescaledMap_mem_scaledTarget (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℝ) {z : ℂ} (hz : z ∈ strip) :
    rescaledMap e b z ∈ scaledTarget (e.toFun b).re := by
  have hp := normalized_equivalence_positive_real e he0 hepos hereal b
  have hval : ((e.toFun b).re : ℂ) = e.toFun b :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.2.symm)
  have hne : e.toFun b ≠ 0 := by
    intro h
    exact hp.1.ne' (congrArg Complex.re h)
  change ((e.toFun b).re : ℂ) * rescaledMap e b z ∈ target
  rw [hval, rescaledMap, ← mul_div_assoc, mul_div_cancel_left₀ _ hne]
  apply e.mapsTo
  simpa only [strip, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, zero_add] using hz

theorem bounded_rescaledMap (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℝ) :
    DifferentiableOn ℂ (slitToDisc ∘ rescaledMap e b) strip ∧
      (slitToDisc ∘ rescaledMap e b) 0 = 0 ∧
      ∀ z ∈ strip, ‖(slitToDisc ∘ rescaledMap e b) z‖ < 1 := by
  have hm : MapsTo (rescaledMap e b) strip Complex.slitPlane := fun z hz =>
    scaledTarget_subset_slitPlane
      (normalized_equivalence_positive_real e he0 hepos hereal b).1
      (rescaledMap_mem_scaledTarget e he0 hepos hereal b hz)
  refine ⟨slitToDisc_differentiableOn.comp (rescaledMap_differentiableOn e b) hm, ?_, ?_⟩
  · simp only [Function.comp_apply, rescaledMap_zero e he0 hepos hereal b, slitToDisc_one]
  · exact fun z hz => slitToDisc_norm_lt_one (hm hz)

end MaxModulusPoints.StripMap
