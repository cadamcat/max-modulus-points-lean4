module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.ExponentialChart
public import MaxModulusPoints.StripMap.Geometry
public import MaxModulusPoints.StripMap.LimitRange
public import MaxModulusPoints.StripMap.RealDerivative
public import MaxModulusPoints.StripMap.Rescaling
public import MaxModulusPoints.StripMap.SharpDerivative
public import MaxModulusPoints.StripMap.Symmetry

/-!
# Identification of rescaled limits

The sharp lower bound for the real logarithmic derivative survives locally
uniform limits. For a normalized map into the right half-plane, Schwarz's
lemma gives the opposite bound. Its equality case identifies the map with
the exponential.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

theorem rescaledMap_derivative_zero_real (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℝ) :
    deriv (rescaledMap e b) 0 =
      (((deriv e.toFun b).re / (e.toFun b).re : ℝ) : ℂ) := by
  have hp := normalized_equivalence_positive_real e he0 hepos hereal b
  have hdr := normalized_equivalence_derivative_real e he0 hepos hereal b
  have hv : e.toFun b = ((e.toFun b).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hp.2)
  have hdv : deriv e.toFun b = ((deriv e.toFun b).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hdr)
  rw [(rescaledMap_hasDerivAt_zero e b).deriv, hdv, hv, Complex.ofReal_div]
  simp only [Complex.ofReal_re]

theorem rescaledMap_limit_derivative (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {b : ℕ → ℝ} {f : ℂ → ℂ}
    (hc : TendstoLocallyUniformlyOn (fun n => rescaledMap e (b n)) f atTop strip) :
    Real.pi ≤ (deriv f 0).re ∧ (deriv f 0).im = 0 := by
  have hcd : Tendsto (fun n => deriv (rescaledMap e (b n)) 0) atTop (𝓝 (deriv f 0)) := by
    simpa only [Function.comp_apply] using
      (hc.deriv (Eventually.of_forall fun n => rescaledMap_differentiableOn e (b n))
        isOpen_strip).tendsto_at zero_mem_strip
  constructor
  · apply ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hcd)
    apply Eventually.of_forall
    intro n
    rw [Function.comp_apply, rescaledMap_derivative_zero_real e he0 hepos hereal, Complex.ofReal_re]
    exact normalized_equivalence_log_derivative_ge_pi e he0 hepos hereal (b n)
  · have hi : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (deriv f 0).im) := by
      convert Complex.continuous_im.continuousAt.tendsto.comp hcd using 1
      funext n
      rw [Function.comp_apply, rescaledMap_derivative_zero_real e he0 hepos hereal,
        Complex.ofReal_im]
    exact tendsto_nhds_unique hi tendsto_const_nhds

theorem halfPlane_map_eq_stripExp_of_derivative {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f strip) (hm : MapsTo f strip rightHalfPlane)
    (hf0 : f 0 = 1) (hpi : Real.pi ≤ (deriv f 0).re) (hreal : (deriv f 0).im = 0) :
    EqOn f stripExp strip := by
  let q : ℂ → ℂ := fun w => halfToDisc (f (discToStrip w))
  have qzero : q 0 = 0 := by
    simp only [q, discToStrip_zero, hf0, halfToDisc, sub_self, zero_div]
  have qmaps : MapsTo q (ball 0 1) (ball 0 1) :=
    halfToDisc_mapsTo.comp (hm.comp discToStrip_mapsTo)
  have qdiff : DifferentiableOn ℂ q (ball 0 1) :=
    halfToDisc_differentiableOn.comp
      (hd.comp discToStrip_differentiableOn discToStrip_mapsTo)
      (hm.comp discToStrip_mapsTo)
  have hdf : HasDerivAt f (deriv f 0) (discToStrip 0) := by
    rw [discToStrip_zero]
    exact (hd.differentiableAt (isOpen_strip.mem_nhds zero_mem_strip)).hasDerivAt
  have hhalf : HasDerivAt halfToDisc (1 / 2) (f (discToStrip 0)) := by
    rw [discToStrip_zero, hf0]
    exact halfToDisc_hasDerivAt_one
  have qder : deriv q 0 = deriv f 0 / (Real.pi : ℂ) := by
    have hn : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    convert (hhalf.comp 0 (hdf.comp 0 discToStrip_hasDerivAt_zero)).deriv using 1
    · rfl
    · field_simp
  have qbound := Complex.norm_deriv_le_one_of_mapsTo_ball qdiff
    (by simpa only [qzero] using qmaps.mono_right ball_subset_closedBall) (by norm_num)
  have hdreal : deriv f 0 = ((deriv f 0).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hreal)
  have hratio : 1 ≤ (deriv f 0).re / Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by simpa using hpi)
  have qder_real : deriv q 0 = (((deriv f 0).re / Real.pi : ℝ) : ℂ) := by
    rw [qder, hdreal, Complex.ofReal_div]
    simp only [Complex.ofReal_re]
  have qone : deriv q 0 = 1 := by
    rw [qder_real, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ (deriv f 0).re / Real.pi)] at qbound
    rw [qder_real, le_antisymm qbound hratio, Complex.ofReal_one]
  have qaffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div qdiff
    (by simpa only [qzero] using qmaps.mono_right ball_subset_closedBall)
    (by norm_num : (0 : ℂ) ∈ ball 0 (1 : ℝ))
    (by simp only [dslope_same, qone, norm_one, div_one])
  intro z hz
  have heq := qaffine (stripToDisc_mapsTo hz)
  have heq' : q (stripToDisc z) = stripToDisc z := by
    simpa only [qzero, dslope_same, qone, sub_zero, smul_eq_mul, mul_one, zero_add] using heq
  have he : halfToDisc (f z) = halfToDisc (stripExp z) := by
    change halfToDisc (f (discToStrip (stripToDisc z))) = halfToDisc (stripExp z) at heq'
    rwa [discToStrip_stripToDisc hz] at heq'
  have hinv := congrArg discToHalf he
  simpa only [discToHalf_halfToDisc (hm hz),
    discToHalf_halfToDisc (stripExp_mapsTo hz)] using hinv

/-- Every escaping locally uniform rescaled limit is the exponential on the strip. -/
theorem rescaledMap_limit_eq_stripExp (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {b : ℕ → ℝ} (hb : Tendsto b atTop atTop)
    {f : ℂ → ℂ}
    (hc : TendstoLocallyUniformlyOn (fun n => rescaledMap e (b n)) f atTop strip) :
    EqOn f stripExp strip := by
  have hder := rescaledMap_limit_derivative e he0 hepos hereal hc
  exact halfPlane_map_eq_stripExp_of_derivative
    (hc.differentiableOn (Eventually.of_forall fun n => rescaledMap_differentiableOn e (b n))
      isOpen_strip)
    (rescaledMap_limit_re_pos e he0 hepos hereal hb hc)
    (rescaledMap_limit_zero e he0 hepos hereal hc) hder.1 hder.2

end MaxModulusPoints.StripMap
