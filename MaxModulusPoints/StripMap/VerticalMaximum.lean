module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.Geometry
public import MaxModulusPoints.StripMap.Growth
public import MaxModulusPoints.StripMap.ImaginaryContraction
public import MaxModulusPoints.StripMap.Symmetry

/-!
# The vertical real-part maximum

Horizontal translation preserves the logarithmic target. Pulling these
translations back to the strip gives symmetric holomorphic self-maps.
Their imaginary contraction implies that the imaginary part of the strip
map's derivative is nonnegative above the real axis. The real part of the
map therefore decreases along every upward vertical segment.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology ComplexConjugate

theorem add_nonneg_mem_target {w : ℂ} (hw : w ∈ target) {t : ℝ} (ht : 0 ≤ t) :
    w + t ∈ target := by
  change -14 * max 0 (Real.log |(w + t).im|) < (w + t).re
  simpa only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, add_zero] using lt_of_lt_of_le hw (le_add_of_nonneg_right ht)

theorem normalized_inverse_symmetric (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {w : ℂ} (hw : w ∈ target) :
    e.invFun (conj w) = conj (e.invFun w) := by
  have hs := normalized_equivalence_symmetric e he0 hepos hereal
    (e.invFun w) (e.inverse_mapsTo hw)
  rw [e.right_inv w hw] at hs
  rw [← hs, e.left_inv _ (conj_mem_strip (e.inverse_mapsTo hw))]

def translationFlow (e : ConformalEquivalence strip target) (t : ℝ) (z : ℂ) : ℂ :=
  e.invFun (e.toFun z + t)

theorem translationFlow_mapsTo (e : ConformalEquivalence strip target) {t : ℝ} (ht : 0 ≤ t) :
    MapsTo (translationFlow e t) strip strip := by
  intro z hz
  exact e.inverse_mapsTo (add_nonneg_mem_target (e.mapsTo hz) ht)

theorem translationFlow_differentiableOn (e : ConformalEquivalence strip target)
    {t : ℝ} (ht : 0 ≤ t) : DifferentiableOn ℂ (translationFlow e t) strip :=
  e.inverse_holomorphic.comp (e.holomorphic.add_const (t : ℂ))
    (fun _ hz => add_nonneg_mem_target (e.mapsTo hz) ht)

theorem translationFlow_symmetric (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∀ z ∈ strip, translationFlow e t (conj z) = conj (translationFlow e t z) := by
  intro z hz
  change e.invFun (e.toFun (conj z) + t) = conj (e.invFun (e.toFun z + t))
  rw [normalized_equivalence_symmetric e he0 hepos hereal z hz]
  have hc : conj (e.toFun z + t) = conj (e.toFun z) + t := by simp
  rw [← hc]
  exact normalized_inverse_symmetric e he0 hepos hereal
    (add_nonneg_mem_target (e.mapsTo hz) ht)

theorem translationFlow_zero (e : ConformalEquivalence strip target) {z : ℂ} (hz : z ∈ strip) :
    translationFlow e 0 z = z := by
  simpa only [translationFlow, Complex.ofReal_zero, add_zero] using e.left_inv z hz

theorem inverse_derivative_im_nonpos (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {z : ℂ} (hz : z ∈ strip) (hi : 0 ≤ z.im) :
    (deriv e.invFun (e.toFun z)).im ≤ 0 := by
  let F : ℂ → ℂ := fun w => e.invFun (e.toFun z + w)
  have houter : HasDerivAt e.invFun (deriv e.invFun (e.toFun z)) (e.toFun z + (0 : ℂ)) := by
    simpa only [add_zero] using (e.inverse_holomorphic.differentiableAt
      (isOpen_target.mem_nhds (e.mapsTo hz))).hasDerivAt
  have hF : HasDerivAt F (deriv e.invFun (e.toFun z)) 0 := by
    change HasDerivAt (fun w : ℂ => e.invFun (e.toFun z + w)) _ _
    simpa only [Function.comp_def, id_eq, mul_one] using
      houter.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add (e.toFun z))
  have hder : HasDerivAt (fun t : ℝ => (translationFlow e t z).im)
      (deriv e.invFun (e.toFun z)).im 0 := by
    have h := (hF.mul_const (-Complex.I)).real_of_complex
    simpa only [F, translationFlow, Complex.mul_re, Complex.neg_re, Complex.I_re,
      neg_zero, mul_zero, Complex.neg_im, Complex.I_im, mul_neg_one, zero_sub, neg_neg] using h
  apply le_of_tendsto hder.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hbound := (le_abs_self (translationFlow e t z).im).trans
    (strip_symmetric_selfMap_im_abs_le (translationFlow_differentiableOn e ht.le)
      (translationFlow_mapsTo e ht.le) (translationFlow_symmetric e he0 hepos hereal ht.le) hz)
  have hbound' : (translationFlow e t z).im ≤ (translationFlow e 0 z).im := by
    simpa only [translationFlow_zero e hz, abs_of_nonneg hi] using hbound
  simpa only [zero_add, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr hbound')

theorem normalized_equivalence_derivative_im_nonneg (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {z : ℂ} (hz : z ∈ strip) (hi : 0 ≤ z.im) :
    0 ≤ (deriv e.toFun z).im := by
  have hm := inverse_derivative_mul e hz
  have hn : deriv e.toFun z ≠ 0 := by intro h; simp only [h, mul_zero, zero_ne_one] at hm
  have he : deriv e.invFun (e.toFun z) = (deriv e.toFun z)⁻¹ := by
    calc
      deriv e.invFun (e.toFun z) =
          (deriv e.invFun (e.toFun z) * deriv e.toFun z) * (deriv e.toFun z)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
      _ = (deriv e.toFun z)⁻¹ := by rw [hm, one_mul]
  have hb := inverse_derivative_im_nonpos e he0 hepos hereal hz hi
  rw [he, Complex.inv_im] at hb
  have h := (div_le_iff₀ (Complex.normSq_pos.mpr hn)).mp hb
  linarith

theorem normalized_equivalence_vertical_maximum_nonneg (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (s y : ℝ) (hy : 0 ≤ y) (hyhalf : y < 1 / 2) :
    (e.toFun ((s : ℂ) + y * Complex.I)).re ≤ (e.toFun s).re := by
  let f : ℝ → ℝ := fun t => (e.toFun ((s : ℂ) + t * Complex.I)).re
  have hmem (t : ℝ) (ht : t ∈ Icc 0 y) : (s : ℂ) + t * Complex.I ∈ strip := by
    simpa only [strip, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, zero_mul, add_zero,
      zero_add, abs_of_nonneg ht.1] using ht.2.trans_lt hyhalf
  have hd (t : ℝ) (ht : t ∈ Icc 0 y) :
      HasDerivAt f (-(deriv e.toFun ((s : ℂ) + t * Complex.I)).im) t := by
    have he := (e.holomorphic.differentiableAt (isOpen_strip.mem_nhds (hmem t ht))).hasDerivAt
    have hc : HasDerivAt (fun w : ℂ => (s : ℂ) + w * Complex.I) Complex.I (t : ℂ) := by
      simpa only [one_mul, id_eq] using
        ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (s : ℂ)
    have h := (he.comp (t : ℂ) hc).real_of_complex
    change HasDerivAt (fun t : ℝ => (e.toFun ((s : ℂ) + t * Complex.I)).re) _ _
    simpa only [Function.comp_def, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.I_im, mul_one, zero_sub] using h
  have ha : AntitoneOn f (Icc 0 y) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 y)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    apply neg_nonpos.mpr
    apply normalized_equivalence_derivative_im_nonneg e he0 hepos hereal
      (hmem t (interior_subset ht))
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add] using
      (interior_subset ht : t ∈ Icc 0 y).1
  have h := ha (by simp [hy]) (by simp [hy]) hy
  simpa only [f, Complex.ofReal_zero, zero_mul, add_zero] using h

/-- The real part of the normalized strip map is maximal at the real point of each vertical line. -/
theorem normalized_equivalence_vertical_maximum (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (s y : ℝ) (hy : |y| < 1 / 2) :
    (e.toFun ((s : ℂ) + y * Complex.I)).re ≤ (e.toFun s).re := by
  by_cases hy0 : 0 ≤ y
  · exact normalized_equivalence_vertical_maximum_nonneg e he0 hepos hereal s y hy0
      (by rwa [abs_of_nonneg hy0] at hy)
  · have hyn : 0 ≤ -y := by linarith
    have hhalf : -y < 1 / 2 := by rwa [abs_of_neg (lt_of_not_ge hy0)] at hy
    have h := normalized_equivalence_vertical_maximum_nonneg e he0 hepos hereal s (-y) hyn hhalf
    have hz : (s : ℂ) + y * Complex.I ∈ strip := by
      simpa only [strip, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add] using hy
    have hc : conj ((s : ℂ) + y * Complex.I) = (s : ℂ) + (-y : ℝ) * Complex.I := by simp
    have hs := congrArg Complex.re (normalized_equivalence_symmetric e he0 hepos hereal _ hz)
    rw [hc, Complex.conj_re] at hs
    rwa [hs] at h

end MaxModulusPoints.StripMap
