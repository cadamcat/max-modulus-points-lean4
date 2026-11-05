module

public import OAI.Probability.SLE.AngularLaws
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripEstimates.Growth
public import MaxModulusPoints.StripMap.Geometry
public import MaxModulusPoints.StripMap.RealDerivative
public import MaxModulusPoints.StripMap.Symmetry

/-!
# Exponential growth of the strip map

An omitted-value bound on discs, applied to the map and its inverse,
gives uniform bounds on the logarithmic derivative along the real axis.
Integrating these bounds gives the two-sided exponential estimate.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

theorem ball_real_subset_strip (s : ℝ) : ball (s : ℂ) (1 / 2) ⊆ strip := by
  intro z hz
  have hi := Complex.abs_im_le_norm (z - (s : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  exact hi.trans_lt (by simpa only [mem_ball, dist_eq_norm] using hz)

theorem ball_real_subset_target {x : ℝ} (_hx : 0 < x) : ball (x : ℂ) x ⊆ target := by
  intro z hz
  have hr := Complex.abs_re_le_norm (z - (x : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  have hn : ‖z - (x : ℂ)‖ < x := by simpa only [mem_ball, dist_eq_norm] using hz
  have hh := (abs_lt.mp (hr.trans_lt hn)).1
  have hpos : 0 < z.re := by linarith
  change -14 * max 0 (Real.log |z.im|) < z.re
  exact lt_of_le_of_lt (by nlinarith [le_max_left (0 : ℝ) (Real.log |z.im|)]) hpos

theorem inverse_derivative_mul (e : ConformalEquivalence strip target) {z : ℂ}
    (hz : z ∈ strip) : deriv e.invFun (e.toFun z) * deriv e.toFun z = 1 := by
  have hd := (e.holomorphic.differentiableAt (isOpen_strip.mem_nhds hz)).hasDerivAt
  have hdi := (e.inverse_holomorphic.differentiableAt
    (isOpen_target.mem_nhds (e.mapsTo hz))).hasDerivAt
  have he : (e.invFun ∘ e.toFun) =ᶠ[𝓝 z] id :=
    eventually_nhds_iff.mpr ⟨strip, fun w hw => e.left_inv w hw, isOpen_strip, hz⟩
  exact ((hdi.comp z hd).congr_of_eventuallyEq he.symm).unique (hasDerivAt_id z)

/-- Coarse universal logarithmic derivative bounds suffice for exponential growth. -/
theorem normalized_equivalence_log_derivative_bounds (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (s : ℝ) :
    1 / (64 * Real.pi) ≤ (deriv e.toFun s).re / (e.toFun s).re ∧
      (deriv e.toFun s).re / (e.toFun s).re ≤ 256 * Real.pi := by
  have hpr := normalized_equivalence_positive_real e he0 hepos hereal s
  have hdr := normalized_equivalence_derivative_real e he0 hepos hereal s
  have hdp := normalized_equivalence_derivative_positive e he0 hepos hereal s
  have hval : e.toFun s = ((e.toFun s).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hpr.2)
  have hdval : deriv e.toFun s = ((deriv e.toFun s).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hdr)
  have hnorm : ‖e.toFun s‖ = (e.toFun s).re := by
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpr.1, Complex.ofReal_re]
  have hdnorm : ‖deriv e.toFun s‖ = (deriv e.toFun s).re := by
    rw [hdval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdp, Complex.ofReal_re]
  have hu := OAI.SLEExactGauge.univalent_omitted_value_bound_ball
    (by norm_num : (0 : ℝ) < 1 / 2)
    (e.holomorphic.mono (ball_real_subset_strip s))
    ((equivalence_injOn e).mono (ball_real_subset_strip s)) (0 : ℂ) (by
      rintro ⟨z, hz, he⟩
      have ht := e.mapsTo (ball_real_subset_strip s hz)
      rw [he] at ht
      norm_num [target] at ht)
  rw [sub_zero, hnorm, hdnorm] at hu
  have hball : ball (e.toFun s) (e.toFun s).re ⊆ target := by
    rw [hval]
    exact ball_real_subset_target hpr.1
  have hinj : InjOn e.invFun target := by
    intro z hz w hw he
    simpa only [e.right_inv z hz, e.right_inv w hw] using congrArg e.toFun he
  have hl := OAI.SLEExactGauge.univalent_omitted_value_bound_ball hpr.1
    (e.inverse_holomorphic.mono hball) (hinj.mono hball)
    ((s : ℂ) + (1 / 2 : ℂ) * Complex.I) (by
      rintro ⟨z, hz, he⟩
      have ht := e.inverse_mapsTo (hball hz)
      rw [he] at ht
      norm_num [strip] at ht)
  have hdist : ‖e.invFun (e.toFun s) - ((s : ℂ) + (1 / 2 : ℂ) * Complex.I)‖ = 1 / 2 := by
    rw [e.left_inv s (real_mem_strip s), sub_add_eq_sub_sub, sub_self, zero_sub,
      norm_neg, norm_mul, Complex.norm_I, mul_one]
    norm_num
  rw [hdist] at hl
  have hmul : ‖deriv e.invFun (e.toFun s)‖ * (deriv e.toFun s).re = 1 := by
    have h := congrArg norm (inverse_derivative_mul e (real_mem_strip s))
    simpa only [norm_mul, norm_one, hdnorm] using h
  have hlow := mul_le_mul_of_nonneg_right hl hdp.le
  rw [mul_assoc, hmul, mul_one] at hlow
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0 < 64 * Real.pi) hpr.1).mpr
    nlinarith
  · apply (div_le_iff₀ hpr.1).mpr
    nlinarith

/-- The normalized map satisfies two-sided exponential bounds for every real base point. -/
theorem normalized_equivalence_growth (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (s u : ℝ) (hu : 0 ≤ u) :
    Real.exp ((1 / (64 * Real.pi)) * u) * (e.toFun s).re ≤ (e.toFun (s + u : ℝ)).re ∧
      (e.toFun (s + u : ℝ)).re ≤ Real.exp ((256 * Real.pi) * u) * (e.toFun s).re := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => (e.toFun x).re) (deriv e.toFun t).re t :=
    (e.holomorphic.differentiableAt
      (isOpen_strip.mem_nhds (real_mem_strip t))).hasDerivAt.real_of_complex
  apply StripEstimates.exp_growth_of_log_deriv_bounds
    (fun t => (normalized_equivalence_positive_real e he0 hepos hereal t).1)
    (fun t => (hd t).differentiableAt)
    (fun t => ?_) (fun t => ?_) s u hu
  · rw [(hd t).deriv]
    exact (normalized_equivalence_log_derivative_bounds e he0 hepos hereal t).1
  · rw [(hd t).deriv]
    exact (normalized_equivalence_log_derivative_bounds e he0 hepos hereal t).2

/-- The positive real values of the normalized map tend to infinity. -/
theorem normalized_equivalence_real_escape (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) :
    Tendsto (fun b : ℝ => (e.toFun b).re) atTop atTop := by
  have ha : 0 < 1 / (64 * Real.pi) := by positivity
  have hexp : Tendsto (fun b : ℝ => Real.exp ((1 / (64 * Real.pi)) * b)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop ha tendsto_id)
  apply tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  have h := (normalized_equivalence_growth e he0 hepos hereal 0 b hb).1
  simpa only [Complex.ofReal_zero, he0, Complex.one_re, mul_one, zero_add] using h

end MaxModulusPoints.StripMap
