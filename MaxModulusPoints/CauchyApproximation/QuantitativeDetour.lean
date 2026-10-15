import Mathlib.Analysis.Analytic.Uniqueness
import MaxModulusPoints.CauchyApproximation.CanonicalApproximation
import MaxModulusPoints.CauchyApproximation.CanonicalDensity
import MaxModulusPoints.CauchyApproximation.ContourDensity
import MaxModulusPoints.CauchyApproximation.ContourDerivative
import MaxModulusPoints.CauchyApproximation.ContourTube
import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
import MaxModulusPoints.CauchyApproximation.Holomorphy
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
import MaxModulusPoints.CauchyApproximation.InverseDistortion
import MaxModulusPoints.CauchyApproximation.LocalAgreement
import MaxModulusPoints.CauchyApproximation.LocalDetour
import MaxModulusPoints.CauchyApproximation.Model
import MaxModulusPoints.CauchyApproximation.ScaledDistortion
/-!
# A uniform scaled neighborhood for the tent detour

The image detour misses a fixed disk about the original image contour point.
The quarter theorem transfers this disk to a tract neighborhood with radius
proportional to the normalization derivative. The detour Cauchy integral
agrees with the canonical entire function throughout this neighborhood by
analytic continuation of their established local agreement.
-/

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The nonnegative graph shift stays in the enlarged half-plane. -/
theorem imageDetour_mem_modelHalfPlane (s t : ℝ) : imageDetour s t ∈ modelHalfPlane := by
  have h := imageContour_mem_modelHalfPlane t
  change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re at h
  change -14 * Real.posLog |(imageDetour s t).im| < (imageDetour s t).re
  simp only [imageDetour, add_im, ofReal_im, add_zero, add_re, ofReal_re]
  linarith [le_max_left (0 : ℝ) (1 - |t - s|)]

/-- A fixed disk about the original graph lies strictly to the left of the
tent graph and between its parameter endpoints. -/
theorem imageDetour_right_of_near_imageContour {s : ℝ} {w : ℂ}
    (hw : ‖w - imageContour s‖ < (1 / 30 : ℝ)) :
    s - 1 < w.im ∧ w.im < s + 1 ∧ w.re < (imageDetour s w.im).re := by
  have him : |w.im - s| < (1 / 30 : ℝ) := by
    simpa [imageContour] using (Complex.abs_im_le_norm (w - imageContour s)).trans_lt hw
  have hre : w.re < 1 - 13 * Real.posLog |s| + (1 / 30) := by
    have h := ((le_abs_self (w - imageContour s).re).trans
      (Complex.abs_re_le_norm (w - imageContour s))).trans_lt hw
    simp only [sub_re, imageContour, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
    linarith
  have hlog := lipschitzWith_posLog_abs.dist_le_mul w.im s
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlog
  have hlog' : Real.posLog |w.im| < Real.posLog |s| + (1 / 30) := by
    linarith [le_abs_self (Real.posLog |w.im| - Real.posLog |s|)]
  obtain ⟨hlo, hhi⟩ := abs_lt.1 him
  refine ⟨by linarith, by linarith, ?_⟩
  simp only [imageDetour, imageContour, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have ht : 1 - |w.im - s| ≤ max 0 (1 - |w.im - s|) := le_max_right _ _
  linarith

/-- Every point of the shifted graph stays outside the fixed image disk. -/
theorem imageDetour_separation (s t : ℝ) :
    (1 / 30 : ℝ) ≤ ‖imageDetour s t - imageContour s‖ := by
  by_contra! h
  have hr := (imageDetour_right_of_near_imageContour h).2.2
  have him : (imageDetour s t).im = t := by simp [imageDetour, imageContour]
  rw [him] at hr
  exact (lt_irrefl _ hr)

/-- One uniform scaled neighborhood has its conformal preimages in the
fixed image disk, retaining the actual positive normalization scale. -/
theorem exists_scaled_contour_preimage_neighborhood :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : NormalizedModel) (s : ℝ) (z : ℂ),
      ‖z - m.contour s‖ ≤ ε * ‖deriv m.inverse 1‖ / (max |s| 1) ^ 4 →
        z ∈ m.domain ∧ ‖m.forward z - imageContour s‖ < (1 / 30 : ℝ) := by
  obtain ⟨C, hC, hbounds⟩ := exists_scaled_inverse_deriv_contour_bounds
  let ε : ℝ := 1 / (240 * C)
  refine ⟨ε, by positivity, ?_⟩
  intro m s z hz
  have hscale := m.norm_inverse_deriv_one_pos
  have hs : 0 < (max |s| 1) ^ 4 := by positivity
  have hlow : ‖deriv m.inverse 1‖ / (C * (max |s| 1) ^ 4) ≤
      ‖deriv m.inverse (imageContour s)‖ := by
    apply (div_le_iff₀ (mul_pos hC hs)).2
    simpa only [mul_comm] using (hbounds m s).1
  have hrad : ε * ‖deriv m.inverse 1‖ / (max |s| 1) ^ 4 <
      (1 / 30) * ‖deriv m.inverse (imageContour s)‖ / 4 := by
    calc
      _ = (1 / 240) * (‖deriv m.inverse 1‖ / (C * (max |s| 1) ^ 4)) := by
        dsimp only [ε]
        ring
      _ < (1 / 120) * (‖deriv m.inverse 1‖ / (C * (max |s| 1) ^ 4)) :=
        mul_lt_mul_of_pos_right (by norm_num) (div_pos hscale (mul_pos hC hs))
      _ ≤ (1 / 120) * ‖deriv m.inverse (imageContour s)‖ :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)
      _ = _ := by ring
  have hball := imageContour_ball_subset_modelHalfPlane s
  have hu : UnivalentOn m.inverse (Metric.ball (imageContour s) (1 / 30)) :=
    ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
  have hzin : z ∈ Metric.ball (m.inverse (imageContour s))
      ((1 / 30) * ‖deriv m.inverse (imageContour s)‖ / 4) := by
    simpa only [Metric.mem_ball, dist_eq_norm, NormalizedModel.contour,
      Function.comp_def] using hz.trans_lt hrad
  obtain ⟨w, hw, he⟩ := univalent_ball_quarter (by norm_num : (0 : ℝ) < 1 / 30) hu hzin
  have hwH : w ∈ modelHalfPlane := hball hw
  refine ⟨he ▸ m.inverse_mem hwH, ?_⟩
  have hzforward : m.forward z = w := by rw [← he, m.right_inverse w hwH]
  rw [hzforward]
  simpa only [Metric.mem_ball, dist_eq_norm] using hw

/-- The detour Cauchy integral and the canonical entire function agree on
some neighborhood of the original contour point, including the point itself. -/
theorem NormalizedModel.canonicalEntire_eventuallyEq_localDetour (m : NormalizedModel)
    (s : ℝ) :
    m.canonicalEntire =ᶠ[𝓝 (m.contour s)]
      cauchyIntegral (m.localDetour s)
        (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t) := by
  let S : Set ℂ := (range m.contour)ᶜ
  let J := cauchyIntegral (m.localDetour s)
    (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t)
  obtain ⟨δ, hδ, -, hJ, hagree⟩ :=
    m.localDetour_cauchyIntegral_agrees s m.integrable_density
  have hdense : Dense S := m.contour_frontier_and_dense_complement.2
  have heq : EqOn m.canonicalEntire J (Metric.ball (m.contour s) δ) := by
    intro z hz
    have : NeBot (𝓝[S] z) := mem_closure_iff_nhdsWithin_neBot.1 (hdense z)
    have hcontJ : ContinuousAt J z :=
      hJ.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    have hevent : m.canonicalEntire =ᶠ[𝓝[S] z] J := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hz)] with w hwS hwδ
      by_cases hwcore : w ∈ m.core
      · exact ((m.canonicalEntire_spec.2 w hwS).1 hwcore).trans
          ((hagree w hwδ hwS).1 hwcore).symm
      · exact ((m.canonicalEntire_spec.2 w hwS).2 hwcore).trans
          ((hagree w hwδ hwS).2 hwcore).symm
    exact tendsto_nhds_unique_of_eventuallyEq
      (m.canonicalEntire_spec.1.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hcontJ.tendsto.mono_left nhdsWithin_le_nhds) hevent
  exact heq.eventuallyEq_of_mem (Metric.ball_mem_nhds _ hδ)

/-- One scaled neighborhood lies in the tract, avoids the entire detour,
and has the actual detour integral as its canonical entire function. -/
theorem exists_scaled_localDetour_agreement :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : NormalizedModel) (s : ℝ),
      let U := Metric.ball (m.contour s)
        (ε * ‖deriv m.inverse 1‖ / (max |s| 1) ^ 4)
      let J := cauchyIntegral (m.localDetour s)
        (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t)
      U ⊆ m.domain ∧ U ⊆ (range (m.localDetour s))ᶜ ∧
        DifferentiableOn ℂ J U ∧ EqOn m.canonicalEntire J U := by
  obtain ⟨ε, hε, hpre⟩ := exists_scaled_contour_preimage_neighborhood
  refine ⟨ε, hε, ?_⟩
  intro m s
  dsimp only
  let r := ε * ‖deriv m.inverse 1‖ / (max |s| 1) ^ 4
  let U := Metric.ball (m.contour s) r
  let J := cauchyIntegral (m.localDetour s)
    (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t)
  have hscale := m.norm_inverse_deriv_one_pos
  have hr : 0 < r := by dsimp only [r]; positivity
  have hpreU (z : ℂ) (hz : z ∈ U) :
      z ∈ m.domain ∧ ‖m.forward z - imageContour s‖ < (1 / 30 : ℝ) :=
    hpre m s z (le_of_lt (by simpa only [U, Metric.mem_ball, dist_eq_norm] using hz))
  have havoid : U ⊆ (range (m.localDetour s))ᶜ := by
    intro z hz
    have hrgt := (imageDetour_right_of_near_imageContour (hpreU z hz).2).2.2
    rintro ⟨t, ht⟩
    have he : imageDetour s t = m.forward z := by
      exact (m.right_inverse _ (imageDetour_mem_modelHalfPlane s t)).symm.trans
        (congrArg m.forward ht)
    have hti : t = (m.forward z).im := by
      simpa [imageDetour, imageContour] using congrArg Complex.im he
    have hre := congrArg Complex.re he
    rw [hti] at hre
    exact hrgt.ne hre.symm
  obtain ⟨hproper, hρ, -⟩ :=
    m.proper_contour_and_localDetour_holomorphy.2 s m.integrable_density
  have hJ : DifferentiableOn ℂ J U := fun z hz ↦
    (hasDerivAt_cauchyIntegral hproper hρ (havoid hz)).differentiableAt.differentiableWithinAt
  refine ⟨(fun z hz ↦ (hpreU z hz).1), havoid, hJ, ?_⟩
  have hf : AnalyticOnNhd ℂ m.canonicalEntire U :=
    m.canonicalEntire_spec.1.differentiableOn.analyticOnNhd Metric.isOpen_ball
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hJ.analyticOnNhd Metric.isOpen_ball)
      (convex_ball _ _).isPreconnected (Metric.mem_ball_self hr)
      (m.canonicalEntire_eventuallyEq_localDetour s)

#print axioms imageDetour_mem_modelHalfPlane
#print axioms imageDetour_right_of_near_imageContour
#print axioms imageDetour_separation
#print axioms exists_scaled_contour_preimage_neighborhood
#print axioms NormalizedModel.canonicalEntire_eventuallyEq_localDetour
#print axioms exists_scaled_localDetour_agreement

end MaxModulusPoints.CauchyApproximation
