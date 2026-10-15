import MaxModulusPoints.CauchyApproximation.AdmissibleModification
import MaxModulusPoints.CauchyApproximation.ContourRegularity
import MaxModulusPoints.CauchyApproximation.Holomorphy
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
import MaxModulusPoints.CauchyApproximation.LocalDetour
import MaxModulusPoints.CauchyApproximation.Model
/-!
# Holomorphic Cauchy integrals on the specified detours

The escape condition on the conformal inverse makes the canonical contour
proper: its image-domain imaginary coordinate already escapes with the
parameter. When its density is integrable, compact modification preserves
that integrability for the piecewise C¹ detour. The detour integral is then
holomorphic on a whole neighborhood of the original contour point.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The canonical contour is proper. If its density is integrable, every
specified detour has integrable density and a Cauchy integral holomorphic
on a neighborhood of the original contour point. -/
theorem NormalizedModel.proper_contour_and_localDetour_holomorphy (m : NormalizedModel) :
    IsProperMap m.contour ∧
      ∀ s : ℝ, Integrable m.density →
        let η := m.localDetour s
        let ρ : ℝ → ℂ := fun t ↦ m.modelFunction (η t) * deriv η t
        IsProperMap η ∧ Integrable ρ ∧
          ∃ ε : ℝ, 0 < ε ∧ Metric.ball (m.contour s) ε ⊆ (range η)ᶜ ∧
            DifferentiableOn ℂ (cauchyIntegral η ρ) (Metric.ball (m.contour s) ε) := by
  classical
  have hαmem (t : ℝ) : imageContour t ∈ modelHalfPlane := by
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
    simp only [imageContour, add_im, ofReal_im, mul_im, ofReal_re, mul_re,
      I_im, I_re, mul_one, mul_zero, add_zero, zero_add, add_re, sub_zero]
    linarith [Real.posLog_nonneg (x := |t|)]
  have hαlower (t : ℝ) : |t| ≤ ‖imageContour t‖ := by
    simpa [imageContour] using Complex.abs_im_le_norm (imageContour t)
  have hescape : ∀ R : ℝ, ∃ S : ℝ, ∀ t : ℝ, S ≤ |t| → R ≤ ‖m.contour t‖ := by
    intro R
    by_contra! h
    choose t htN htR using fun n : ℕ ↦ h (n : ℝ)
    have hαnorm : Tendsto (fun n : ℕ ↦ ‖imageContour (t n)‖) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ (htN n).trans (hαlower (t n)))
        tendsto_natCast_atTop_atTop
    have hγnorm := m.inverse_infinity (fun n ↦ imageContour (t n))
      (fun n ↦ hαmem (t n)) hαnorm
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hγnorm.eventually_ge_atTop R)
    exact (htR N).not_ge (hN N le_rfl)
  have hnorm : Tendsto (fun t : ℝ ↦ ‖m.contour t‖) (cocompact ℝ) atTop := by
    refine tendsto_atTop.2 fun R ↦ ?_
    obtain ⟨S, hS⟩ := hescape R
    filter_upwards [(tendsto_norm_cocompact_atTop :
      Tendsto (fun t : ℝ ↦ ‖t‖) (cocompact ℝ) atTop).eventually_ge_atTop S] with t ht
    exact hS t (by simpa only [Real.norm_eq_abs] using ht)
  have hαcont : Continuous imageContour := by
    unfold imageContour
    fun_prop
  have hcont : Continuous m.contour :=
    m.holomorphic_inverse.continuousOn.comp_continuous hαcont hαmem
  have hproper : IsProperMap m.contour := by
    apply isProperMap_iff_tendsto_cocompact.2
    refine ⟨hcont, ?_⟩
    simpa only [Metric.cobounded_eq_cocompact] using
      tendsto_norm_atTop_iff_cobounded.1 hnorm
  refine ⟨hproper, ?_⟩
  intro s hρ
  dsimp only
  obtain ⟨hηcont, hηmem, hagree, hηproper, ε, hε, hball⟩ :=
    m.localDetour_properties s hproper
  have hpc := (m.contour_and_localDetour_piecewiseC1 s (s - 1) (s + 1)).2
  have hg : ContinuousOn m.modelFunction m.domain :=
    Complex.continuous_exp.comp_continuousOn m.holomorphic_forward.continuousOn
  have hρη : Integrable (fun t : ℝ ↦
      m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t) :=
    (proper_and_integrable_of_compact_modification hproper hηcont hρ
      (by linarith : s - 1 ≤ s + 1) hpc hg (fun t _ ↦ hηmem t)
      (fun t ht ↦ (hagree t (fun hi ↦ ht ⟨hi.1.le, hi.2.le⟩)).symm)).2
  refine ⟨hηproper, hρη, ε, hε, hball, ?_⟩
  intro z hz
  exact (hasDerivAt_cauchyIntegral hηproper hρη (hball hz)).differentiableAt.differentiableWithinAt

#print axioms NormalizedModel.proper_contour_and_localDetour_holomorphy

end MaxModulusPoints.CauchyApproximation
