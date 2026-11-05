module

public import TauCeti.Analysis.Contour.Argument.Cycle
public import MaxModulusPoints.CauchyApproximation.ContourRegularity
public import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
public import MaxModulusPoints.CauchyApproximation.DetourHomology
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral
public import MaxModulusPoints.CauchyApproximation.LocalDetour
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.ResidueJump

/-!
# Conformal transfer of the detour winding number

The argument principle transfers the winding number of the concrete detour
loop to its image in the enlarged half-plane. The translated conformal map
has exactly one zero in the tract, and its holomorphic inverse makes that
zero simple. Thus the graph geometry in the image domain determines the
winding number needed for the local Cauchy jump.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open TauCeti.Contour
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The actual detour loop and its image-domain graph loop have the same
winding number at corresponding points off the two contours. -/
theorem NormalizedModel.localDetour_windingNumber_forward (m : NormalizedModel) (s : ℝ)
    {z : ℂ} (hz : z ∈ m.domain) (hzγ : z ∉ range m.contour)
    (hzη : z ∉ range (m.localDetour s)) :
    windingNumber (closedContourDifference imageContour (imageDetour s) (s + 1))
        (s - 1) (s + 3) (m.forward z) =
      windingNumber (closedContourDifference m.contour (m.localDetour s) (s + 1))
        (s - 1) (s + 3) z := by
  let K := closedContourDifference m.contour (m.localDetour s) (s + 1)
  let F : ℂ → ℂ := fun w ↦ m.forward w - m.forward z
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hf (w : ℂ) (hw : w ∈ m.domain) : AnalyticAt ℂ m.forward w :=
    m.holomorphic_forward.analyticAt (m.isOpen_domain.mem_nhds hw)
  have hF (w : ℂ) (hw : w ∈ m.domain) : AnalyticAt ℂ F w :=
    (hf w hw).sub analyticAt_const
  have hderiv : deriv m.forward z ≠ 0 := by
    have hcomp := ((m.holomorphic_inverse (m.forward z) (m.forward_mem hz)).differentiableAt
      (hH.mem_nhds (m.forward_mem hz))).hasDerivAt.comp z
        ((m.holomorphic_forward z hz).differentiableAt
          (m.isOpen_domain.mem_nhds hz)).hasDerivAt
    have heq : m.inverse ∘ m.forward =ᶠ[𝓝 z] id := by
      filter_upwards [m.isOpen_domain.mem_nhds hz] with w hw
      exact m.left_inverse w hw
    have hmul : deriv m.inverse (m.forward z) * deriv m.forward z = 1 := by
      exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact zero_ne_one hmul
  have horder : meromorphicOrderAt F z = ((1 : ℤ) : WithTop ℤ) := by
    rw [(hF z hz).meromorphicOrderAt_eq]
    simp [F, (hf z hz).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv]
  have hnonzero (w : ℂ) (hw : w ∈ m.domain) (hwz : w ≠ z) : F w ≠ 0 := by
    intro hzero
    have heq : m.forward w = m.forward z := sub_eq_zero.1 hzero
    apply hwz
    calc
      w = m.inverse (m.forward w) := (m.left_inverse w hw).symm
      _ = m.inverse (m.forward z) := congrArg m.inverse heq
      _ = z := m.left_inverse z hz
  have hproper := m.proper_contour_and_localDetour_holomorphy.1
  obtain ⟨-, hηmem, hagree, -, -⟩ := m.localDetour_properties s hproper
  obtain ⟨hγpc, hηpc⟩ := m.contour_and_localDetour_piecewiseC1 s (s - 1) (s + 1)
  have hbb : 2 * (s + 1) - (s + 1) = s + 1 := by ring
  have hca : 2 * (s + 1) - (s - 1) = s + 3 := by ring
  have haa : 2 * (s + 1) - (s + 3) = s - 1 := by ring
  have hrev : IsPiecewiseC1On (fun t ↦ m.localDetour s (2 * (s + 1) - t))
      (s + 1) (s + 3) := by
    simpa only [hbb, hca] using (hηpc.comp_const_sub (2 * (s + 1))).symm
  have hb : m.contour (s + 1) = m.localDetour s (2 * (s + 1) - (s + 1)) := by
    simpa only [hbb] using (hagree (s + 1) (by simp)).symm
  have hK : IsPiecewiseC1On K (s - 1) (s + 3) :=
    hγpc.if_le hrev (by linarith) (by linarith) hb
  have hclosed : K (s - 1) = K (s + 3) := by
    dsimp only [K, closedContourDifference]
    rw [if_pos (by linarith : s - 1 ≤ s + 1),
      if_neg (by linarith : ¬ s + 3 ≤ s + 1), haa]
    exact (hagree (s - 1) (by simp)).symm
  have hαmem (t : ℝ) : imageContour t ∈ modelHalfPlane := by
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
    simp only [imageContour, add_im, ofReal_im, mul_im, ofReal_re, mul_re,
      I_im, I_re, mul_one, mul_zero, add_zero, zero_add, add_re, sub_zero]
    linarith [Real.posLog_nonneg (x := |t|)]
  have hKT (t : ℝ) : K t ∈ m.domain := by
    by_cases ht : t ≤ s + 1
    · simp only [K, closedContourDifference, if_pos ht]
      exact m.inverse_mem (hαmem t)
    · simp only [K, closedContourDifference, if_neg ht]
      exact hηmem _
  have hoff (t : ℝ) : K t ≠ z := by
    by_cases ht : t ≤ s + 1
    · simpa only [K, closedContourDifference, if_pos ht] using
        (fun h ↦ hzγ ⟨t, h⟩)
    · simpa only [K, closedContourDifference, if_neg ht] using
        (fun h ↦ hzη ⟨2 * (s + 1) - t, h⟩)
  have harg := argumentPrinciple_nullHomologous_local m.isOpen_domain
    (fun _ ↦ (hF z hz).meromorphicAt) (fun _ ↦ horder)
    (fun w hw hwz ↦ ⟨hF w hw, hnonzero w hw hwz⟩)
    hK (fun t _ ↦ hKT t) hclosed (fun t _ ↦ hoff t)
    (m.localDetour_nullHomologous s)
  have hwind : windingNumber (F ∘ K) (s - 1) (s + 3) 0 =
      windingNumber K (s - 1) (s + 3) z := by
    rw [windingNumber_comp_eq_integral_logDeriv hK
      (fun t _ ↦ hF _ (hKT t)) (fun t _ ↦ hnonzero _ (hKT t) (hoff t)), harg]
    simp only [Int.cast_one, mul_one, inv_mul_cancel_left₀ Complex.two_pi_I_ne_zero]
  have htranslate : windingNumber (F ∘ K) (s - 1) (s + 3) 0 =
      windingNumber (m.forward ∘ K) (s - 1) (s + 3) (m.forward z) := by
    rw [windingNumber_eq_cauchyPVAt, windingNumber_eq_cauchyPVAt]
    congr 1
    simpa [F, Function.comp_def, sub_eq_add_neg, add_assoc] using
      (cauchyPVAt_translate (γ := m.forward ∘ K) (a := s - 1) (b := s + 3)
        (f := fun w : ℂ ↦ (w - m.forward z)⁻¹) (z₀ := m.forward z) (-m.forward z))
  have himage : m.forward ∘ K =
      closedContourDifference imageContour (imageDetour s) (s + 1) := by
    funext t
    by_cases ht : t ≤ s + 1
    · simp only [Function.comp_apply, K, closedContourDifference, if_pos ht,
        NormalizedModel.contour]
      exact m.right_inverse _ (hαmem t)
    · simp only [Function.comp_apply, K, closedContourDifference, if_neg ht,
        NormalizedModel.localDetour]
      have hδmem : imageDetour s (2 * (s + 1) - t) ∈ modelHalfPlane := by
        have h := hαmem (2 * (s + 1) - t)
        change -14 * Real.posLog |(imageContour _).im| < (imageContour _).re at h
        change -14 * Real.posLog |(imageDetour s _).im| < (imageDetour s _).re
        simp only [imageDetour, add_im, ofReal_im, add_zero, add_re, ofReal_re]
        linarith [le_max_left (0 : ℝ) (1 - |2 * (s + 1) - t - s|)]
      exact m.right_inverse _ hδmem
  rw [← himage]
  exact htranslate.symm.trans hwind

#print axioms NormalizedModel.localDetour_windingNumber_forward

end MaxModulusPoints.CauchyApproximation
