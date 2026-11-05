module

public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# A local detour of the interior contour

Adding a nonnegative tent function to the real coordinate of the image
contour keeps it in the enlarged half-plane. Its imaginary coordinate remains
the parameter, so the shifted graph misses the original point at the centre
of the tent. The conformal inverse transfers the detour to the tract. If the
original contour is proper, the detour avoids a whole neighborhood of that
point and retains the original tails.
-/


@[expose] public section

open Complex Filter Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Shift the image contour to the right on the interval `[s-1, s+1]`. -/
noncomputable def imageDetour (s t : ℝ) : ℂ :=
  imageContour t + (max 0 (1 - |t - s|) : ℝ)

/-- Transfer the shifted graph to the tract using the conformal inverse. -/
noncomputable def NormalizedModel.localDetour (m : NormalizedModel) (s : ℝ) : ℝ → ℂ :=
  m.inverse ∘ imageDetour s

/-- A proper interior contour admits this continuous compact modification in
the tract, whose entire image avoids a neighborhood of the original point. -/
theorem NormalizedModel.localDetour_properties (m : NormalizedModel) (s : ℝ)
    (hproper : IsProperMap m.contour) :
    Continuous (m.localDetour s) ∧
      (∀ t, m.localDetour s t ∈ m.domain) ∧
      (∀ t ∉ Ioo (s - 1) (s + 1), m.localDetour s t = m.contour t) ∧
      IsProperMap (m.localDetour s) ∧
      ∃ ε : ℝ, 0 < ε ∧
        Metric.ball (m.contour s) ε ⊆ (range (m.localDetour s))ᶜ := by
  have hαmem (t : ℝ) : imageContour t ∈ modelHalfPlane := by
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
    simp only [imageContour, add_im, ofReal_im, mul_im, ofReal_re, mul_re,
      I_im, I_re, mul_one, mul_zero, add_zero, zero_add, add_re, sub_zero]
    have hlog := Real.posLog_nonneg (x := |t|)
    linarith
  have hδmem (t : ℝ) : imageDetour s t ∈ modelHalfPlane := by
    have h := hαmem t
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re at h
    change -14 * Real.posLog |(imageDetour s t).im| < (imageDetour s t).re
    simp only [imageDetour, add_im, ofReal_im, add_zero, add_re, ofReal_re]
    linarith [le_max_left (0 : ℝ) (1 - |t - s|)]
  have hδcont : Continuous (imageDetour s) := by
    unfold imageDetour imageContour
    fun_prop
  have hcont : Continuous (m.localDetour s) :=
    m.holomorphic_inverse.continuousOn.comp_continuous hδcont hδmem
  have hmem (t : ℝ) : m.localDetour s t ∈ m.domain := m.inverse_mem (hδmem t)
  have hagree (t : ℝ) (ht : t ∉ Ioo (s - 1) (s + 1)) :
      m.localDetour s t = m.contour t := by
    have haway : 1 ≤ |t - s| := by
      by_contra! h
      obtain ⟨hl, hr⟩ := abs_lt.1 h
      exact ht ⟨by linarith, by linarith⟩
    have hzero : 1 - |t - s| ≤ 0 := by linarith
    simp only [localDetour, contour, Function.comp_apply, imageDetour,
      max_eq_left hzero, ofReal_zero, add_zero]
  have heq : m.contour =ᶠ[cocompact ℝ] m.localDetour s := by
    have hco : (Icc (s - 1) (s + 1))ᶜ ∈ cocompact ℝ :=
      isCompact_Icc.compl_mem_cocompact
    filter_upwards [hco] with t ht
    exact (hagree t (fun hi ↦ ht ⟨hi.1.le, hi.2.le⟩)).symm
  have hδproper : IsProperMap (m.localDetour s) :=
    isProperMap_iff_tendsto_cocompact.2
      ⟨hcont, (isProperMap_iff_tendsto_cocompact.1 hproper).2.congr' heq⟩
  have hoff : m.contour s ∉ range (m.localDetour s) := by
    rintro ⟨t, ht⟩
    have himage : imageDetour s t = imageContour s := by
      calc
        _ = m.forward (m.inverse (imageDetour s t)) := (m.right_inverse _ (hδmem t)).symm
        _ = m.forward (m.contour s) := congrArg m.forward ht
        _ = imageContour s := m.right_inverse _ (hαmem s)
    have hts : t = s := by
      simpa [imageDetour, imageContour] using congrArg Complex.im himage
    subst t
    have hre := congrArg Complex.re himage
    simp only [imageDetour, sub_self, abs_zero, sub_zero, max_eq_right zero_le_one,
      ofReal_one, add_re, one_re] at hre
    linarith
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 hδproper.isClosed_range.isOpen_compl (m.contour s) hoff
  exact ⟨hcont, hmem, hagree, hδproper, ε, hε, hball⟩

#print axioms NormalizedModel.localDetour_properties

end MaxModulusPoints.CauchyApproximation
