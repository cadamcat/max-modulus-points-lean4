import TauCeti.Analysis.Contour.Curve.Concat
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import MaxModulusPoints.CauchyApproximation.LocalDetour
import MaxModulusPoints.CauchyApproximation.Model
/-!
# Piecewise smoothness of the interior contour and its detour

The positive logarithm in the image contour has two breakpoints, at −1
and 1. The tent perturbation is affine on four pieces. Gluing these pieces
gives piecewise C¹ regularity on every bounded interval. Holomorphy of the
conformal inverse then transfers this regularity to the tract.
-/

open Complex Set
open TauCeti.Contour

namespace MaxModulusPoints.CauchyApproximation

/-- The image contour and its tent detour are piecewise C¹ on every bounded
parameter interval. -/
theorem imageContour_and_imageDetour_piecewiseC1 (s a b : ℝ) :
    IsPiecewiseC1On imageContour a b ∧ IsPiecewiseC1On (imageDetour s) a b := by
  have hcast : ContDiff ℝ 1 (fun t : ℝ ↦ (t : ℂ)) := ofRealCLM.contDiff
  have hline : ContDiff ℝ 1 (fun t : ℝ ↦ (t : ℂ) * I) := hcast.mul contDiff_const
  have hglue {γ : ℝ → ℂ} {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w)
      (h₁ : IsPiecewiseC1On γ u v) (h₂ : IsPiecewiseC1On γ v w) :
      IsPiecewiseC1On γ u w := by
    simpa only [ite_self] using h₁.if_le h₂ huv hvw rfl
  have hα (u v : ℝ) : IsPiecewiseC1On imageContour u v := by
    let L := min (min u v) (-1)
    let R := max (max u v) 1
    have hL : L ≤ -1 := min_le_right _ _
    have hR : 1 ≤ R := le_max_right _ _
    let β : ℝ → ℂ := fun t ↦ ((1 - 13 * Real.log t : ℝ) : ℂ) + t * I
    have hβ {S : Set ℝ} (hS : ∀ t ∈ S, t ≠ 0) : ContDiffOn ℝ 1 β S := by
      have hlog : ContDiffOn ℝ 1 (fun t : ℝ ↦ Real.log t) S := contDiffOn_id.log hS
      exact (hcast.comp_contDiffOn
        (contDiffOn_const.sub (contDiffOn_const.mul hlog))).add hline.contDiffOn
    have houter (t : ℝ) (ht : 1 ≤ |t|) : imageContour t = β t := by
      simp only [imageContour, Real.posLog_abs, Real.posLog_eq_log ht, β]
    have hinner (t : ℝ) (ht : |t| ≤ 1) : imageContour t = 1 + (t : ℂ) * I := by
      simp only [imageContour, Real.posLog_abs, (Real.posLog_eq_zero_iff t).2 ht,
        mul_zero, sub_zero, ofReal_one]
    have hleft : IsPiecewiseC1On imageContour L (-1) := by
      apply IsPiecewiseC1On.of_contDiffOn
      rw [uIcc_of_le hL]
      refine (hβ (fun t ht ↦ by linarith [ht.2])).congr ?_
      intro t ht
      exact houter t (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2])
    have hmid : IsPiecewiseC1On imageContour (-1) 1 := by
      apply IsPiecewiseC1On.of_contDiffOn
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      refine ((contDiff_const (c := (1 : ℂ))).add hline).contDiffOn.congr ?_
      intro t ht
      exact hinner t (abs_le.2 ht)
    have hright : IsPiecewiseC1On imageContour 1 R := by
      apply IsPiecewiseC1On.of_contDiffOn
      rw [uIcc_of_le hR]
      refine (hβ (fun t ht ↦ by linarith [ht.1])).congr ?_
      intro t ht
      exact houter t (ht.1.trans (le_abs_self t))
    have hbig : IsPiecewiseC1On imageContour L R :=
      hglue (by linarith) hR (hglue hL (by norm_num) hleft hmid) hright
    apply hbig.mono
    rw [uIcc_of_le (by linarith : L ≤ R)]
    intro t ht
    exact ⟨(min_le_left _ _).trans ht.1, ht.2.trans (le_max_left _ _)⟩
  let B : ℝ → ℂ := fun t ↦ ((max 0 (1 - |t - s|) : ℝ) : ℂ)
  have hBzero (t : ℝ) (ht : t ≤ s - 1 ∨ s + 1 ≤ t) : B t = 0 := by
    have haway : 1 ≤ |t - s| := by
      rcases ht with ht | ht
      · linarith [neg_le_abs (t - s)]
      · linarith [le_abs_self (t - s)]
    simp only [B, max_eq_left (by linarith : 1 - |t - s| ≤ 0), ofReal_zero]
  have hBup (t : ℝ) (ht : t ∈ Icc (s - 1) s) : B t = ((1 + t - s : ℝ) : ℂ) := by
    have hn : t - s ≤ 0 := by linarith [ht.2]
    have hp : 0 ≤ 1 - |t - s| := by rw [abs_of_nonpos hn]; linarith [ht.1]
    change ((max 0 (1 - |t - s|) : ℝ) : ℂ) = ((1 + t - s : ℝ) : ℂ)
    rw [max_eq_right hp, abs_of_nonpos hn]
    exact congrArg Complex.ofReal (by ring)
  have hBdown (t : ℝ) (ht : t ∈ Icc s (s + 1)) : B t = ((1 - t + s : ℝ) : ℂ) := by
    have hn : 0 ≤ t - s := by linarith [ht.1]
    have hp : 0 ≤ 1 - |t - s| := by rw [abs_of_nonneg hn]; linarith [ht.2]
    change ((max 0 (1 - |t - s|) : ℝ) : ℂ) = ((1 - t + s : ℝ) : ℂ)
    rw [max_eq_right hp, abs_of_nonneg hn]
    exact congrArg Complex.ofReal (by ring)
  have hB : IsPiecewiseC1On B a b := by
    let L := min (min a b) (s - 1)
    let R := max (max a b) (s + 1)
    have hL : L ≤ s - 1 := min_le_right _ _
    have hR : s + 1 ≤ R := le_max_right _ _
    have h₁ : IsPiecewiseC1On B L (s - 1) := by
      apply IsPiecewiseC1On.of_contDiffOn
      rw [uIcc_of_le hL]
      refine (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ (0 : ℂ)) _).congr ?_
      exact fun t ht ↦ hBzero t (Or.inl ht.2)
    have h₂ : IsPiecewiseC1On B (s - 1) s := by
      apply IsPiecewiseC1On.of_contDiffOn
      rw [uIcc_of_le (by linarith : s - 1 ≤ s)]
      refine (hcast.comp (((contDiff_const (c := (1 : ℝ))).add contDiff_id).sub
        (contDiff_const (c := s)))).contDiffOn.congr ?_
      exact hBup
    have h₃ : IsPiecewiseC1On B s (s + 1) := by
      apply IsPiecewiseC1On.of_contDiffOn
      rw [uIcc_of_le (by linarith : s ≤ s + 1)]
      refine (hcast.comp (((contDiff_const (c := (1 : ℝ))).sub contDiff_id).add
        (contDiff_const (c := s)))).contDiffOn.congr ?_
      exact hBdown
    have h₄ : IsPiecewiseC1On B (s + 1) R := by
      apply IsPiecewiseC1On.of_contDiffOn
      rw [uIcc_of_le hR]
      refine (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ (0 : ℂ)) _).congr ?_
      exact fun t ht ↦ hBzero t (Or.inr ht.1)
    have hbig : IsPiecewiseC1On B L R :=
      hglue (by linarith) hR
        (hglue (by linarith) (by linarith)
          (hglue hL (by linarith) h₁ h₂) h₃) h₄
    apply hbig.mono
    rw [uIcc_of_le (by linarith : L ≤ R)]
    intro t ht
    exact ⟨(min_le_left _ _).trans ht.1, ht.2.trans (le_max_left _ _)⟩
  have hδ : IsPiecewiseC1On (imageDetour s) a b := (hα a b).add hB
  exact ⟨hα a b, hδ⟩

/-- The canonical contour and its specified local detour are piecewise C¹
on every bounded parameter interval. -/
theorem NormalizedModel.contour_and_localDetour_piecewiseC1
    (m : NormalizedModel) (s a b : ℝ) :
    IsPiecewiseC1On m.contour a b ∧ IsPiecewiseC1On (m.localDetour s) a b := by
  obtain ⟨hα, hδ⟩ := imageContour_and_imageDetour_piecewiseC1 s a b
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hinverse : ContDiffOn ℝ 1 m.inverse modelHalfPlane :=
    (m.holomorphic_inverse.contDiffOn hH).restrict_scalars ℝ
  have hcompose {γ : ℝ → ℂ} (hγ : IsPiecewiseC1On γ a b)
      (hmem : MapsTo γ (uIcc a b) modelHalfPlane) :
      IsPiecewiseC1On (m.inverse ∘ γ) a b := by
    obtain ⟨p, hp, hC⟩ := hγ.exists_breakpoints
    refine IsPiecewiseC1On.of_breakpoints
      (m.holomorphic_inverse.continuousOn.comp hγ.continuousOn hmem) p hp ?_
    intro c d hcd hdisj
    exact hinverse.comp (hC c d hcd hdisj) (fun t ht ↦ hmem (hcd ht))
  have hαmem (t : ℝ) : imageContour t ∈ modelHalfPlane := by
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
    simp only [imageContour, add_im, ofReal_im, mul_im, ofReal_re, mul_re,
      I_im, I_re, mul_one, mul_zero, add_zero, zero_add, add_re, sub_zero]
    linarith [Real.posLog_nonneg (x := |t|)]
  have hδmem (t : ℝ) : imageDetour s t ∈ modelHalfPlane := by
    have h := hαmem t
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re at h
    change -14 * Real.posLog |(imageDetour s t).im| < (imageDetour s t).re
    simp only [imageDetour, add_im, ofReal_im, add_zero, add_re, ofReal_re]
    linarith [le_max_left (0 : ℝ) (1 - |t - s|)]
  exact ⟨hcompose hα (fun t _ ↦ hαmem t), hcompose hδ (fun t _ ↦ hδmem t)⟩

#print axioms imageContour_and_imageDetour_piecewiseC1
#print axioms NormalizedModel.contour_and_localDetour_piecewiseC1

end MaxModulusPoints.CauchyApproximation
