module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import MaxModulusPoints.CauchyApproximation.ContourRegularity
public import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral
public import MaxModulusPoints.CauchyApproximation.LocalDetour
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.ResidueJump

/-!
# Null-homology of the concrete detour loop

The finite difference of the interior contour and its local detour is a
closed piecewise C¹ curve in the simply connected tract. For every point
outside the tract, a holomorphic logarithm of the translated coordinate
provides a primitive of the winding kernel. The fundamental theorem of
calculus across the finitely many corners makes its winding number zero.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open TauCeti.Contour
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The closed difference of the canonical contour and its specified detour
is null-homologous in the tract. -/
theorem NormalizedModel.localDetour_nullHomologous (m : NormalizedModel) (s : ℝ) :
    IsNullHomologous (closedContourDifference m.contour (m.localDetour s) (s + 1))
      (s - 1) (s + 3) m.domain := by
  have hsimply {θ : ℝ → ℂ} {a b : ℝ} (hθ : IsPiecewiseC1On θ a b)
      (hθT : ∀ t ∈ uIcc a b, θ t ∈ m.domain) (hclosed : θ a = θ b) :
      IsNullHomologous θ a b m.domain := by
    rw [isNullHomologous_iff]
    intro w hw
    have hnonzero : (0 : ℂ) ∉ (fun z : ℂ ↦ z - w) '' m.domain := by
      rintro ⟨z, hz, heq⟩
      exact hw ((sub_eq_zero.1 heq) ▸ hz)
    obtain ⟨L, hL, hLeq⟩ := TauCeti.exists_differentiableOn_eqOn_exp_comp
      m.simplyConnected_domain m.isOpen_domain (differentiableOn_id.sub_const w) hnonzero
    have hLder (z : ℂ) (hz : z ∈ m.domain) : HasDerivAt L ((z - w)⁻¹) z := by
      have h := ((hL z hz).differentiableAt (m.isOpen_domain.mem_nhds hz)).hasDerivAt
      rw [TauCeti.deriv_eq_logDeriv_of_eqOn_exp_comp m.isOpen_domain hL hLeq hz] at h
      simpa [logDeriv] using h
    have hoff (t : ℝ) (ht : t ∈ uIcc a b) : θ t ≠ w := fun heq ↦
      hw (heq ▸ hθT t ht)
    have hint := intervalIntegrable_inv_sub_mul_deriv hθ.continuousOn hoff
      hθ.intervalIntegrable_deriv
    obtain ⟨P, hP, hdiff⟩ := hθ.exists_countable_differentiableAt
    have hD : ∀ t ∈ Ioo (min a b) (max a b) \ P,
        HasDerivAt (L ∘ θ) ((θ t - w)⁻¹ * deriv θ t) t := by
      intro t ht
      simpa only [Function.comp_apply, smul_eq_mul, mul_comm] using
        (hLder (θ t) (hθT t (Ioo_subset_Icc_self ht.1))).scomp t (hdiff t ht).hasDerivAt
    have hFTC := integral_eq_of_hasDerivAt_off_countable (L ∘ θ)
      (fun t ↦ (θ t - w)⁻¹ * deriv θ t) hP
      (hL.continuousOn.comp hθ.continuousOn hθT) hD hint
    rw [windingNumber_eq_integral_of_avoidance hθ.continuousOn hoff hint, hFTC]
    simp only [Function.comp_apply, hclosed, sub_self, mul_zero]
  have hproper := m.proper_contour_and_localDetour_holomorphy.1
  obtain ⟨-, hηmem, hagree, -, -⟩ := m.localDetour_properties s hproper
  obtain ⟨hγpc, hηpc⟩ := m.contour_and_localDetour_piecewiseC1 s (s - 1) (s + 1)
  let ηrev : ℝ → ℂ := fun t ↦ m.localDetour s (2 * (s + 1) - t)
  let K := closedContourDifference m.contour (m.localDetour s) (s + 1)
  have hbb : 2 * (s + 1) - (s + 1) = s + 1 := by ring
  have hca : 2 * (s + 1) - (s - 1) = s + 3 := by ring
  have haa : 2 * (s + 1) - (s + 3) = s - 1 := by ring
  have hrev : IsPiecewiseC1On ηrev (s + 1) (s + 3) := by
    simpa only [hbb, hca] using (hηpc.comp_const_sub (2 * (s + 1))).symm
  have hb : m.contour (s + 1) = ηrev (s + 1) := by
    simpa only [ηrev, hbb] using (hagree (s + 1) (by simp)).symm
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
  exact hsimply hK (fun t _ ↦ hKT t) hclosed

#print axioms NormalizedModel.localDetour_nullHomologous

end MaxModulusPoints.CauchyApproximation
