import MaxModulusPoints.CauchyApproximation.ContourRegularity
import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
import MaxModulusPoints.CauchyApproximation.DetourHomology
import MaxModulusPoints.CauchyApproximation.DetourWinding
import MaxModulusPoints.CauchyApproximation.Holomorphy
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
import MaxModulusPoints.CauchyApproximation.LocalDetour
import MaxModulusPoints.CauchyApproximation.Model
import MaxModulusPoints.CauchyApproximation.ResidueJump
/-!
# Analytic agreement across the interior contour

The Cauchy integral on the specified local detour is holomorphic on a ball
about the original contour point. The compact-modification residue identity
and the computed clockwise winding values show that it agrees there with
the original integral plus the prescribed holomorphic function on the core
side, and with the original integral on the other side.
-/

open Complex Filter MeasureTheory Set
open TauCeti.Contour
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The actual detour integral is one holomorphic local extension of the
canonical gluing, conditional on integrability of the original density. -/
theorem NormalizedModel.localDetour_cauchyIntegral_agrees (m : NormalizedModel)
    (s : ℝ) (hρ : Integrable m.density) :
    let η := m.localDetour s
    let ρ : ℝ → ℂ := fun t ↦ m.modelFunction (η t) * deriv η t
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (m.contour s) ε ⊆ m.domain ∧
      DifferentiableOn ℂ (cauchyIntegral η ρ) (Metric.ball (m.contour s) ε) ∧
      ∀ z ∈ Metric.ball (m.contour s) ε, z ∉ range m.contour →
        (z ∈ m.core → cauchyIntegral η ρ z =
          cauchyIntegral m.contour m.density z + m.modelFunction z) ∧
        (z ∉ m.core → cauchyIntegral η ρ z = cauchyIntegral m.contour m.density z) := by
  classical
  dsimp only
  have hγproper := m.proper_contour_and_localDetour_holomorphy.1
  obtain ⟨hηproper, hρη, -⟩ := m.proper_contour_and_localDetour_holomorphy.2 s hρ
  obtain ⟨ε, hε, hballT, havoid, hwind⟩ := m.localDetour_windingNumber s
  have hg : DifferentiableOn ℂ m.modelFunction m.domain := m.holomorphic_forward.cexp
  have hαmem (t : ℝ) : imageContour t ∈ modelHalfPlane := by
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
    simp only [imageContour, add_im, ofReal_im, mul_im, ofReal_re, mul_re,
      I_im, I_re, mul_one, mul_zero, add_zero, zero_add, add_re, sub_zero]
    linarith [Real.posLog_nonneg (x := |t|)]
  obtain ⟨-, hηmem, hagree, -, -⟩ := m.localDetour_properties s hγproper
  obtain ⟨hγpc, hηpc⟩ := m.contour_and_localDetour_piecewiseC1 s (s - 1) (s + 1)
  have hendpoint : 2 * (s + 1) - (s - 1) = s + 3 := by ring
  have hnull : IsNullHomologous
      (closedContourDifference m.contour (m.localDetour s) (s + 1))
      (s - 1) (2 * (s + 1) - (s - 1)) m.domain := by
    simpa only [hendpoint] using m.localDetour_nullHomologous s
  refine ⟨ε, hε, hballT, ?_, ?_⟩
  · intro z hz
    exact (hasDerivAt_cauchyIntegral hηproper hρη (havoid hz)).differentiableAt.differentiableWithinAt
  · intro z hz hzγ
    have hres := cauchyIntegral_sub_eq_winding_mul m.isOpen_domain hg
      hγproper hηproper hρ hρη (by linarith : s - 1 ≤ s + 1) hγpc hηpc
      (fun t _ ↦ m.inverse_mem (hαmem t)) (fun t _ ↦ hηmem t)
      (fun t ht ↦ (hagree t ht).symm) hnull (hballT hz) hzγ (havoid hz)
    rw [hendpoint, hwind z hz hzγ] at hres
    change cauchyIntegral m.contour m.density z -
        cauchyIntegral (m.localDetour s)
          (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t) z =
      (if z ∈ m.core then (-1 : ℂ) else 0) * m.modelFunction z at hres
    constructor
    · intro hzcore
      rw [if_pos hzcore, neg_one_mul] at hres
      calc
        _ = cauchyIntegral m.contour m.density z -
            (cauchyIntegral m.contour m.density z -
              cauchyIntegral (m.localDetour s)
                (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t) z) := by ring
        _ = _ := by rw [hres]; ring
    · intro hzcore
      rw [if_neg hzcore, zero_mul] at hres
      exact (sub_eq_zero.1 hres).symm

#print axioms NormalizedModel.localDetour_cauchyIntegral_agrees

end MaxModulusPoints.CauchyApproximation
