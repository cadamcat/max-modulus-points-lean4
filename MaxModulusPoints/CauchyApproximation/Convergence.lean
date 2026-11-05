module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import MaxModulusPoints.CauchyApproximation.DensityBounds
public import MaxModulusPoints.CauchyApproximation.Holomorphy
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral

/-!
# Convergence and holomorphy under polynomial contour estimates

This is the absolute-convergence and holomorphy part of Rempe-Gillen's
Theorem 2.1. Escape to infinity makes the contour proper, while the polynomial
bounds make its density integrable. Injectivity, orientation, and a bound in a
neighborhood of the contour enter the subsequent gluing and decay arguments.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- A holomorphic function with the prescribed polynomial decay along a
continuous curve to infinity has an absolutely convergent Cauchy integral,
which is holomorphic off the curve and is the limit of its finite truncations. -/
theorem cauchyIntegral_of_polynomial_bounds {T : Set ℂ} {g : ℂ → ℂ} {γ : ℝ → ℂ}
    (hg : DifferentiableOn ℂ g T) (hγ : Continuous γ) (hγT : ∀ t, γ t ∈ T)
    (hescape : ∀ R : ℝ, ∃ S : ℝ, ∀ t : ℝ, S ≤ |t| → R ≤ ‖γ t‖)
    {C₂ C₃ δ₁ δ₂ : ℝ} (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hδ₂ : 0 ≤ δ₂)
    (hgb : ∀ t, ‖g (γ t)‖ ≤ C₃ * (max |t| 1) ^ (-(2 + δ₁ + δ₂)))
    (hγb : ∀ t, ‖deriv γ t‖ ≤ C₂ * (max |t| 1) ^ δ₁) :
    let ρ : ℝ → ℂ := fun t ↦ g (γ t) * deriv γ t
    Integrable ρ ∧ DifferentiableOn ℂ (cauchyIntegral γ ρ) (range γ)ᶜ ∧
      ∀ z ∉ range γ,
        Integrable (fun t : ℝ ↦ ρ t / (γ t - z)) ∧
          Tendsto (fun R : ℝ ↦ (2 * (Real.pi : ℂ) * I)⁻¹ *
            ∫ t in -R..R, ρ t / (γ t - z)) atTop (𝓝 (cauchyIntegral γ ρ z)) := by
  dsimp only
  have hnorm : Tendsto (fun t : ℝ ↦ ‖γ t‖) (cocompact ℝ) atTop := by
    refine tendsto_atTop.2 fun R ↦ ?_
    obtain ⟨S, hS⟩ := hescape R
    filter_upwards [(tendsto_norm_cocompact_atTop :
      Tendsto (fun t : ℝ ↦ ‖t‖) (cocompact ℝ) atTop).eventually_ge_atTop S] with t ht
    exact hS t (by simpa only [Real.norm_eq_abs] using ht)
  have hproper : IsProperMap γ := by
    apply isProperMap_iff_tendsto_cocompact.2
    refine ⟨hγ, ?_⟩
    simpa only [Metric.cobounded_eq_cocompact] using
      tendsto_norm_atTop_iff_cobounded.1 hnorm
  have hdensity : Integrable (fun t : ℝ ↦ g (γ t) * deriv γ t) :=
    integrable_density_of_polynomial_bounds
      (hg.continuousOn.comp_continuous hγ hγT).aestronglyMeasurable
      (aestronglyMeasurable_deriv γ volume) hC₂ hC₃ hδ₂ hgb hγb
  refine ⟨hdensity, ?_, ?_⟩
  · intro z hz
    exact (hasDerivAt_cauchyIntegral hproper hdensity hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact cauchyIntegral_converges_of_integrable hproper hdensity hz

#print axioms cauchyIntegral_of_polynomial_bounds

end MaxModulusPoints.CauchyApproximation
