import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Complex.Basic
/-!
# Absolutely convergent Cauchy integrals on proper curves

The density of a parametrized Cauchy integral is `g (γ t) * deriv γ t`.
Absolute integrability of this density and properness of the curve suffice for
absolute convergence at every point off the curve. This is the convergence step
in Theorem 2.1 of Rempe-Gillen, *Hyperbolic entire functions with full hyperbolic
dimension and approximation by Eremenko–Lyubich functions*.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The Cauchy transform of an integrable density on a real-parametrized curve. -/
noncomputable def cauchyIntegral (γ ρ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t : ℝ, ρ t / (γ t - z)

/-- The improper Cauchy integral converges absolutely off a proper curve, and
its finite truncations converge to its Bochner-integral value. -/
theorem cauchyIntegral_converges_of_integrable {γ ρ : ℝ → ℂ}
    (hγ : IsProperMap γ) (hρ : Integrable ρ) {z : ℂ} (hz : z ∉ range γ) :
    Integrable (fun t : ℝ ↦ ρ t / (γ t - z)) ∧
      Tendsto (fun R : ℝ ↦ (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ t in -R..R, ρ t / (γ t - z)) atTop (𝓝 (cauchyIntegral γ ρ z)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hγ.isClosed_range.isOpen_compl z hz
  have hsep (t : ℝ) : ε ≤ ‖γ t - z‖ := by
    by_contra! h
    exact hball (by simpa [Metric.mem_ball, dist_eq_norm] using h) ⟨t, rfl⟩
  have hint : Integrable (fun t : ℝ ↦ ρ t / (γ t - z)) := by
    apply (hρ.norm.div_const ε).mono'
      (hρ.aestronglyMeasurable.div₀
        ((hγ.continuous.sub continuous_const).aestronglyMeasurable))
    exact ae_of_all _ fun t ↦ by
      change ‖ρ t / (γ t - z)‖ ≤ ‖ρ t‖ / ε
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hε (hsep t)
  refine ⟨hint, ?_⟩
  exact (intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id).const_mul _

#print axioms cauchyIntegral_converges_of_integrable

end MaxModulusPoints.CauchyApproximation
