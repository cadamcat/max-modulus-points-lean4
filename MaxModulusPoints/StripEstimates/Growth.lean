module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exponential growth from logarithmic derivative bounds

The real-variable implication used in Pardo-Simón–Sixsmith, Lemma 2.6,
equation (2.9). Its geometric input is a positive real restriction of a
normalized conformal map, together with bounds on its logarithmic derivative.
-/


@[expose] public section

namespace MaxModulusPoints.StripEstimates

/-- A positive differentiable function with logarithmic derivative between
`a` and `A` satisfies the corresponding two-sided exponential growth bound. -/
theorem exp_growth_of_log_deriv_bounds {ψ : ℝ → ℝ} {a A : ℝ}
    (hpos : ∀ x : ℝ, 0 < ψ x) (hdiff : Differentiable ℝ ψ)
    (hlower : ∀ x : ℝ, a ≤ deriv ψ x / ψ x)
    (hupper : ∀ x : ℝ, deriv ψ x / ψ x ≤ A)
    (s u : ℝ) (hu : 0 ≤ u) :
    Real.exp (a * u) * ψ s ≤ ψ (s + u) ∧
      ψ (s + u) ≤ Real.exp (A * u) * ψ s := by
  have hdlog (x : ℝ) :
      HasDerivAt (fun t : ℝ => Real.log (ψ t)) (deriv ψ x / ψ x) x :=
    (hdiff x).hasDerivAt.log (ne_of_gt (hpos x))
  have hlogdiff : Differentiable ℝ (fun t : ℝ => Real.log (ψ t)) :=
    fun x => (hdlog x).differentiableAt
  have hlow := mul_sub_le_image_sub_of_le_deriv hlogdiff
    (fun x => (hdlog x).deriv.symm ▸ hlower x) (x := s) (y := s + u) (by linarith)
  have hupp := image_sub_le_mul_sub_of_deriv_le hlogdiff
    (fun x => (hdlog x).deriv.symm ▸ hupper x) (x := s) (y := s + u) (by linarith)
  constructor
  · calc
      Real.exp (a * u) * ψ s = Real.exp (a * u + Real.log (ψ s)) := by
        rw [Real.exp_add, Real.exp_log (hpos s)]
      _ ≤ Real.exp (Real.log (ψ (s + u))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = ψ (s + u) := Real.exp_log (hpos (s + u))
  · calc
      ψ (s + u) = Real.exp (Real.log (ψ (s + u))) :=
        (Real.exp_log (hpos (s + u))).symm
      _ ≤ Real.exp (A * u + Real.log (ψ s)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (A * u) * ψ s := by
        rw [Real.exp_add, Real.exp_log (hpos s)]

end MaxModulusPoints.StripEstimates
