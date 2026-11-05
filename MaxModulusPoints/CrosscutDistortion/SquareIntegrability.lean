module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith

/-!
# Integrability of a nonnegative density from its square

On a finite measure space, a nonnegative real density with integrable
square is integrable. Its measurability follows by taking the square
root, so a separate measurability hypothesis on the density is unnecessary.
-/


@[expose] public section

universe u

namespace MaxModulusPoints.CrosscutDistortion

open Set MeasureTheory

/-- A nonnegative real function with integrable square is integrable on a
finite measure space, including when nonnegativity only holds a.e. -/
theorem integrable_nonneg_of_integrable_square {α : Type u} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (g : α → ℝ)
    (hnonneg : 0 ≤ᵐ[μ] g) (hsquare : Integrable (fun x => (g x) ^ 2) μ) :
    Integrable g μ := by
  have hmeas : AEStronglyMeasurable g μ := by
    have hsqrt := hsquare.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    apply hsqrt.congr
    filter_upwards [hnonneg] with x hx
    exact Real.sqrt_sq hx
  apply (hsquare.add (integrable_const (1 : ℝ))).mono' hmeas
  filter_upwards [hnonneg] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx]
  change g x ≤ (g x) ^ 2 + 1
  nlinarith [sq_nonneg (g x - 1 / 2)]

/-- The finite-measure square-integrability implication on a real interval. -/
theorem intervalIntegrable_nonneg_of_square (g : ℝ → ℝ) (a b : ℝ)
    (hnonneg : 0 ≤ᵐ[volume.restrict (uIoc a b)] g)
    (hsquare : IntervalIntegrable (fun t => (g t) ^ 2) volume a b) :
    IntervalIntegrable g volume a b := by
  letI : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    rw [uIoc]
    infer_instance
  apply intervalIntegrable_iff.mpr
  exact integrable_nonneg_of_integrable_square (volume.restrict (uIoc a b)) g
    hnonneg hsquare.def'

end MaxModulusPoints.CrosscutDistortion
