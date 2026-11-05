module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A rectangular length–area lower bound

A length density whose integral across each vertical slice is at least one
has squared integral at least the width divided by the height. For a tunnel
of width one half, this is the term `1 / (2 * h)` in the crosscut distortion
estimate.
-/


@[expose] public section

namespace MaxModulusPoints.CrosscutDistortion

open MeasureTheory Set

/-- The sharp rectangular energy lower bound for unit vertical slice lengths.
The slice and total energy integrability assumptions are explicit; no boundary
extension of a conformal map is presumed. -/
theorem rectangle_energy_lower_bound
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) (g : ℝ → ℝ → ℝ)
    (hlinear : ∀ x ∈ Ioo a b,
      IntervalIntegrable (g x) volume (-h / 2) (h / 2))
    (hsquare : ∀ x ∈ Ioo a b,
      IntervalIntegrable (fun y => (g x y) ^ 2) volume (-h / 2) (h / 2))
    (hlength : ∀ x ∈ Ioo a b, 1 ≤ ∫ y in (-h / 2)..(h / 2), g x y)
    (henergy : IntervalIntegrable
      (fun x => ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2) volume a b) :
    (b - a) / h ≤ ∫ x in a..b, ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2 := by
  have hslicebound : ∀ x ∈ Ioo a b,
      1 / h ≤ ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2 := by
    intro x hx
    have hnonneg := intervalIntegral.integral_nonneg (μ := volume)
      (show -h / 2 ≤ h / 2 by linarith)
      (fun y _ => sq_nonneg (g x y - 1 / h))
    have hexpand : (fun y => (g x y - 1 / h) ^ 2) =
        (fun y => (g x y) ^ 2 - (2 / h) * g x y + (1 / h) ^ 2) := by
      funext y
      ring
    rw [hexpand, intervalIntegral.integral_add
      ((hsquare x hx).sub ((hlinear x hx).const_mul (2 / h))) intervalIntegrable_const,
      intervalIntegral.integral_sub (hsquare x hx) ((hlinear x hx).const_mul (2 / h)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnonneg
    simp only [smul_eq_mul] at hnonneg
    have hconstant : (h / 2 - (-h / 2)) * (1 / h) ^ 2 = 1 / h := by
      field_simp [ne_of_gt hh]
      <;> ring
    rw [hconstant] at hnonneg
    have hlength' := mul_le_mul_of_nonneg_left (hlength x hx)
      (show 0 ≤ 2 / h by positivity)
    linarith only [hnonneg, hlength', (show 2 / h = 2 * (1 / h) by ring)]
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / h) volume a b)
    henergy hslicebound
  simpa [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using hbound

end MaxModulusPoints.CrosscutDistortion
