module

public import MaxModulusPoints.Challenge
public import MaxModulusPoints.FiberContinuation.InverseCoordinates
public import MaxModulusPoints.FiberContinuation.LogarithmicValues

/-!
# Analytic coordinates at poles

The reciprocal of a genuine simple pole extends analytically by zero and has
a nonzero derivative. It therefore has an analytic local inverse.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Filter
open scoped Topology
open MaxModulusPoints.Blueprint

/-- The reciprocal finite formula, extended by zero at zeros of the factor. -/
def reciprocalLogarithmicValue (m : ℕ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if g z = 0 then 0 else (finiteLogarithmicValue m g z)⁻¹

theorem meromorphicOrderAt_reciprocalLogarithmicValue {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (hga : g a = 0) :
    meromorphicOrderAt (reciprocalLogarithmicValue m g) a = 1 := by
  have hne : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 :=
    (hg.analyticAt a).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (not_eventually_zero_of_entire hg hg0 a)
  have heq : reciprocalLogarithmicValue m g =ᶠ[𝓝[≠] a]
      (finiteLogarithmicValue m g)⁻¹ := by
    filter_upwards [hne] with z hz
    simp [reciprocalLogarithmicValue, hz]
  calc
    meromorphicOrderAt (reciprocalLogarithmicValue m g) a =
        meromorphicOrderAt ((finiteLogarithmicValue m g)⁻¹) a := meromorphicOrderAt_congr heq
    _ = -meromorphicOrderAt (finiteLogarithmicValue m g) a := meromorphicOrderAt_inv
    _ = 1 := by rw [meromorphicOrderAt_finiteLogarithmicValue hg hg0 m hga]; rfl

/-- The reciprocal spherical coordinate is analytic at every pole. -/
theorem analyticAt_reciprocalLogarithmicValue {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (hga : g a = 0) :
    AnalyticAt ℂ (reciprocalLogarithmicValue m g) a := by
  apply AnalyticAt.of_meromorphicOrderAt_pos
  · rw [meromorphicOrderAt_reciprocalLogarithmicValue hg hg0 m hga]
    exact WithTop.coe_lt_coe.mpr (show (0 : ℤ) < 1 from zero_lt_one)
  · simp [reciprocalLogarithmicValue, hga]

/-- A simple pole has a conformal reciprocal coordinate. -/
theorem deriv_reciprocalLogarithmicValue_ne_zero {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (hga : g a = 0) :
    deriv (reciprocalLogarithmicValue m g) a ≠ 0 := by
  have hr := analyticAt_reciprocalLogarithmicValue hg hg0 m hga
  have horder : meromorphicOrderAt (deriv (reciprocalLogarithmicValue m g)) a = 0 := by
    apply meromorphicOrderAt_deriv (n := 0)
    · simp
    · simpa using meromorphicOrderAt_reciprocalLogarithmicValue hg hg0 m hga
  obtain ⟨c, hc, hlim⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hr.deriv.meromorphicAt horder
  have heq : deriv (reciprocalLogarithmicValue m g) a = c :=
    tendsto_nhds_unique hr.deriv.continuousAt.continuousWithinAt.tendsto hlim
  intro hzero
  exact hc (heq.symm.trans hzero)

/-- The reciprocal at a pole has a local analytic power chart with inverse. -/
theorem exists_pole_power_coordinate {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (hga : g a = 0) :
    Nonempty (LocalPowerCoordinate (reciprocalLogarithmicValue m g) a) := by
  apply exists_local_power_coordinate_with_inverse
    (analyticAt_reciprocalLogarithmicValue hg hg0 m hga)
  intro hconstant
  have hd : deriv (reciprocalLogarithmicValue m g) a = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hconstant]
    exact deriv_const a _
  exact deriv_reciprocalLogarithmicValue_ne_zero hg hg0 m hga hd

end MaxModulusPoints.FiberContinuation
