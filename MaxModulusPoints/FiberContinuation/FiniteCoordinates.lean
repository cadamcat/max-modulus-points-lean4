module

public import Mathlib.Analysis.Calculus.MeanValue
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.FiberContinuation.InverseCoordinates
public import MaxModulusPoints.FiberContinuation.LogarithmicValues

/-!
# Finite logarithmic-value coordinates

Clearing the denominator gives an entire equation. A constant germ of the
logarithmic derivative would make the normalized entire factor constant.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter
open scoped Topology
open MaxModulusPoints.Blueprint

/-- The entire numerator for a prescribed finite logarithmic value. -/
def logarithmicEquation (m : ℕ) (g : ℂ → ℂ) (q : ℂ) (z : ℂ) : ℂ :=
  z * deriv g z - (q - (m : ℂ)) * g z

theorem entire_logarithmicEquation {g : ℂ → ℂ} (hg : Entire g) (m : ℕ) (q : ℂ) :
    Entire (logarithmicEquation m g q) := by
  change Differentiable ℂ (logarithmicEquation m g q)
  exact (differentiable_id.mul hg.deriv).sub
    ((differentiable_const (q - (m : ℂ))).mul hg)

theorem logarithmicEquation_eq_zero_iff {g : ℂ → ℂ} (m : ℕ) (q : ℂ) {z : ℂ}
    (hgz : g z ≠ 0) :
    logarithmicEquation m g q z = 0 ↔ finiteLogarithmicValue m g z = q := by
  change z * deriv g z - (q - (m : ℂ)) * g z = 0 ↔
    (m : ℂ) + z * deriv g z / g z = q
  rw [sub_eq_zero, ← div_eq_iff hgz, eq_sub_iff_add_eq']

/-- The cleared logarithmic equation is not a zero germ at any point. -/
theorem not_eventually_zero_logarithmicEquation {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, g z = c)
    (m : ℕ) (q a : ℂ) : ¬ ∀ᶠ z in 𝓝 a, logarithmicEquation m g q z = 0 := by
  intro hzero
  have hglobal : logarithmicEquation m g q = fun _ => (0 : ℂ) :=
    (show AnalyticOnNhd ℂ (logarithmicEquation m g q) univ from
      fun z _ => (entire_logarithmicEquation hg m q).analyticAt z).eq_of_eventuallyEq
        analyticOnNhd_const hzero
  have hprod : (q - (m : ℂ)) * g 0 = 0 := by
    simpa only [logarithmicEquation, zero_mul, zero_sub, neg_eq_zero] using congrFun hglobal 0
  have hqm : q = (m : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hg0)
  have hDlocal : ∀ᶠ z in 𝓝 (1 : ℂ), deriv g z = 0 := by
    filter_upwards [eventually_ne_nhds (show (1 : ℂ) ≠ 0 from one_ne_zero)] with z hz
    have hzg : z * deriv g z = 0 := by
      simpa [logarithmicEquation, hqm] using congrFun hglobal z
    exact (mul_eq_zero.mp hzg).resolve_left hz
  have hDglobal : deriv g = fun _ => (0 : ℂ) :=
    (show AnalyticOnNhd ℂ (deriv g) univ from
      fun z _ => hg.deriv.analyticAt z).eq_of_eventuallyEq analyticOnNhd_const hDlocal
  exact hnc ⟨g 0, fun z => is_const_of_deriv_eq_zero hg (fun u => congrFun hDglobal u) z 0⟩

/-- At a finite-valued point, the logarithmic formula is not a constant germ. -/
theorem not_eventually_constant_finiteLogarithmicValue {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, g z = c)
    (m : ℕ) {a : ℂ} (hga : g a ≠ 0) :
    ¬ ∀ᶠ z in 𝓝 a, finiteLogarithmicValue m g z = finiteLogarithmicValue m g a := by
  intro hconstant
  apply not_eventually_zero_logarithmicEquation hg hg0 hnc m (finiteLogarithmicValue m g a) a
  filter_upwards [hconstant, (hg a).continuousAt.eventually (isOpen_ne.mem_nhds hga)] with z hz hgz
  exact (logarithmicEquation_eq_zero_iff m _ hgz).mpr hz

/-- Every finite actual value has an analytic power coordinate with inverse. -/
theorem exists_finite_power_coordinate {f : ℂ → ℂ} (d : NormalizedFunction f)
    {a : ℂ} (hga : d.g a ≠ 0) :
    Nonempty (LocalPowerCoordinate (finiteLogarithmicValue d.multiplicity d.g) a) := by
  exact exists_local_power_coordinate_with_inverse
    (analyticAt_finiteLogarithmicValue d.entire d.multiplicity hga)
    (not_eventually_constant_finiteLogarithmicValue d.entire d.at_zero d.nonconstant
      d.multiplicity hga)

end MaxModulusPoints.FiberContinuation
