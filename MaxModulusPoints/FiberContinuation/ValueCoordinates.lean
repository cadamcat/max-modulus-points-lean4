module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.FiberContinuation.FiniteCoordinates
public import MaxModulusPoints.FiberContinuation.InverseCoordinates
public import MaxModulusPoints.FiberContinuation.LogarithmicValues
public import MaxModulusPoints.FiberContinuation.PoleCoordinates
public import MaxModulusPoints.FiberContinuation.SphericalCharts

/-!
# Uniform local value coordinates

Finite centers use translation; infinity uses reciprocation. In either case,
the actual logarithmic derivative is represented by an injective spherical
value chart applied to a nonconstant analytic germ vanishing at the root.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter
open scoped Topology
open MaxModulusPoints.Blueprint

/-- A value chart centered at a finite or infinite spherical value. -/
def centeredValue (p : OnePoint ℂ) (t : ℂ) : OnePoint ℂ :=
  p.elim (infiniteValue t) (fun q => ((q + t : ℂ) : OnePoint ℂ))

@[simp] theorem centeredValue_zero (p : OnePoint ℂ) : centeredValue p 0 = p := by
  cases p using OnePoint.rec <;> simp [centeredValue]

theorem continuous_centeredValue (p : OnePoint ℂ) : Continuous (centeredValue p) := by
  cases p using OnePoint.rec with
  | infty => exact continuous_infiniteValue
  | coe q => exact OnePoint.continuous_coe.comp (continuous_const.add continuous_id)

theorem centeredValue_injective (p : OnePoint ℂ) : Function.Injective (centeredValue p) := by
  cases p using OnePoint.rec with
  | infty => exact infiniteValue_injective
  | coe q =>
    intro u v heq
    exact add_left_cancel (OnePoint.coe_injective heq)

/-- The finite analytic coordinate of the logarithmic derivative in a value chart. -/
def localValueFunction (m : ℕ) (g : ℂ → ℂ) (p : OnePoint ℂ) (z : ℂ) : ℂ :=
  p.elim (reciprocalLogarithmicValue m g z) (fun q => finiteLogarithmicValue m g z - q)

theorem nonconstant_reflected {g : ℂ → ℂ} (hnc : ¬ ∃ c : ℂ, ∀ z, g z = c) :
    ¬ ∃ c : ℂ, ∀ z, reflected g z = c := by
  rintro ⟨c, hc⟩
  apply hnc
  refine ⟨star c, fun z => ?_⟩
  simpa [reflected] using congrArg star (hc (star z))

/-- Every physical root has a power coordinate representing its actual spherical
value, including roots over the omitted value and poles over infinity. -/
theorem exists_logarithmic_power_coordinate {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (hnc : ¬ ∃ c : ℂ, ∀ z, g z = c)
    (m : ℕ) {a : ℂ} {p : OnePoint ℂ} (hvalue : logarithmicValue m g a = p) :
    ∃ c : LocalPowerCoordinate (localValueFunction m g p) a,
      localValueFunction m g p a = 0 ∧
      ∀ᶠ z in 𝓝 a, logarithmicValue m g z = centeredValue p (localValueFunction m g p z) := by
  cases p using OnePoint.rec with
  | infty =>
    have hga : g a = 0 := by
      by_contra hga
      simp [logarithmicValue, hga] at hvalue
    obtain ⟨c⟩ := exists_pole_power_coordinate hg hg0 m hga
    exact ⟨c, by simp [localValueFunction, reciprocalLogarithmicValue, hga],
      eventually_logarithmicValue_eq_infiniteValue hg hg0 m hga⟩
  | coe p =>
    have hga : g a ≠ 0 := by
      intro hga
      simp [logarithmicValue, hga] at hvalue
    have hfinite : finiteLogarithmicValue m g a = p :=
      OnePoint.coe_injective (by simpa [logarithmicValue, hga, finiteLogarithmicValue] using hvalue)
    have han : AnalyticAt ℂ (fun z => finiteLogarithmicValue m g z - p) a :=
      (analyticAt_finiteLogarithmicValue hg m hga).sub analyticAt_const
    have hnonconstant : ¬ ∀ᶠ z in 𝓝 a,
        finiteLogarithmicValue m g z - p = finiteLogarithmicValue m g a - p := by
      intro hconstant
      apply not_eventually_constant_finiteLogarithmicValue hg hg0 hnc m hga
      exact hconstant.mono (fun _ hz => by
        simpa only [sub_add_cancel] using congrArg (fun w : ℂ => w + p) hz)
    obtain ⟨c⟩ := exists_local_power_coordinate_with_inverse han hnonconstant
    refine ⟨c, sub_eq_zero.mpr hfinite, ?_⟩
    filter_upwards [(hg a).continuousAt.eventually (isOpen_ne.mem_nhds hga)] with z hgz
    change logarithmicValue m g z = ((p + (finiteLogarithmicValue m g z - p) : ℂ) : OnePoint ℂ)
    rw [logarithmicValue, if_neg hgz]
    congr 1
    change (m : ℂ) + z * deriv g z / g z = p + ((m : ℂ) + z * deriv g z / g z - p)
    ring

end MaxModulusPoints.FiberContinuation
