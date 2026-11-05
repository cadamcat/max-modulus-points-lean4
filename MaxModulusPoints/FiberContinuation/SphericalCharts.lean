module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.FiberContinuation.LogarithmicValues
public import MaxModulusPoints.FiberContinuation.PoleCoordinates

/-!
# A spherical chart at infinity

The map sending zero to infinity and a nonzero parameter to its reciprocal
is a continuous injective value chart. Near a pole it represents the actual
spherical logarithmic derivative through the analytic reciprocal coordinate.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

/-- The reciprocal chart, with its center assigned the spherical value infinity. -/
def infiniteValue (t : ℂ) : OnePoint ℂ :=
  if t = 0 then OnePoint.infty else (t⁻¹ : ℂ)

@[simp] theorem infiniteValue_zero : infiniteValue 0 = OnePoint.infty := by
  simp [infiniteValue]

theorem infiniteValue_injective : Function.Injective infiniteValue := by
  intro u v heq
  by_cases hu : u = 0
  · subst u
    by_cases hv : v = 0
    · exact hv.symm
    · simp [infiniteValue, hv] at heq
  · by_cases hv : v = 0
    · subst v
      simp [infiniteValue, hu] at heq
    · apply inv_injective
      exact OnePoint.coe_injective (by simpa only [infiniteValue, if_neg hu, if_neg hv] using heq)

theorem continuous_infiniteValue : Continuous infiniteValue := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    rw [continuousAt_iff_punctured_nhds, infiniteValue_zero]
    have hinv : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] 0) (coclosedCompact ℂ) := by
      simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
    apply (OnePoint.tendsto_coe_infty.comp hinv).congr'
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    change z ≠ 0 at hz
    simp [infiniteValue, hz]
  · have hcont : ContinuousAt (fun z : ℂ => (z⁻¹ : ℂ) : ℂ → OnePoint ℂ) t :=
      OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ ht)
    apply hcont.congr
    filter_upwards [eventually_ne_nhds ht] with z hz
    simp [infiniteValue, hz]

/-- The analytic reciprocal represents the actual spherical value near a pole. -/
theorem eventually_logarithmicValue_eq_infiniteValue {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (hga : g a = 0) :
    ∀ᶠ z in 𝓝 a, logarithmicValue m g z = infiniteValue (reciprocalLogarithmicValue m g z) := by
  have hrawne : ∀ᶠ z in 𝓝[≠] a, finiteLogarithmicValue m g z ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (meromorphicAt_finiteLogarithmicValue hg m a)).mp
    rw [meromorphicOrderAt_finiteLogarithmicValue hg hg0 m hga]
    exact WithTop.coe_ne_top
  filter_upwards [eventually_nhdsWithin_iff.mp hrawne] with z hz
  by_cases hgz : g z = 0
  · simp [logarithmicValue, reciprocalLogarithmicValue, infiniteValue, hgz]
  · have hza : z ≠ a := by
      intro heq
      exact hgz (heq ▸ hga)
    have hrawz : finiteLogarithmicValue m g z ≠ 0 := hz hza
    have hrawz' : (m : ℂ) + z * deriv g z / g z ≠ 0 := hrawz
    simp [logarithmicValue, reciprocalLogarithmicValue, infiniteValue, hgz,
      finiteLogarithmicValue, hrawz']

end MaxModulusPoints.FiberContinuation
