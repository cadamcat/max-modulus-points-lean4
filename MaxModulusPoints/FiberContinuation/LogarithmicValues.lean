module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge

/-!
# Spherical logarithmic-derivative values

The logarithmic derivative of a nonzero entire function has a simple genuine
pole at each of its zeros away from the origin. Assigning infinity there gives
a continuous spherical-valued function.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter
open scoped Topology
open MaxModulusPoints.Blueprint

/-- The finite formula underlying the spherical logarithmic derivative. -/
def finiteLogarithmicValue (m : ℕ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (m : ℂ) + z * deriv g z / g z

theorem entire_reflected {g : ℂ → ℂ} (hg : Entire g) : Entire (reflected g) := by
  change Differentiable ℂ (fun z : ℂ => star (g (star z)))
  intro z
  simpa [reflected, Function.comp_def] using (hg (star z)).conj_conj

theorem reflected_zero_ne {g : ℂ → ℂ} (hg0 : g 0 ≠ 0) : reflected g 0 ≠ 0 := by
  simpa [reflected] using star_ne_zero.mpr hg0

/-- A function nonzero at zero cannot vanish as a germ anywhere in the plane. -/
theorem not_eventually_zero_of_entire {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (a : ℂ) : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
  intro heq
  have hglobal : g = fun _ => (0 : ℂ) :=
    (show AnalyticOnNhd ℂ g univ from fun z _ => hg.analyticAt z).eq_of_eventuallyEq
      analyticOnNhd_const heq
  exact hg0 (congrFun hglobal 0)

theorem analyticAt_finiteLogarithmicValue {g : ℂ → ℂ} (hg : Entire g)
    (m : ℕ) {a : ℂ} (hga : g a ≠ 0) :
    AnalyticAt ℂ (finiteLogarithmicValue m g) a := by
  exact analyticAt_const.add ((analyticAt_id.mul (hg.analyticAt a).deriv).div
    (hg.analyticAt a) hga)

theorem meromorphicAt_finiteLogarithmicValue {g : ℂ → ℂ} (hg : Entire g)
    (m : ℕ) (a : ℂ) : MeromorphicAt (finiteLogarithmicValue m g) a := by
  exact (MeromorphicAt.const (m : ℂ) a).fun_add
    (((MeromorphicAt.id a).fun_mul (hg.analyticAt a).deriv.meromorphicAt).fun_div
      (hg.analyticAt a).meromorphicAt)

/-- Every zero away from the origin gives a simple pole of the finite formula. -/
theorem meromorphicOrderAt_finiteLogarithmicValue {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) {a : ℂ} (hga : g a = 0) :
    meromorphicOrderAt (finiteLogarithmicValue m g) a = -1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hg0 hga
  have hmerom := (hg.analyticAt a).meromorphicAt
  have horderpos : 0 < meromorphicOrderAt g a :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hmerom).mp
      (by simpa only [hga] using (hg a).continuousAt.continuousWithinAt.tendsto)
  have hordernottop : meromorphicOrderAt g a ≠ ⊤ := by
    intro htop
    have hzero := (hg.analyticAt a).frequently_zero_iff_eventually_zero.mp
      (meromorphicOrderAt_eq_top_iff.mp htop).frequently
    exact not_eventually_zero_of_entire hg hg0 a hzero
  have hlog : meromorphicOrderAt (logDeriv g) a = -1 :=
    meromorphicOrderAt_logDeriv_eq_neg_one hmerom horderpos.ne' hordernottop
  have hmul : meromorphicOrderAt (id * logDeriv g) a = -1 := by
    rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_id ha0, hlog]
  have hformula : finiteLogarithmicValue m g =
      (fun _ : ℂ => (m : ℂ)) + id * logDeriv g := by
    funext z
    simp [finiteLogarithmicValue, logDeriv, mul_div_assoc]
  rw [hformula]
  apply (meromorphicOrderAt_add_eq_right_of_lt (MeromorphicAt.const (m : ℂ) a) ?_).trans hmul
  rw [hmul]
  exact lt_of_lt_of_le (show (-1 : WithTop ℤ) < 0 from by
    change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by norm_num))
    (show 0 ≤ meromorphicOrderAt (fun _ : ℂ => (m : ℂ)) a from
      analyticAt_const.meromorphicOrderAt_nonneg)

/-- The frozen spherical value is continuous, with genuine poles at zeros. -/
theorem continuous_logarithmicValue {g : ℂ → ℂ} (hg : Entire g)
    (hg0 : g 0 ≠ 0) (m : ℕ) : Continuous (logarithmicValue m g) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases hga : g a = 0
  · have hpole : meromorphicOrderAt (finiteLogarithmicValue m g) a < 0 := by
      rw [meromorphicOrderAt_finiteLogarithmicValue hg hg0 m hga]
      change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
      exact WithTop.coe_lt_coe.mpr (by norm_num)
    have hraw : Tendsto (finiteLogarithmicValue m g) (𝓝[≠] a)
        (coclosedCompact ℂ) := by
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_cobounded_of_meromorphicOrderAt_neg hpole
    have hne : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 :=
      (hg.analyticAt a).eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (not_eventually_zero_of_entire hg hg0 a)
    rw [continuousAt_iff_punctured_nhds]
    have hvalue : logarithmicValue m g a = OnePoint.infty := by
      simp [logarithmicValue, hga]
    rw [hvalue]
    apply (OnePoint.tendsto_coe_infty.comp hraw).congr'
    filter_upwards [hne] with z hz
    simp [logarithmicValue, finiteLogarithmicValue, hz]
  · have hne : ∀ᶠ z in 𝓝 a, g z ≠ 0 :=
      (hg a).continuousAt.eventually (isOpen_ne.mem_nhds hga)
    have hcont : ContinuousAt
        (fun z => (finiteLogarithmicValue m g z : OnePoint ℂ)) a :=
      OnePoint.continuous_coe.continuousAt.comp
        (analyticAt_finiteLogarithmicValue hg m hga).continuousAt
    apply hcont.congr
    filter_upwards [hne] with z hz
    simp [logarithmicValue, finiteLogarithmicValue, hz]

end MaxModulusPoints.FiberContinuation
