module

public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Calculus.MeanValue
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.CompleteBranches
public import MaxModulusPoints.FiberContinuation.LogarithmicValues
public import MaxModulusPoints.FiberContinuation.OmittedContinuation
public import MaxModulusPoints.FiberContinuation.ValueCoordinates

/-!
# Nonconstant product coordinates of physical branches

Clearing both logarithmic denominators preserves their equality even at poles.
If a physical branch had constant nonzero product, the open mapping theorem
for its first coordinate would make the cleared product equation vanish on
an open set. Analytic continuation and derivative constancy would then make
the reflected product constant on the punctured plane.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

/-- Equality of actual spherical logarithmic values implies the cleared
equation, including when both values are poles. -/
theorem cleared_logarithmic_equality (m : ℕ) (g h : ℂ → ℂ) (z w : ℂ)
    (heq : logarithmicValue m g z = logarithmicValue m h w) :
    z * deriv g z * h w - w * deriv h w * g z = 0 := by
  by_cases hgz : g z = 0
  · have hhw : h w = 0 := by
      by_contra hhw
      simp [logarithmicValue, hgz, hhw] at heq
    simp [hgz, hhw]
  · have hhw : h w ≠ 0 := by
      intro hzero
      simp [logarithmicValue, hgz, hzero] at heq
    have hfinite : (m : ℂ) + z * deriv g z / g z = (m : ℂ) + w * deriv h w / h w :=
      OnePoint.coe_injective (by simpa [logarithmicValue, hgz, hhw] using heq)
    exact sub_eq_zero.mpr ((div_eq_div_iff hgz hhw).mp (add_left_cancel hfinite))

def reflectedProduct {f : ℂ → ℂ} (d : NormalizedFunction f) (s z : ℂ) : ℂ :=
  d.g z * reflected d.g (s / z)

def productEquation {f : ℂ → ℂ} (d : NormalizedFunction f) (s z : ℂ) : ℂ :=
  z * deriv d.g z * reflected d.g (s / z) -
    (s / z) * deriv (reflected d.g) (s / z) * d.g z

theorem analyticAt_reflectedProduct {f : ℂ → ℂ} (d : NormalizedFunction f)
    (s : ℂ) {z : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (reflectedProduct d s) z := by
  have hdiv : AnalyticAt ℂ (fun u : ℂ => s / u) z := analyticAt_const.div analyticAt_id hz
  exact (d.entire.analyticAt z).mul
    (((entire_reflected d.entire).analyticAt (s / z)).comp hdiv)

theorem analyticAt_productEquation {f : ℂ → ℂ} (d : NormalizedFunction f)
    (s : ℂ) {z : ℂ} (hz : z ≠ 0) : AnalyticAt ℂ (productEquation d s) z := by
  have hdiv : AnalyticAt ℂ (fun u : ℂ => s / u) z := analyticAt_const.div analyticAt_id hz
  have hh := ((entire_reflected d.entire).analyticAt (s / z)).comp hdiv
  have hhd := ((entire_reflected d.entire).deriv.analyticAt (s / z)).comp hdiv
  exact ((analyticAt_id.mul (d.entire.deriv.analyticAt z)).mul hh).sub
    ((hdiv.mul hhd).mul (d.entire.analyticAt z))

/-- The cleared equation is the reflected product derivative multiplied by z. -/
theorem mul_deriv_reflectedProduct {f : ℂ → ℂ} (d : NormalizedFunction f)
    (s : ℂ) {z : ℂ} (hz : z ≠ 0) :
    z * deriv (reflectedProduct d s) z = productEquation d s z := by
  have hdiv : DifferentiableAt ℂ (fun u : ℂ => s / u) z :=
    (analyticAt_const.div analyticAt_id hz).differentiableAt
  have hh : DifferentiableAt ℂ (fun u : ℂ => reflected d.g (s / u)) z :=
    ((entire_reflected d.entire) (s / z)).comp z hdiv
  have hcomp : deriv (fun u : ℂ => reflected d.g (s / u)) z =
      deriv (reflected d.g) (s / z) * (-s / z ^ 2) := by
    simpa only [Function.comp_def, deriv_const_div_id] using
      deriv_comp z ((entire_reflected d.entire) (s / z)) hdiv
  change z * deriv (fun u => d.g u * reflected d.g (s / u)) z = productEquation d s z
  rw [deriv_fun_mul (d.entire z) hh, hcomp]
  dsimp [productEquation]
  field_simp [hz]
  <;> ring

namespace CompleteHighBranch

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {L : ℕ} {s : ℂ} {p : OnePoint ℂ}
    (B : CompleteHighBranch d L s p)

def productFunction (t : ℂ) : ℂ := (B.pair t).1 * (B.pair t).2

@[simp] theorem productFunction_zero : B.productFunction 0 = s := B.central_pair.1

theorem analyticAt_productFunction : AnalyticAt ℂ B.productFunction 0 := by
  have hpair := B.analytic_pair 0 (mem_ball_self B.radius_pos)
  exact (analyticAt_fst.comp hpair).mul (analyticAt_snd.comp hpair)

/-- A constant first physical germ would make the positive-power common value
constant, which is impossible on a punctured neighborhood. -/
theorem not_eventually_constant_fst :
    ¬ ∀ᶠ t in 𝓝 (0 : ℂ), (B.pair t).1 = (B.pair 0).1 := by
  intro hconstant
  have hvalue : ∀ᶠ t in 𝓝 (0 : ℂ), centeredValue p (t ^ B.exponent) = p := by
    filter_upwards [hconstant, ball_mem_nhds 0 B.radius_pos] with t ht htball
    calc
      centeredValue p (t ^ B.exponent) = logarithmicValue d.multiplicity d.g (B.pair t).1 :=
        (B.forward t htball).2.1.symm
      _ = logarithmicValue d.multiplicity d.g (B.pair 0).1 := by rw [ht]
      _ = p := B.central_pair.2.1
  have hzero : ∀ᶠ t in 𝓝 (0 : ℂ), t = 0 := hvalue.mono (by
    intro t ht
    have hpow : t ^ B.exponent = 0 :=
      centeredValue_injective p (ht.trans (centeredValue_zero p).symm)
    by_contra ht0
    exact pow_ne_zero _ ht0 hpow)
  obtain ⟨t, htzero, htne⟩ := ((hzero.filter_mono nhdsWithin_le_nhds).and
    (show ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 from self_mem_nhdsWithin)).exists
  exact htne htzero

/-- A constant nonzero product germ would force the reflected product on the
punctured plane to be constant. -/
theorem not_eventually_constant_product (hs : s ≠ 0) (hnonconstant : NonconstantProducts d) :
    ¬ ∀ᶠ t in 𝓝 (0 : ℂ), B.productFunction t = s := by
  intro hconstant
  let Z : ℂ → ℂ := fun t => (B.pair t).1
  have hZ : AnalyticAt ℂ Z 0 :=
    analyticAt_fst.comp (B.analytic_pair 0 (mem_ball_self B.radius_pos))
  have hopen : 𝓝 (Z 0) ≤ map Z (𝓝 0) :=
    hZ.eventually_constant_or_nhds_le_map_nhds.resolve_left B.not_eventually_constant_fst
  have hz0 : Z 0 ≠ 0 := by
    intro hzero
    change (B.pair 0).1 = 0 at hzero
    apply hs
    rw [← B.productFunction_zero]
    change (B.pair 0).1 * (B.pair 0).2 = 0
    rw [hzero, zero_mul]
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℂ), productEquation d s (Z t) = 0 := by
    filter_upwards [hconstant, ball_mem_nhds 0 B.radius_pos] with t ht htball
    change (B.pair t).1 * (B.pair t).2 = s at ht
    have hz : (B.pair t).1 ≠ 0 := by
      intro hzero
      apply hs
      rw [← ht, hzero, zero_mul]
    have hw : s / (B.pair t).1 = (B.pair t).2 :=
      (div_eq_iff hz).mpr (ht.symm.trans (mul_comm _ _))
    have hforward := B.forward t htball
    have hcleared := cleared_logarithmic_equality d.multiplicity d.g (reflected d.g)
      (B.pair t).1 (B.pair t).2 (hforward.2.1.trans hforward.2.2.symm)
    dsimp [productEquation, Z]
    rw [hw]
    exact hcleared
  have hmapzero : ∀ᶠ z in map Z (𝓝 0), productEquation d s z = 0 := by
    simpa only [Filter.eventually_map] using hlocal
  have hzero : ∀ᶠ z in 𝓝 (Z 0), productEquation d s z = 0 := hmapzero.filter_mono hopen
  let U : Set ℂ := {0}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hconnected : IsPreconnected U := by
    rw [show U = Set.range Complex.exp from Complex.range_exp.symm]
    exact isPreconnected_range Complex.continuous_exp
  have hE : AnalyticOnNhd ℂ (productEquation d s) U :=
    fun z hz => analyticAt_productEquation d s hz
  have hglobal : EqOn (productEquation d s) 0 U :=
    hE.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconnected hz0 hzero
  have hP : DifferentiableOn ℂ (reflectedProduct d s) U :=
    fun z hz => (analyticAt_reflectedProduct d s hz).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv (reflectedProduct d s)) 0 U := by
    intro z hz
    have heq : z * deriv (reflectedProduct d s) z = 0 :=
      (mul_deriv_reflectedProduct d s hz).trans (hglobal hz)
    exact (mul_eq_zero.mp heq).resolve_left hz
  obtain ⟨c, hc⟩ := hU.exists_is_const_of_deriv_eq_zero hconnected hP hderiv
  exact hnonconstant s hs ⟨c, fun z hz => hc z hz⟩

end CompleteHighBranch

end MaxModulusPoints.FiberContinuation
