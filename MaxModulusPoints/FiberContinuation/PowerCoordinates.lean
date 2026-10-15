import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Polynomial.Basic
/-!
# Local analytic power coordinates

A nonconstant analytic germ is a positive integral power of a local conformal
coordinate after subtracting its central value.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Filter
open scoped Topology

/-- A nonvanishing analytic germ admits an analytic root of any positive order. -/
theorem exists_analytic_root {u : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hu : AnalyticAt ℂ u a) (hu0 : u a ≠ 0) (hn : 0 < n) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧ r a ≠ 0 ∧
      ∀ᶠ z in 𝓝 a, (r z) ^ n = u z := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (u a) hn
  have hb0 : b ≠ 0 := by
    intro hzero
    exact hu0 (hb.symm.trans (by simp [hzero, Nat.ne_of_gt hn]))
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ n) b := analyticAt_id.pow n
  have hderiv : deriv (fun z : ℂ => z ^ n) b ≠ 0 := by
    rw [(hasDerivAt_pow n b).deriv]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (pow_ne_zero _ hb0)
  let R : ℂ → ℂ := hpow.hasStrictDerivAt.localInverse _ _ _ hderiv
  have hR : AnalyticAt ℂ R (u a) := by
    simpa only [hb] using hpow.analyticAt_localInverse hderiv
  have hright : ∀ᶠ x in 𝓝 (u a), (R x) ^ n = x := by
    simpa only [hb] using hpow.hasStrictDerivAt.eventually_right_inverse hderiv
  have heq : ∀ᶠ z in 𝓝 a, (R (u z)) ^ n = u z :=
    hu.continuousAt.tendsto.eventually hright
  refine ⟨fun z => R (u z), hR.comp hu, ?_, heq⟩
  intro hzero
  exact hu0 ((Filter.EventuallyEq.eq_of_nhds heq).symm.trans
    (by simp [hzero, Nat.ne_of_gt hn]))

/-- The local power normal form at a nonconstant analytic germ. -/
theorem exists_local_power_coordinate {h : ℂ → ℂ} {a : ℂ}
    (hh : AnalyticAt ℂ h a)
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 a, h z = h a) :
    ∃ (n : ℕ) (e : ℂ → ℂ), 0 < n ∧ AnalyticAt ℂ e a ∧ e a = 0 ∧
      deriv e a ≠ 0 ∧ ∀ᶠ z in 𝓝 a, h z = h a + (e z) ^ n := by
  have hsub : AnalyticAt ℂ (fun z => h z - h a) a := hh.sub analyticAt_const
  have hnotzero : ¬ ∀ᶠ z in 𝓝 a, h z - h a = 0 := by
    simpa only [sub_eq_zero] using hnonconstant
  obtain ⟨n, u, hu, hu0, heq⟩ :=
    hsub.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotzero
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hcenter := Filter.EventuallyEq.eq_of_nhds heq
    have : u a = 0 := by simpa [hn0] using hcenter.symm
    exact hu0 this
  obtain ⟨r, hr, hr0, hroot⟩ := exists_analytic_root hu hu0 hn
  let e : ℂ → ℂ := fun z => (z - a) * r z
  have he : AnalyticAt ℂ e a := (analyticAt_id.sub analyticAt_const).mul hr
  have he0 : e a = 0 := by simp [e]
  have hederiv : deriv e a = r a := by
    have hd := ((hasDerivAt_id a).sub_const a).fun_mul hr.differentiableAt.hasDerivAt
    simpa [e] using hd.deriv
  refine ⟨n, e, hn, he, he0, hederiv ▸ hr0, ?_⟩
  filter_upwards [heq, hroot] with z hz hzr
  change h z - h a = (z - a) ^ n • u z at hz
  rw [smul_eq_mul] at hz
  calc
    h z = h a + (z - a) ^ n * u z := (sub_eq_iff_eq_add.mp hz).trans (add_comm _ _)
    _ = h a + (e z) ^ n := by
      change h a + (z - a) ^ n * u z = h a + ((z - a) * r z) ^ n
      rw [mul_pow, hzr]

end MaxModulusPoints.FiberContinuation
