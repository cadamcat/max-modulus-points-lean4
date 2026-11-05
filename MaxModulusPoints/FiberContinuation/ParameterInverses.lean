module

public import MaxModulusPoints.FiberContinuation.SphericalCharts
public import MaxModulusPoints.FiberContinuation.ValueCoordinates

/-!
# Inverse value parameters away from the center

At a nonzero parameter, a positive power has nonzero derivative. The finite
common value, also in a pole chart, therefore has an analytic local inverse.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Filter
open scoped Topology

/-- The finite common value of a nonzero common-power parameter. -/
def finiteParameterValue (p : OnePoint ℂ) (N : ℕ) (t : ℂ) : ℂ :=
  p.elim ((t ^ N)⁻¹) (fun q => q + t ^ N)

theorem centeredValue_pow_eq_coe (p : OnePoint ℂ) (N : ℕ) {t : ℂ} (ht : t ≠ 0) :
    centeredValue p (t ^ N) = (finiteParameterValue p N t : OnePoint ℂ) := by
  cases p using OnePoint.rec <;> simp [centeredValue, finiteParameterValue, infiniteValue, pow_ne_zero N ht]

theorem analyticAt_finiteParameterValue (p : OnePoint ℂ) (N : ℕ) {t : ℂ} (ht : t ≠ 0) :
    AnalyticAt ℂ (finiteParameterValue p N) t := by
  cases p using OnePoint.rec with
  | infty => exact (analyticAt_id.pow N).inv (pow_ne_zero N ht)
  | coe q => exact analyticAt_const.add (analyticAt_id.pow N)

theorem deriv_finiteParameterValue_ne_zero (p : OnePoint ℂ) {N : ℕ} (hN : 0 < N)
    {t : ℂ} (ht : t ≠ 0) : deriv (finiteParameterValue p N) t ≠ 0 := by
  have hderiv : (N : ℂ) * t ^ (N - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hN.ne') (pow_ne_zero _ ht)
  cases p using OnePoint.rec with
  | infty =>
    change deriv ((fun z : ℂ => z ^ N)⁻¹) t ≠ 0
    rw [((hasDerivAt_pow N t).inv (pow_ne_zero N ht)).deriv]
    exact div_ne_zero (neg_ne_zero.mpr hderiv) (pow_ne_zero _ (pow_ne_zero N ht))
  | coe q =>
    change deriv ((fun _ : ℂ => q) + (fun z : ℂ => z ^ N)) t ≠ 0
    rw [((hasDerivAt_const t q).add (hasDerivAt_pow N t)).deriv, zero_add]
    exact hderiv

/-- A noncentral finite common value has an analytic local parameter inverse. -/
theorem exists_inverse_value_parameter (p : OnePoint ℂ) {N : ℕ} (hN : 0 < N)
    {t : ℂ} (ht : t ≠ 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R (finiteParameterValue p N t) ∧
      R (finiteParameterValue p N t) = t ∧
      ∀ᶠ q in 𝓝 (finiteParameterValue p N t), R q ≠ 0 ∧
        centeredValue p ((R q) ^ N) = (q : OnePoint ℂ) := by
  have han := analyticAt_finiteParameterValue p N ht
  have hderiv := deriv_finiteParameterValue_ne_zero p hN ht
  let R : ℂ → ℂ := han.hasStrictDerivAt.localInverse _ _ _ hderiv
  have hR : AnalyticAt ℂ R (finiteParameterValue p N t) := han.analyticAt_localInverse hderiv
  have hleft : ∀ᶠ u in 𝓝 t, R (finiteParameterValue p N u) = u :=
    han.hasStrictDerivAt.eventually_left_inverse hderiv
  have hRcenter : R (finiteParameterValue p N t) = t := Filter.EventuallyEq.eq_of_nhds hleft
  have hright : ∀ᶠ q in 𝓝 (finiteParameterValue p N t), finiteParameterValue p N (R q) = q :=
    han.hasStrictDerivAt.eventually_right_inverse hderiv
  have hnonzero : ∀ᶠ q in 𝓝 (finiteParameterValue p N t), R q ≠ 0 := by
    have hcenter_ne : R (finiteParameterValue p N t) ≠ 0 := by rw [hRcenter]; exact ht
    exact hR.continuousAt.eventually (isOpen_ne.mem_nhds hcenter_ne)
  refine ⟨R, hR, hRcenter, ?_⟩
  filter_upwards [hnonzero, hright] with q hq0 hq
  exact ⟨hq0, (centeredValue_pow_eq_coe p N hq0).trans (congrArg (fun z : ℂ => (z : OnePoint ℂ)) hq)⟩

end MaxModulusPoints.FiberContinuation
