import MaxModulusPoints.FiberContinuation.PowerCoordinates
/-!
# Analytic inverse coordinates for local powers

The inverse coordinate supplies analytic representatives of the local inverse
roots. Both inverse identities hold on neighborhoods of their respective centers.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Filter
open scoped Topology

/-- A local power normal form with its analytic inverse coordinate. -/
structure LocalPowerCoordinate (h : ℂ → ℂ) (a : ℂ) where
  order : ℕ
  order_pos : 0 < order
  coordinate : ℂ → ℂ
  inverse : ℂ → ℂ
  analytic_coordinate : AnalyticAt ℂ coordinate a
  analytic_inverse : AnalyticAt ℂ inverse 0
  coordinate_center : coordinate a = 0
  inverse_center : inverse 0 = a
  derivative_ne_zero : deriv coordinate a ≠ 0
  left_inverse : ∀ᶠ z in 𝓝 a, inverse (coordinate z) = z
  right_inverse : ∀ᶠ t in 𝓝 (0 : ℂ), coordinate (inverse t) = t
  normal_form : ∀ᶠ z in 𝓝 a, h z = h a + (coordinate z) ^ order
  inverse_normal_form : ∀ᶠ t in 𝓝 (0 : ℂ), h (inverse t) = h a + t ^ order

/-- Every nonconstant analytic germ has an analytic inverse power coordinate. -/
theorem exists_local_power_coordinate_with_inverse {h : ℂ → ℂ} {a : ℂ}
    (hh : AnalyticAt ℂ h a)
    (hnonconstant : ¬ ∀ᶠ z in 𝓝 a, h z = h a) :
    Nonempty (LocalPowerCoordinate h a) := by
  obtain ⟨n, e, hn, he, he0, he', hform⟩ :=
    exists_local_power_coordinate hh hnonconstant
  let R : ℂ → ℂ := he.hasStrictDerivAt.localInverse _ _ _ he'
  have hleft : ∀ᶠ z in 𝓝 a, R (e z) = z :=
    he.hasStrictDerivAt.eventually_left_inverse he'
  have hR0 : R 0 = a := by
    simpa only [he0] using Filter.EventuallyEq.eq_of_nhds hleft
  have hR : AnalyticAt ℂ R 0 := by
    simpa only [he0] using he.analyticAt_localInverse he'
  have hright : ∀ᶠ t in 𝓝 (0 : ℂ), e (R t) = t := by
    simpa only [he0] using he.hasStrictDerivAt.eventually_right_inverse he'
  have hRtendsto : Tendsto R (𝓝 0) (𝓝 a) := by
    simpa only [hR0] using hR.continuousAt.tendsto
  have hinvform : ∀ᶠ t in 𝓝 (0 : ℂ), h (R t) = h a + t ^ n := by
    filter_upwards [hRtendsto.eventually hform, hright] with t ht htr
    simpa only [htr] using ht
  exact ⟨⟨n, hn, e, R, he, hR, he0, hR0, he', hleft, hright, hform, hinvform⟩⟩

end MaxModulusPoints.FiberContinuation
