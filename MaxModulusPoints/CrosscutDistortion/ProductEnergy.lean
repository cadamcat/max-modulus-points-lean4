module

public import Mathlib.MeasureTheory.Integral.Prod
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.AlmostEverywhereEnergy
public import MaxModulusPoints.CrosscutDistortion.ConformalDensity
public import MaxModulusPoints.CrosscutDistortion.SquareIntegrability

/-!
# Product energy of a rectangular family of curves

Fubini supplies almost-everywhere slice integrability and integrability of
the outer energy. Square-integrable nonnegative densities then satisfy
the rectangular energy bound whenever their integrable slices have unit
length. This applies to the conformal density in a narrow tunnel.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set MeasureTheory Blueprint

/-- Product square integrability supplies all integrability conditions in
the rectangular energy bound for nonnegative densities. -/
theorem rectangle_product_energy_lower_bound {a b h : ℝ}
    (hab : a ≤ b) (hh : 0 < h) (g : ℝ → ℝ → ℝ)
    (hnonneg : ∀ x y, 0 ≤ g x y)
    (hsquare : Integrable (fun q : ℝ × ℝ => (g q.1 q.2) ^ 2)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo (-h / 2) (h / 2)))))
    (hlength : ∀ x ∈ Ioo a b,
      IntervalIntegrable (g x) volume (-h / 2) (h / 2) →
        1 ≤ ∫ y in (-h / 2)..(h / 2), g x y) :
    (b - a) / h ≤ ∫ q : ℝ × ℝ, (g q.1 q.2) ^ 2
      ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo (-h / 2) (h / 2)))) := by
  have hy : -h / 2 ≤ h / 2 := by linarith
  have hinner (x : ℝ) : (∫ y in (-h / 2)..(h / 2), (g x y) ^ 2) =
      ∫ y in Ioo (-h / 2) (h / 2), (g x y) ^ 2 := by
    rw [intervalIntegral.integral_of_le hy, integral_Ioc_eq_integral_Ioo]
  have henergySet : IntegrableOn
      (fun x => ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2) (Ioo a b) := by
    simpa only [IntegrableOn, hinner] using hsquare.integral_prod_left
  have henergy : IntervalIntegrable
      (fun x => ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr henergySet
  have hslice : ∀ᵐ x ∂volume.restrict (Ioo a b),
      IntervalIntegrable (g x) volume (-h / 2) (h / 2) ∧
        IntervalIntegrable (fun y => (g x y) ^ 2) volume (-h / 2) (h / 2) ∧
        1 ≤ ∫ y in (-h / 2)..(h / 2), g x y := by
    filter_upwards [hsquare.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with x hx hxab
    have hxsquare : IntervalIntegrable (fun y => (g x y) ^ 2) volume (-h / 2) (h / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hy).mpr hx
    have hxlinear := intervalIntegrable_nonneg_of_square (g x) (-h / 2) (h / 2)
      (Filter.Eventually.of_forall fun y => hnonneg x y) hxsquare
    exact ⟨hxlinear, hxsquare, hlength x hxab hxlinear⟩
  have hbound := rectangle_energy_lower_bound_ae hab hh g hslice henergy
  have heq : (∫ q : ℝ × ℝ, (g q.1 q.2) ^ 2
        ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo (-h / 2) (h / 2))))) =
      ∫ x in a..b, ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2 := by
    rw [integral_prod _ hsquare, intervalIntegral.integral_of_le hab,
      integral_Ioc_eq_integral_Ioo]
    simp only [hinner]
  rw [heq]
  exact hbound

/-- The squared conformal density has energy at least the reciprocal tunnel
aspect ratio, assuming its square is integrable on the product rectangle. -/
theorem tunnel_product_energy_lower_bound (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0) (n : ℕ)
    (w z : ℂ) (hw : w ∈ passageSlice p n) (hz : z ∈ cleanSlice p n)
    (hwV : w ∈ tract p δ) (hzV : z ∈ tract p δ)
    (hsquare : Integrable
      (fun q : ℝ × ℝ => (slabPullbackDensity (φ.toFun w).re
        (max (φ.toFun w).re (φ.toFun z).re) φ.toFun ((q.1 : ℂ) + q.2 * Complex.I)) ^ 2)
      ((volume.restrict (Ioo (blockPosition p n + 1 / 2) (blockPosition p n + 1))).prod
        (volume.restrict (Ioo (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2))))) :
    1 / (2 * p.tunnelHeight n) ≤ ∫ q : ℝ × ℝ,
      (slabPullbackDensity (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        φ.toFun ((q.1 : ℂ) + q.2 * Complex.I)) ^ 2
      ∂((volume.restrict (Ioo (blockPosition p n + 1 / 2) (blockPosition p n + 1))).prod
        (volume.restrict (Ioo (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2)))) := by
  have hbound := rectangle_product_energy_lower_bound
    (a := blockPosition p n + 1 / 2) (b := blockPosition p n + 1)
    (by linarith) (p.tunnel_pos n)
    (fun x y => slabPullbackDensity (φ.toFun w).re
      (max (φ.toFun w).re (φ.toFun z).re) φ.toFun ((x : ℂ) + y * Complex.I))
    (fun x y => by unfold slabPullbackDensity; split_ifs <;> positivity) hsquare
    (fun x hx hint => tunnel_density_length p δ φ hφ0 hφre hφim n x hx w z hw hz
      hwV hzV hint)
  have hwidth : (blockPosition p n + 1 - (blockPosition p n + 1 / 2)) /
      p.tunnelHeight n = 1 / (2 * p.tunnelHeight n) := by
    field_simp [ne_of_gt (p.tunnel_pos n)]
    <;> ring
  rw [hwidth] at hbound
  exact hbound

end MaxModulusPoints.CrosscutDistortion
