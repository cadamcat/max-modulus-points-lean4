import MaxModulusPoints.CrosscutDistortion.RectangleEnergy
/-!
# Rectangular energy from almost-everywhere slice bounds

The squared-density energy is at least width divided by height when the
vertical length bound and slice integrability hold almost everywhere.
Exceptional horizontal coordinates do not affect the total integral.
-/

namespace MaxModulusPoints.CrosscutDistortion

open MeasureTheory Set

/-- The rectangular energy lower bound with a.e. slice hypotheses, suitable
for slice integrability obtained from Fubini's theorem. -/
theorem rectangle_energy_lower_bound_ae
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 < h) (g : ℝ → ℝ → ℝ)
    (hslice : ∀ᵐ x ∂volume.restrict (Ioo a b),
      IntervalIntegrable (g x) volume (-h / 2) (h / 2) ∧
        IntervalIntegrable (fun y => (g x y) ^ 2) volume (-h / 2) (h / 2) ∧
        1 ≤ ∫ y in (-h / 2)..(h / 2), g x y)
    (henergy : IntervalIntegrable
      (fun x => ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2) volume a b) :
    (b - a) / h ≤ ∫ x in a..b, ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2 := by
  have hslicebound : ∀ᵐ x ∂volume.restrict (Ioo a b),
      1 / h ≤ ∫ y in (-h / 2)..(h / 2), (g x y) ^ 2 := by
    filter_upwards [hslice] with x hx
    have hsingle := rectangle_energy_lower_bound (a := 0) (b := 1) (by norm_num) hh
      (fun _ y => g x y) (fun _ _ => hx.1) (fun _ _ => hx.2.1)
      (fun _ _ => hx.2.2) intervalIntegrable_const
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hsingle
  have hbound := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / h) volume a b)
    henergy (by rwa [← restrict_Ioo_eq_restrict_Icc])
  simpa [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using hbound

end MaxModulusPoints.CrosscutDistortion
