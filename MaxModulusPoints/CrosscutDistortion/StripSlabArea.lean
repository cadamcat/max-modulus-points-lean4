module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import MaxModulusPoints.Blueprint.Data

/-!
# Area of a vertical slab in the unit-height strip

Complex Lebesgue measure agrees with product Lebesgue measure in real and
imaginary coordinates. The target support slab therefore has area equal
to its horizontal width, with zero area when that width is nonpositive.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set MeasureTheory Blueprint

/-- The unit-height strip between the enlarged sides of a real-coordinate core. -/
def stripSlab (a b : ℝ) : Set ℂ :=
  {ξ : ℂ | ξ.re ∈ Ioo (a - 1 / 2) (b + 1 / 2) ∧ |ξ.im| < 1 / 2}

/-- The strip slab has its horizontal width as area, with no ordering assumption. -/
theorem volume_stripSlab (a b : ℝ) :
    volume (stripSlab a b) = ENNReal.ofReal (b - a + 1) := by
  have hpreimage : stripSlab a b = Complex.measurableEquivRealProd ⁻¹'
      (Ioo (a - 1 / 2) (b + 1 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext ξ
    simp [stripSlab, abs_lt]
  rw [hpreimage, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  have hwidth : b + 1 / 2 - (a - 1 / 2) = b - a + 1 := by ring
  rw [hwidth]
  norm_num

/-- A supported image in the strip has area bounded by the area of the slab. -/
theorem strip_supported_image_volume_le {U : Set ℂ}
    (φ : ConformalEquivalence U strip) (E : Set ℂ) (hEU : E ⊆ U)
    (a b : ℝ)
    (hsupport : ∀ q ∈ E, (φ.toFun q).re ∈ Ioo (a - 1 / 2) (b + 1 / 2)) :
    volume (φ.toFun '' E) ≤ ENNReal.ofReal (b - a + 1) := by
  rw [← volume_stripSlab a b]
  apply measure_mono
  rintro ξ ⟨q, hq, rfl⟩
  exact ⟨hsupport q hq, φ.mapsTo (hEU hq)⟩

end MaxModulusPoints.CrosscutDistortion
