module

public import MaxModulusPoints.Blueprint.Data

/-!
# `StripMapData`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- The normalized strip-to-target map and the estimates used in the open-gate
comparison, including the rescaled kernel limit. -/
structure StripMapData extends ConformalEquivalence strip target where
  base_value : toFun 0 = 1
  positive_derivative : 0 < (deriv toFun 0).re
  real_derivative : (deriv toFun 0).im = 0
  positive_real : ∀ s : ℝ, 0 < (toFun s).re ∧ (toFun s).im = 0
  lowerRate : ℝ
  upperRate : ℝ
  lowerRate_pos : 0 < lowerRate
  upperRate_pos : 0 < upperRate
  growth : ∀ s u : ℝ, 0 ≤ u →
    Real.exp (lowerRate * u) * (toFun s).re ≤ (toFun (s + u : ℝ)).re ∧
    (toFun (s + u : ℝ)).re ≤ Real.exp (upperRate * u) * (toFun s).re
  vertical_maximum : ∀ s y : ℝ, |y| < 1 / 2 →
    (toFun ((s : ℂ) + y * Complex.I)).re ≤ (toFun s).re
  rescaled_limit : TendstoLocallyUniformlyOn
    (fun b : ℝ => fun z : ℂ => toFun ((b : ℂ) + z) / toFun b)
    (fun z => Complex.exp (Real.pi * z)) atTop strip
  rescaled_derivative_limit : TendstoLocallyUniformlyOn
    (fun b : ℝ => deriv (fun z : ℂ => toFun ((b : ℂ) + z) / toFun b))
    (fun z => (Real.pi : ℂ) * Complex.exp (Real.pi * z)) atTop strip
