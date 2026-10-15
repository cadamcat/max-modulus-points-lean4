import MaxModulusPoints.Blueprint.Data
/-!
# Decay between the interior contour and the tract walls

The canonical Cauchy construction approximates the exponential conformal
function on the core. Extending the approximation to the original tract
requires decay of that function on the portion to the left of the interior
contour.
-/

namespace MaxModulusPoints.CauchyApproximation

open Blueprint

/-- One bound on the exponential conformal function outside the interior
core, uniform over the chamber and gate tracts and their normalized maps. -/
def TractWallDecay : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : BlockParameters) (δ : GateIndex → ℝ),
    (∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) → ∀ G : LogModel (tract p δ),
    ∀ z ∈ tract p δ, 1 < ‖Complex.exp z‖ →
      (G.toFun z).re ≤ 1 - 13 * max 0 (Real.log |(G.toFun z).im|) →
        ‖Complex.exp (G.toFun z)‖ ≤ C / ‖Complex.exp z‖

end MaxModulusPoints.CauchyApproximation
