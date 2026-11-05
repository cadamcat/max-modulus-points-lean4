module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge

/-!
# `FixedRempeApproximation`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- The fixed-model approximation for the chamber and gate tracts used in the
construction, with an error bound that is uniform over their normalized models. -/
def FixedRempeApproximation : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ (p : BlockParameters) (δ : GateIndex → ℝ),
    (∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) → ∀ G : LogModel (tract p δ),
    ∃ f : ℂ → ℂ, Entire f ∧ ¬ IsMonomial f ∧
      (∀ z, f (star z) = star (f z)) ∧
      (∀ z ∈ tract p δ, 1 < ‖Complex.exp z‖ →
        ‖f (Complex.exp z) - Complex.exp (G.toFun z)‖ ≤ M / ‖Complex.exp z‖) ∧
      (∀ z, z ∉ Complex.exp '' tract p δ → 1 < ‖z‖ → ‖f z‖ ≤ M / ‖z‖)
