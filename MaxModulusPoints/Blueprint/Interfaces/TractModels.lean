module

public import MaxModulusPoints.Blueprint.Data

/-!
# `TractModels`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- Normalized conformal models on the concrete chamber and gate tracts. -/
def TractModels : Prop :=
  ∀ (p : BlockParameters) (δ : GateIndex → ℝ),
    (∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) → Nonempty (LogModel (tract p δ))
