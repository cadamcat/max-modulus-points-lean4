module

public import MaxModulusPoints.Blueprint.Data

/-!
# `BottleneckEstimates`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- The consequence of Ahlfors' crosscut theorem needed for the narrow tunnel. -/
def BottleneckEstimates : Prop :=
  ∀ (p : BlockParameters) (δ : GateIndex → ℝ),
    (∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) →
    ∀ φ : ConformalEquivalence (tract p δ) strip,
      φ.toFun (-1) = 0 → 0 < (deriv φ.toFun (-1)).re →
      (deriv φ.toFun (-1)).im = 0 →
      ∀ n z, z ∈ cleanSlice p n → ∀ w, w ∈ passageSlice p n →
        1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi ≤
          (φ.toFun z).re - (φ.toFun w).re
