module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
public import MaxModulusPoints.Blueprint.Interfaces.HalfDisc

/-!
# `HalfDiscBarriers`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- A uniform half-disc barrier at the midpoint of a straight boundary wall. -/
def HalfDiscBarriers : Prop :=
  ∀ B ε : ℝ, 0 < B → 0 < ε → ∃ η : ℝ, 0 < η ∧
    ∀ G : ℂ → ℂ, DifferentiableOn ℂ G halfDisc →
      (∀ z ∈ halfDisc, (G z).re ≤ B) →
      (∀ ζ : ℂ, ‖ζ‖ < 1 → ζ.im = 0 → BoundaryUpper halfDisc G ζ 0) →
      ∀ z ∈ halfDisc, ‖z‖ < η → (G z).re ≤ ε
