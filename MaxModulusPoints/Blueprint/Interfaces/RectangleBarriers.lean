module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
public import MaxModulusPoints.Blueprint.Interfaces.ClosedGateInterval
public import MaxModulusPoints.Blueprint.Interfaces.Rectangle

/-!
# `RectangleBarriers`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- A boundary interval of length s has harmonic measure O(s), uniformly on the
full vertical slice at real part 1/4, including its approaches to the walls. -/
def RectangleBarriers : Prop :=
  ∀ h y ρ : ℝ, 0 < h → 0 < ρ → ρ < y → y + ρ < h →
    ∃ K : ℝ, 0 < K ∧ ∀ s B : ℝ, 0 < s → s ≤ ρ → 0 < B →
      ∀ G : ℂ → ℂ, DifferentiableOn ℂ G (rectangle h) →
        (∀ z ∈ rectangle h, (G z).re ≤ B) →
        (∀ ζ ∈ frontier (rectangle h) \ closedGateInterval y s,
          BoundaryUpper (rectangle h) G ζ 0) →
        ∀ z ∈ rectangle h, z.re = 1 / 4 → (G z).re ≤ B * K * s
