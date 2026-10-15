import MaxModulusPoints.Blueprint.Data

/-!
# `BoundaryUpper`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- Boundary upper limits expressed without a continuity extension to corners. -/
def BoundaryUpper (U : Set ℂ) (G : ℂ → ℂ) (ζ : ℂ) (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[U] ζ, (G z).re ≤ B + ε
