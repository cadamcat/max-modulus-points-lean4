import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
/-!
# Bounds at the finite end of a conformal tract

Uniform bounds on the images of the left-hand portions of a tract imply
that inverse images of sequences escaping in the target move to the right.
-/

namespace MaxModulusPoints.TractGeometry

open Set Filter
open Blueprint

def TractEndBounds : Prop :=
  ∀ (p : BlockParameters) (δ : GateIndex → ℝ),
    (∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) →
    ∀ e : NormalizedSymmetricEquivalence (tract p δ) target (-1) 1,
      ∀ R : ℝ, ∃ B : ℝ, ∀ z ∈ tract p δ, z.re ≤ R → ‖e.toFun z‖ ≤ B

theorem tract_escape_of_end_bounds (hbound : TractEndBounds)
    (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ gateUpper i)
    (e : NormalizedSymmetricEquivalence (tract p δ) target (-1) 1)
    (z : ℕ → ℂ) (hz : ∀ n, z n ∈ target)
    (ht : Tendsto (fun n => ‖z n‖) atTop atTop) :
    Tendsto (fun n => (e.invFun (z n)).re) atTop atTop := by
  apply tendsto_atTop.mpr
  intro R
  obtain ⟨B, hB⟩ := hbound p δ hδ e R
  filter_upwards [ht.eventually (eventually_ge_atTop (B + 1))] with n hn
  by_contra h
  have hle : (e.invFun (z n)).re ≤ R := le_of_lt (lt_of_not_ge h)
  have hnorm := hB (e.invFun (z n)) (e.inverse_mapsTo (hz n)) hle
  rw [e.right_inv _ (hz n)] at hnorm
  linarith

end MaxModulusPoints.TractGeometry
