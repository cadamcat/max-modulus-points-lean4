import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MaxModulusPoints.Blueprint.Data
/-!
# The normalization point of the chamber and gate tracts

All walls lie to the right of the imaginary axis, leaving `-1` in the tract.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_base_mem (p : BlockParameters) (δ : GateIndex → ℝ) :
    (-1 : ℂ) ∈ tract p δ := by
  have hpos : ∀ n, 0 ≤ blockPosition p n := by
    intro n
    unfold blockPosition
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => le_trans zero_le_one (p.gap_ge_one k))
      (Nat.cast_nonneg n)
  have hfront (s : Set ℂ) (a : ℝ) (hs : s ⊆ {z : ℂ | a ≤ z.re}) :
      frontier s ⊆ {z : ℂ | a ≤ z.re} :=
    frontier_subset_closure.trans
      (closure_minimal hs (isClosed_le continuous_const Complex.continuous_re))
  have hnwall : (-1 : ℂ) ∉ walls p := by
    intro hwall
    rcases mem_iUnion.mp hwall with ⟨n, hn⟩
    have hnneg : blockPosition p n ≤ (-1 : ℂ).re := by
      rcases hn with (hn | hn) | hn
      · exact hfront (passage p n) (blockPosition p n) (fun _ hz => hz.1) hn
      · apply hfront (tunnel p n) (blockPosition p n) ?_ hn
        intro z hz
        have ht := hz.1
        change blockPosition p n ≤ z.re
        linarith
      · rcases mem_iUnion.mp hn with ⟨m, hm⟩
        rcases mem_iUnion.mp hm with ⟨j, hj⟩
        exact hfront (chamber p ⟨n, m⟩ j) (blockPosition p n) (fun _ hz => hz.1) hj
    norm_num at hnneg
    linarith [hpos n]
  refine Or.inl (Or.inl ⟨?_, hnwall⟩)
  constructor
  · norm_num
  · simpa using half_pos Real.pi_pos

end MaxModulusPoints.TractGeometry
