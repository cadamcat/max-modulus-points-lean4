import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.BlockPositions
import MaxModulusPoints.TractGeometry.Walls
/-!
# Restored points on a block's walls

Separated block intervals prevent an opening or gate in one block from
restoring a wall point in another. Thus only the openings and gates of the
same block need to be excluded when constructing paths in the complement.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem blockWalls_mem_tract_iff (p : BlockParameters) (δ : GateIndex → ℝ) (n : ℕ)
    {z : ℂ} (hz : z ∈ blockWalls p n) :
    z ∈ tract p δ ↔ z ∈ openings p n ∨
      ∃ (m : Fin (n + 1)) (j : Bool), z ∈ gate p δ ⟨n, m⟩ j := by
  obtain ⟨hnl, hnr⟩ := blockWalls_re_bounds p n hz
  have hindex {m : ℕ}
      (hm : blockPosition p m ≤ z.re ∧ z.re ≤ blockPosition p m + 1) : m = n := by
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · have hg := blockPosition_growth p hmn.le
      have hc : (m : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hmn
      exfalso
      linarith [hm.1, hm.2]
    · exact hmn
    · have hg := blockPosition_growth p hmn.le
      have hc : (n : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hmn
      exfalso
      linarith [hm.1, hm.2]
  constructor
  · intro hmem
    rcases hmem with (hclean | hopen) | hgate
    · exact (hclean.2 (mem_iUnion.mpr ⟨n, hz⟩)).elim
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hopen
      have hbounds : blockPosition p m ≤ z.re ∧ z.re ≤ blockPosition p m + 1 := by
        rcases hm with h | h | h <;> constructor <;> linarith [h.1]
      have heq : m = n := hindex hbounds
      subst m
      exact Or.inl hm
    · obtain ⟨⟨m, k⟩, hi⟩ := mem_iUnion.mp hgate
      obtain ⟨j, hj⟩ := mem_iUnion.mp hi
      have hbounds : blockPosition p m ≤ z.re ∧ z.re ≤ blockPosition p m + 1 := by
        have hre := hj.1
        constructor <;> linarith
      have heq : m = n := hindex hbounds
      subst m
      exact Or.inr ⟨k, j, hj⟩
  · rintro (hopen | ⟨m, j, hgate⟩)
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, hopen⟩))
    · exact Or.inr (mem_iUnion.mpr ⟨⟨n, m⟩, mem_iUnion.mpr ⟨j, hgate⟩⟩)

end MaxModulusPoints.TractGeometry
