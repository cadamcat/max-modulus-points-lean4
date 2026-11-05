module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Tactic.NormNum
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.BlockPositions

/-!
# Closedness of the chamber and tunnel walls

The walls within each block form a finite union of closed sets. The block
positions tend to the right, so this family is locally finite.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint
open scoped Topology

/-- The passage, tunnel and chamber walls belonging to a single block. -/
def blockWalls (p : BlockParameters) (n : ℕ) : Set ℂ :=
  frontier (passage p n) ∪ frontier (tunnel p n) ∪
    ⋃ m : Fin (n + 1), ⋃ j : Bool, frontier (chamber p ⟨n, m⟩ j)

theorem blockWalls_re_bounds (p : BlockParameters) (n : ℕ) {z : ℂ}
    (hz : z ∈ blockWalls p n) :
    blockPosition p n ≤ z.re ∧ z.re ≤ blockPosition p n + 1 := by
  have hfront (s : Set ℂ)
      (hs : s ⊆ {w : ℂ | blockPosition p n ≤ w.re ∧ w.re ≤ blockPosition p n + 1}) :
      frontier s ⊆ {w : ℂ | blockPosition p n ≤ w.re ∧ w.re ≤ blockPosition p n + 1} :=
    frontier_subset_closure.trans (closure_minimal hs
      ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)))
  rcases hz with (hz | hz) | hz
  · apply hfront (passage p n) ?_ hz
    intro w hw
    refine ⟨hw.1, ?_⟩
    have hr := hw.2.1
    change w.re ≤ blockPosition p n + 1
    linarith
  · apply hfront (tunnel p n) ?_ hz
    intro w hw
    refine ⟨?_, hw.2.1⟩
    have hl := hw.1
    change blockPosition p n ≤ w.re
    linarith
  · rcases mem_iUnion.mp hz with ⟨m, hm⟩
    rcases mem_iUnion.mp hm with ⟨j, hj⟩
    exact hfront (chamber p ⟨n, m⟩ j) (fun _ hw => ⟨hw.1, hw.2.1⟩) hj

theorem walls_isClosed (p : BlockParameters) : IsClosed (walls p) := by
  let W : ℕ → Set ℂ := blockWalls p
  have hclosed (n : ℕ) : IsClosed (W n) := by
    exact (isClosed_frontier.union isClosed_frontier).union
      (isClosed_iUnion_of_finite fun _ =>
        isClosed_iUnion_of_finite fun _ => isClosed_frontier)
  have hzero : 1 ≤ blockPosition p 0 := by
    simpa [blockPosition] using p.gap_ge_one 0
  have hindex (n : ℕ) : (n : ℝ) ≤ blockPosition p n := by
    have h := blockPosition_growth p (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero] at h
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hlf : LocallyFinite W := by
    intro z
    obtain ⟨N, hN⟩ := exists_nat_gt (z.re + 1)
    refine ⟨{w : ℂ | w.re < z.re + 1}, ?_, ?_⟩
    · exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
        change z.re < z.re + 1
        linarith)
    · refine (finite_Iio N).subset ?_
      intro n hn
      rcases hn with ⟨w, hw, hwt⟩
      have hs := (blockWalls_re_bounds p n hw).1
      change w.re < z.re + 1 at hwt
      have hnN : (n : ℝ) < N := by linarith [hindex n]
      exact_mod_cast hnN
  exact hlf.isClosed_iUnion hclosed

theorem walls_localization (p : BlockParameters) (n : ℕ) {z : ℂ}
    (hl : blockPosition p n - 1 < z.re) (hr : z.re < blockPosition p n + 2) :
    z ∈ walls p ↔ z ∈ blockWalls p n := by
  constructor
  · intro hz
    rcases mem_iUnion.mp hz with ⟨k, hk⟩
    have hb := blockWalls_re_bounds p k hk
    rcases lt_trichotomy k n with hkn | hkn | hkn
    · have hg := blockPosition_growth p hkn.le
      have hc : (k : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hkn
      exfalso
      linarith
    · subst k
      exact hk
    · have hg := blockPosition_growth p hkn.le
      have hc : (n : ℝ) + 1 ≤ (k : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hkn
      exfalso
      linarith
  · intro hz
    exact mem_iUnion.mpr ⟨n, hz⟩

end MaxModulusPoints.TractGeometry
