import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import MaxModulusPoints.Blueprint.Data
/-!
# Separation of the block positions

Each successive block starts at least two units to the right of the previous
one, since each block has width one and the intervening gap is at least one.
-/

namespace MaxModulusPoints.TractGeometry

open Blueprint

theorem blockPosition_growth (p : BlockParameters) {n m : ℕ} (hnm : n ≤ m) :
    blockPosition p n + 2 * ((m : ℝ) - (n : ℝ)) ≤ blockPosition p m := by
  have hm : Monotone (fun k : ℕ => blockPosition p k - 2 * (k : ℝ)) := by
    apply monotone_nat_of_le_succ
    intro k
    simp only [blockPosition, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linarith [p.gap_ge_one (k + 1)]
  have h := hm hnm
  linarith

end MaxModulusPoints.TractGeometry
