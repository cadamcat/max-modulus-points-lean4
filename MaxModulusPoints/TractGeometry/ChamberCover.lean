import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.RegularCoordinates
/-!
# Covering the chamber heights

Above the passage height, each point with regular coordinates lies strictly
between two consecutive chamber grid heights. The natural floor selects the
layer, and the sign of the imaginary coordinate selects its reflection.
-/

namespace MaxModulusPoints.TractGeometry

open Blueprint

theorem regularCoordinates_chamber_layer (p : BlockParameters) (n : ℕ) {z : ℂ}
    (hz : z ∈ regularCoordinates p) (hbase : chamberBase < |z.im|)
    (htop : |z.im| < Real.pi / 2) :
    ∃ (m : Fin (n + 1)) (j : Bool),
      chamberBase + (m.val : ℝ) / ((n : ℝ) + 1) < sideSign j * z.im ∧
      sideSign j * z.im < chamberBase + ((m.val : ℝ) + 1) / ((n : ℝ) + 1) := by
  let d : ℝ := (n : ℝ) + 1
  let t : ℝ := (|z.im| - chamberBase) * d
  let k : ℕ := ⌊t⌋₊
  have hd : 0 < d := by dsimp [d]; positivity
  have ht0 : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hbase.le) hd.le
  have htbound : t < d := by
    have hsmall : |z.im| - chamberBase < 1 := by
      dsimp only [chamberBase]
      linarith
    simpa only [one_mul] using mul_lt_mul_of_pos_right hsmall hd
  have hk : k < n + 1 := (Nat.floor_lt ht0).mpr (by
    simpa only [Nat.cast_add, Nat.cast_one] using htbound)
  have hle : (k : ℝ) / d ≤ |z.im| - chamberBase :=
    (div_le_iff₀ hd).mpr (Nat.floor_le ht0)
  have hlt : |z.im| - chamberBase < ((k : ℝ) + 1) / d :=
    (lt_div_iff₀ hd).mpr (Nat.lt_floor_add_one t)
  have hlo : chamberBase + (k : ℝ) / d < |z.im| := by
    have hweak : chamberBase + (k : ℝ) / d ≤ |z.im| := by linarith
    rcases lt_or_eq_of_le hweak with h | h
    · exact h
    · exact (hz.2.2 n k h.symm).elim
  have hhi : |z.im| < chamberBase + ((k : ℝ) + 1) / d := by linarith
  have hsign : ∃ j : Bool, sideSign j * z.im = |z.im| := by
    by_cases hnonneg : 0 ≤ z.im
    · exact ⟨true, by simp [sideSign, abs_of_nonneg hnonneg]⟩
    · exact ⟨false, by simp [sideSign, abs_of_neg (lt_of_not_ge hnonneg)]⟩
  obtain ⟨j, hj⟩ := hsign
  refine ⟨⟨k, hk⟩, j, ?_⟩
  rw [hj]
  exact ⟨hlo, hhi⟩

end MaxModulusPoints.TractGeometry
