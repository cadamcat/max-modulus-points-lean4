module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import MaxModulusPoints.Blueprint.Data

/-!
# Heights of the chamber gates

A gate is centered halfway between consecutive chamber grid heights. Its
width bound places every gate point strictly between those heights, after
reflecting negative gates into the positive half-plane. Consequently no gate
meets a chamber grid line of either sign.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Blueprint

theorem gate_height_bounds (p : BlockParameters) (δ : GateIndex → ℝ) (i : GateIndex)
    (j : Bool) (hδ : δ i ≤ gateUpper i) {z : ℂ} (hz : z ∈ gate p δ i j) :
    chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) < sideSign j * z.im ∧
      sideSign j * z.im < chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1) := by
  let d : ℝ := (i.1 : ℝ) + 1
  let v : ℝ := i.2.val
  let b : ℝ := chamberBase
  let c : ℝ := b + (2 * v + 1) / (2 * d)
  let s : ℝ := sideSign j
  have hd : 0 < d := by
    dsimp only [d]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  have hδi : δ i ≤ 1 / d := hδ
  have hhalf : δ i / 2 ≤ 1 / (2 * d) := by
    calc
      δ i / 2 ≤ (1 / d) / 2 := div_le_div_of_nonneg_right hδi (by norm_num)
      _ = 1 / (2 * d) := by rw [div_div, mul_comm d 2]
  have hcenterL : c = b + v / d + 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd]
    ring
  have hcenterU : c = b + (v + 1) / d - 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd]
    ring
  have hsabs : |s| = 1 := by
    dsimp only [s]
    cases j <;> norm_num [sideSign]
  have hs2 : s * s = 1 := by
    dsimp only [s]
    cases j <;> norm_num [sideSign]
  have hid : s * (z.im - s * c) = s * z.im - c := by
    rw [mul_sub, ← mul_assoc, hs2, one_mul]
  have hg : |z.im - s * c| < δ i / 2 := hz.2
  have hdiff : |s * z.im - c| < δ i / 2 := by
    rw [← hid, abs_mul, hsabs, one_mul]
    exact hg
  have hbnds := abs_lt.mp hdiff
  change b + v / d < s * z.im ∧ s * z.im < b + (v + 1) / d
  constructor <;> linarith

theorem gate_avoids_grid (p : BlockParameters) (δ : GateIndex → ℝ) (i : GateIndex)
    (j : Bool) (hδ : δ i ≤ gateUpper i) {z : ℂ} (hz : z ∈ gate p δ i j) (k : ℕ) :
    |z.im| ≠ chamberBase + (k : ℝ) / ((i.1 : ℝ) + 1) := by
  let d : ℝ := (i.1 : ℝ) + 1
  let v : ℝ := i.2.val
  let b : ℝ := chamberBase
  let s : ℝ := sideSign j
  have hd : 0 < d := by
    dsimp only [d]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  have hb : 0 < b := by
    dsimp only [b, chamberBase]
    linarith [Real.pi_gt_three]
  have hvfrac : 0 ≤ v / d := div_nonneg (Nat.cast_nonneg _) hd.le
  have hheight := gate_height_bounds p δ i j hδ hz
  change b + v / d < s * z.im ∧ s * z.im < b + (v + 1) / d at hheight
  obtain ⟨hlo, hhi⟩ := hheight
  have hspos : 0 < s * z.im := by linarith
  have hsabs : |s| = 1 := by
    dsimp only [s]
    cases j <;> norm_num [sideSign]
  have habs : |z.im| = s * z.im := by
    calc
      |z.im| = |s * z.im| := by rw [abs_mul, hsabs, one_mul]
      _ = s * z.im := abs_of_pos hspos
  change |z.im| ≠ b + (k : ℝ) / d
  intro heq
  rw [habs] at heq
  by_cases hk : k ≤ i.2.val
  · have hk' : (k : ℝ) ≤ v := by
      dsimp only [v]
      exact_mod_cast hk
    have hdiv := div_le_div_of_nonneg_right hk' hd.le
    linarith
  · have hk' : v + 1 ≤ (k : ℝ) := by
      dsimp only [v]
      exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hk)
    have hdiv := div_le_div_of_nonneg_right hk' hd.le
    linarith

end MaxModulusPoints.TractGeometry
