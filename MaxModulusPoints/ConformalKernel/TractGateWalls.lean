import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.ConformalKernel.VerticalGates
import MaxModulusPoints.TractGeometry.BlockPositions
/-!
# The variable vertical walls of the chamber tracts

The right sides of the chambers are the locally finite walls on which the
gate parameters act. A gate meets only its own wall, and none of these walls
meets a restored passage or tunnel opening.
-/

noncomputable section

namespace MaxModulusPoints.ConformalKernel

open Set Blueprint
open scoped Topology

/-- Real coordinate of a variable chamber wall. -/
def gateWallPosition (p : BlockParameters) (q : GateIndex × Bool) : ℝ :=
  blockPosition p q.1.1 + 1

/-- Imaginary coordinate of the center of a variable chamber wall. -/
def gateWallCenter (q : GateIndex × Bool) : ℝ :=
  sideSign q.2 * (chamberBase + (2 * (q.1.2.val : ℝ) + 1) /
    (2 * ((q.1.1 : ℝ) + 1)))

/-- Half-height of a variable chamber wall. -/
def gateWallRadius (q : GateIndex × Bool) : ℝ := gateUpper q.1 / 2

/-- Lower height of a chamber after reflection to the upper half-plane. -/
def gateWallLower (i : GateIndex) : ℝ :=
  chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1)

/-- Upper height of a chamber after reflection to the upper half-plane. -/
def gateWallUpper (i : GateIndex) : ℝ :=
  chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1)

/-- The full closed right side of a chamber. -/
def tractGateWall (p : BlockParameters) (q : GateIndex × Bool) : Set ℂ :=
  verticalWall (gateWallPosition p q) (gateWallCenter q) (gateWallRadius q)

private theorem gateWall_endpoints (i : GateIndex) :
    (chamberBase + (2 * (i.2.val : ℝ) + 1) / (2 * ((i.1 : ℝ) + 1))) -
        gateUpper i / 2 = gateWallLower i ∧
    (chamberBase + (2 * (i.2.val : ℝ) + 1) / (2 * ((i.1 : ℝ) + 1))) +
        gateUpper i / 2 = gateWallUpper i := by
  have hd : (i.1 : ℝ) + 1 ≠ 0 := by positivity
  constructor <;> dsimp [gateUpper, gateWallLower, gateWallUpper] <;> field_simp <;> ring

private theorem gate_displacement_le_iff (i : GateIndex) (j : Bool) (z : ℂ) :
    |z.im - gateWallCenter (i, j)| ≤ gateWallRadius (i, j) ↔
      gateWallLower i ≤ sideSign j * z.im ∧ sideSign j * z.im ≤ gateWallUpper i := by
  obtain ⟨hl, hu⟩ := gateWall_endpoints i
  cases j <;> simp only [gateWallCenter, gateWallRadius, sideSign, Bool.false_eq_true,
    ↓reduceIte, neg_one_mul, one_mul, abs_le] <;>
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem gate_displacement_lt_iff (i : GateIndex) (j : Bool) (z : ℂ) :
    |z.im - gateWallCenter (i, j)| < gateWallRadius (i, j) ↔
      gateWallLower i < sideSign j * z.im ∧ sideSign j * z.im < gateWallUpper i := by
  obtain ⟨hl, hu⟩ := gateWall_endpoints i
  cases j <;> simp only [gateWallCenter, gateWallRadius, sideSign, Bool.false_eq_true,
    ↓reduceIte, neg_one_mul, one_mul, abs_lt] <;>
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Membership in a wall in terms of the chamber's two heights. -/
theorem mem_tractGateWall_iff (p : BlockParameters) (i : GateIndex) (j : Bool) (z : ℂ) :
    z ∈ tractGateWall p (i, j) ↔ z.re = blockPosition p i.1 + 1 ∧
      gateWallLower i ≤ sideSign j * z.im ∧ sideSign j * z.im ≤ gateWallUpper i := by
  exact and_congr_right fun _ => gate_displacement_le_iff i j z

private theorem block_interval_unique (p : BlockParameters) {n m : ℕ} {x : ℝ}
    (hn : blockPosition p n ≤ x ∧ x ≤ blockPosition p n + 1)
    (hm : blockPosition p m ≤ x ∧ x ≤ blockPosition p m + 1) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · have hg := TractGeometry.blockPosition_growth p h.le
    have hc : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt h
    exfalso
    linarith
  · exact h
  · have hg := TractGeometry.blockPosition_growth p h.le
    have hc : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
    exfalso
    linarith

/-- The full variable wall is part of the removed chamber frontier. -/
theorem tractGateWall_subset_walls (p : BlockParameters) (q : GateIndex × Bool) :
    tractGateWall p q ⊆ walls p := by
  rintro z hz
  obtain ⟨hx, hl, hu⟩ := (mem_tractGateWall_iff p q.1 q.2 z).mp hz
  have hm : z ∈ chamber p q.1 q.2 :=
    ⟨by linarith, by linarith, hl, hu⟩
  have hnot : z ∉ interior (chamber p q.1 q.2) := by
    intro hi
    have hsub : chamber p q.1 q.2 ⊆ {w : ℂ | w.re ≤ blockPosition p q.1.1 + 1} :=
      fun _ h => h.2.1
    have he := interior_mono hsub hi
    rw [Complex.interior_setOfPred_re_le] at he
    exact (not_lt_of_ge hx.ge) he
  have hf := (mem_frontier_iff_notMem_interior hm).mpr hnot
  exact mem_iUnion.mpr ⟨q.1.1, Or.inr (mem_iUnion.mpr ⟨q.1.2,
    mem_iUnion.mpr ⟨q.2, hf⟩⟩)⟩

/-- No passage or tunnel opening meets a variable chamber wall. -/
theorem tractGateWall_not_mem_openings (p : BlockParameters) (q : GateIndex × Bool)
    {z : ℂ} (hz : z ∈ tractGateWall p q) (n : ℕ) : z ∉ openings p n := by
  obtain ⟨hx, hl, _⟩ := (mem_tractGateWall_iff p q.1 q.2 z).mp hz
  intro ho
  have hb : blockPosition p n ≤ z.re ∧ z.re ≤ blockPosition p n + 1 := by
    rcases ho with ho | ho | ho <;> constructor <;> linarith [ho.1]
  have hn : q.1.1 = n := block_interval_unique p ⟨by linarith, by linarith⟩ hb
  have hfrac : 0 ≤ (q.1.2.val : ℝ) / ((q.1.1 : ℝ) + 1) := by positivity
  have hy : chamberBase ≤ |z.im| := by
    dsimp [gateWallLower] at hl
    cases hq : q.2 <;> simp [hq, sideSign] at hl
    · linarith [neg_le_abs z.im]
    · linarith [le_abs_self z.im]
  rw [← hn] at ho
  rcases ho with ho | ho | ho
  · linarith [ho.1]
  · linarith [ho.1]
  · have ht := p.tunnel_le_quarter q.1.1
    have hpi := Real.pi_gt_three
    dsimp [chamberBase] at hy
    linarith [ho.2]

/-- A gate of admissible height meets only its own full chamber wall. -/
theorem tractGateWall_gate_unique (p : BlockParameters) {δ : GateIndex → ℝ}
    (hδ : ∀ i, δ i ≤ gateUpper i) {q r : GateIndex × Bool} {z : ℂ}
    (hz : z ∈ tractGateWall p q) (hg : z ∈ gate p δ r.1 r.2) : q = r := by
  rcases q with ⟨⟨n, m⟩, j⟩
  rcases r with ⟨⟨k, l⟩, e⟩
  obtain ⟨hx, hw⟩ := (mem_tractGateWall_iff p ⟨n, m⟩ j z).mp hz
  have hk : n = k := block_interval_unique p (x := z.re)
    ⟨by linarith, by linarith⟩ ⟨by linarith [hg.1], by linarith [hg.1]⟩
  subst k
  have hstrict : |z.im - gateWallCenter (⟨n, l⟩, e)| <
      gateWallRadius (⟨n, l⟩, e) := lt_of_lt_of_le hg.2 (div_le_div_of_nonneg_right
        (hδ ⟨n, l⟩) (by norm_num))
  have hg' := (gate_displacement_lt_iff ⟨n, l⟩ e z).mp hstrict
  have hbase : 0 < chamberBase := by dsimp [chamberBase]; linarith [Real.pi_gt_three]
  have hm0 : 0 ≤ (m.val : ℝ) / ((n : ℝ) + 1) := by positivity
  have hl0 : 0 ≤ (l.val : ℝ) / ((n : ℝ) + 1) := by positivity
  have hje : j = e := by
    by_contra h
    dsimp [gateWallLower] at hw hg'
    cases j <;> cases e <;> simp [sideSign] at * <;> linarith
  subst e
  have hml : m = l := by
    apply Fin.ext
    have hd : 0 < (n : ℝ) + 1 := by positivity
    rcases lt_trichotomy m.val l.val with h | h | h
    · have hc : (m.val : ℝ) + 1 ≤ l.val := by exact_mod_cast Nat.succ_le_of_lt h
      have hh := div_le_div_of_nonneg_right hc hd.le
      dsimp [gateWallLower, gateWallUpper] at hw hg'
      exfalso
      linarith [hw.2, hg'.1]
    · exact h
    · have hc : (l.val : ℝ) + 1 ≤ m.val := by exact_mod_cast Nat.succ_le_of_lt h
      have hh := div_le_div_of_nonneg_right hc hd.le
      dsimp [gateWallLower, gateWallUpper] at hw hg'
      exfalso
      linarith [hw.1, hg'.2]
  subst l
  rfl

/-- The family of variable chamber walls is locally finite. -/
theorem locallyFinite_tractGateWall (p : BlockParameters) : LocallyFinite (tractGateWall p) := by
  intro z
  obtain ⟨N, hN⟩ := exists_nat_gt (z.re + 1)
  refine ⟨{w : ℂ | w.re < z.re + 1}, ?_, ?_⟩
  · exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
      change z.re < z.re + 1
      linarith)
  · let E := (Σ n : Fin N, Fin (n.val + 1)) × Bool
    have hfinite : (range (fun q : E => ((⟨q.1.1.val, q.1.2⟩ : GateIndex), q.2))).Finite :=
      finite_range _
    apply hfinite.subset
    rintro ⟨⟨n, m⟩, j⟩ ⟨w, hw, hwt⟩
    have hx := hw.1
    change w.re = blockPosition p n + 1 at hx
    have hg := TractGeometry.blockPosition_growth p (Nat.zero_le n)
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    simp only [Nat.cast_zero, sub_zero] at hg
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnN : (n : ℝ) < N := by
      change w.re < z.re + 1 at hwt
      linarith
    have hn : n < N := by exact_mod_cast hnN
    exact ⟨(⟨⟨n, hn⟩, m⟩, j), rfl⟩

#print axioms mem_tractGateWall_iff
#print axioms tractGateWall_subset_walls
#print axioms tractGateWall_not_mem_openings
#print axioms tractGateWall_gate_unique
#print axioms locallyFinite_tractGateWall

end MaxModulusPoints.ConformalKernel
