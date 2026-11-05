module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Fintype.Option
public import MaxModulusPoints.Construction.CirclePoints

/-!

# A tract with passages, tunnels, and paired chambers

This is the rectangular-wall construction of Pardo-Simón–Sixsmith, Section 4.
Block `n` has `n+1` pairs of chambers. Horizontal walls are described as the
complement of the open height intervals, and vertical walls retain only the
specified passage openings, tunnel openings, and paired gates.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set Filter

noncomputable section

/-- The half-height of the passage, denoted by `τ₂` in Section 4. -/
def passageHalfHeight : ℝ := Real.pi / 2 - 1

theorem passageHalfHeight_pos : 0 < passageHalfHeight := by
  dsimp [passageHalfHeight]
  linarith [Real.pi_gt_three]

/-- The common height of the chambers in block `n`. -/
def chamberWidth (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) : ℝ)

theorem chamberWidth_pos (n : ℕ) : 0 < chamberWidth n := by
  dsimp [chamberWidth]
  positivity

theorem chamberWidth_mul_count (n : ℕ) : ((n + 1 : ℕ) : ℝ) * chamberWidth n = 1 := by
  simp only [chamberWidth, one_div]
  exact mul_inv_cancel₀ (by positivity)

abbrev GateIndex := Σ n : ℕ, Fin (n + 1)

/-- The passage is `none`; `false` denotes an upper chamber and `true` its reflection. -/
abbrev SliceIndex (n : ℕ) := Option (Bool × Fin (n + 1))

theorem card_sliceIndex (n : ℕ) : Fintype.card (SliceIndex n) = 2 * (n + 1) + 1 := by
  simp [SliceIndex, Fintype.card_prod]

def chamberBottom (n : ℕ) (m : Fin (n + 1)) : ℝ :=
  passageHalfHeight + (m.val : ℝ) * chamberWidth n

def chamberTop (n : ℕ) (m : Fin (n + 1)) : ℝ :=
  passageHalfHeight + ((m.val : ℝ) + 1) * chamberWidth n

theorem chamber_bounds (n : ℕ) (m : Fin (n + 1)) :
    passageHalfHeight ≤ chamberBottom n m ∧ chamberBottom n m < chamberTop n m ∧
      chamberTop n m ≤ Real.pi / 2 := by
  have hw := chamberWidth_pos n
  have hcount := chamberWidth_mul_count n
  have hm0 : (0 : ℝ) ≤ m.val := Nat.cast_nonneg _
  have hm : (m.val : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt m.isLt
  dsimp [chamberBottom, chamberTop]
  have hmul := mul_le_mul_of_nonneg_right hm hw.le
  dsimp [passageHalfHeight] at *
  constructor
  · nlinarith [mul_nonneg hm0 hw.le]
  constructor <;> nlinarith

def sliceBottom (n : ℕ) : SliceIndex n → ℝ
  | none => -passageHalfHeight
  | some (false, m) => chamberBottom n m
  | some (true, m) => -chamberTop n m

def sliceTop (n : ℕ) : SliceIndex n → ℝ
  | none => passageHalfHeight
  | some (false, m) => chamberTop n m
  | some (true, m) => -chamberBottom n m

theorem slice_bounds (n : ℕ) (i : SliceIndex n) :
    sliceBottom n i < sliceTop n i ∧ -Real.pi / 2 ≤ sliceBottom n i ∧
      sliceTop n i ≤ Real.pi / 2 := by
  rcases i with _ | ⟨s, m⟩
  · dsimp [sliceBottom, sliceTop]
    have hp := passageHalfHeight_pos
    dsimp [passageHalfHeight] at *
    exact ⟨by linarith, by linarith, by linarith⟩
  · obtain ⟨hmlo, hmlt, hmhi⟩ := chamber_bounds n m
    have hp := passageHalfHeight_pos
    cases s <;> dsimp only [sliceBottom, sliceTop]
    · exact ⟨hmlt, by linarith, hmhi⟩
    · exact ⟨neg_lt_neg hmlt, by linarith, by linarith⟩

def heightAllowed (n : ℕ) (y : ℝ) : Prop :=
  ∃ i : SliceIndex n, sliceBottom n i < y ∧ y < sliceTop n i

theorem heightAllowed_bound {n : ℕ} {y : ℝ} (hy : heightAllowed n y) :
    |y| < Real.pi / 2 := by
  obtain ⟨i, hlo, hhi⟩ := hy
  have hb := slice_bounds n i
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Arbitrary positions with at least one unit of free strip between consecutive blocks. -/
structure BlockLayout where
  base : ℕ → ℝ
  start_nonneg : 0 ≤ base 0
  gap : ∀ n, base n + 2 ≤ base (n + 1)

def BlockLayout.sample (L : BlockLayout) (n : ℕ) : ℝ := L.base n + 1 / 4

theorem BlockLayout.monotone_base (L : BlockLayout) : Monotone L.base :=
  monotone_nat_of_le_succ (fun n => le_trans (by linarith) (L.gap n))

theorem BlockLayout.base_nonneg (L : BlockLayout) (n : ℕ) : 0 ≤ L.base n :=
  L.start_nonneg.trans (L.monotone_base (Nat.zero_le n))

theorem BlockLayout.base_lower (L : BlockLayout) (n : ℕ) : 2 * (n : ℝ) ≤ L.base n := by
  induction n with
  | zero => simpa using L.start_nonneg
  | succ n ih =>
    have hg := L.gap n
    push_cast
    linarith

theorem BlockLayout.sample_tendsto (L : BlockLayout) : Tendsto L.sample atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  obtain ⟨N, hN⟩ := exists_nat_gt r
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hbound := L.base_lower n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  dsimp [BlockLayout.sample]
  linarith

/-- The selected line in one block misses the closed horizontal support of every other block. -/
theorem BlockLayout.sample_outside (L : BlockLayout) {n k : ℕ} (hne : n ≠ k) :
    L.sample n < L.base k ∨ L.base k + 1 < L.sample n := by
  rcases lt_or_gt_of_ne hne with hnk | hkn
  · left
    have hgap := L.gap n
    have hmono := L.monotone_base (Nat.succ_le_of_lt hnk)
    dsimp [BlockLayout.sample]
    linarith
  · right
    have hgap := L.gap k
    have hmono := L.monotone_base (Nat.succ_le_of_lt hkn)
    dsimp [BlockLayout.sample]
    linarith

def gateCenter (n : ℕ) (m : Fin (n + 1)) : ℝ :=
  (chamberBottom n m + chamberTop n m) / 2

/-- The two symmetric gates have the same height parameter. -/
def pairedGateHeight (δ : GateIndex → ℝ) (n : ℕ) (y : ℝ) : Prop :=
  ∃ m : Fin (n + 1), |y - gateCenter n m| < δ ⟨n, m⟩ / 2 ∨
    |y + gateCenter n m| < δ ⟨n, m⟩ / 2

/-- The numerical restrictions on tunnel and gate heights in Section 4. -/
structure AdmissibleHeights (t : ℕ → ℝ) (δ : GateIndex → ℝ) : Prop where
  tunnel_pos : ∀ n, 0 < t n
  tunnel_le : ∀ n, t n ≤ 1 / 4
  gate_pos : ∀ i, 0 < δ i
  gate_le : ∀ i, δ i ≤ chamberWidth i.1

/-- The walls of one blockage. The five alternatives are horizontal chamber walls,
the left wall, the passage-to-tunnel wall, the gated right wall, and tunnel walls. -/
def blockWalls (L : BlockLayout) (t : ℕ → ℝ) (δ : GateIndex → ℝ) (n : ℕ) : Set ℂ :=
  {z | L.base n ≤ z.re ∧ z.re ≤ L.base n + 1 ∧
    (¬heightAllowed n z.im ∨
      (z.re = L.base n ∧ passageHalfHeight ≤ |z.im|) ∨
      (z.re = L.base n + 1 / 2 ∧ |z.im| ≤ passageHalfHeight ∧ t n / 2 ≤ |z.im|) ∨
      (z.re = L.base n + 1 ∧ (passageHalfHeight ≤ |z.im| ∨ |z.im| ≤ t n / 2) ∧
        ¬(|z.im| < t n / 2 ∨ pairedGateHeight δ n z.im)) ∨
      (L.base n + 1 / 2 ≤ z.re ∧ |z.im| = t n / 2))}

/-- The half-infinite strip with rectangular walls and variable paired gates. -/
def chamberTract (L : BlockLayout) (t : ℕ → ℝ) (δ : GateIndex → ℝ) : Set ℂ :=
  {z | -2 < z.re ∧ |z.im| < Real.pi / 2 ∧ ∀ n, z ∉ blockWalls L t δ n}

theorem chamberTract_exp_injective (L : BlockLayout) (t : ℕ → ℝ) (δ : GateIndex → ℝ) :
    InjOn Complex.exp (chamberTract L t δ) := by
  apply exp_injOn_of_strip
  intro z hz
  have him := abs_lt.mp hz.2.1
  constructor <;> linarith [Real.pi_pos]

/-- The normalization point lies before every blockage. -/
theorem neg_one_mem_chamberTract (L : BlockLayout) (t : ℕ → ℝ) (δ : GateIndex → ℝ) :
    (-1 : ℂ) ∈ chamberTract L t δ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · simpa using Real.pi_div_two_pos
  · intro n hn
    have hb := L.base_nonneg n
    have hleft := hn.1
    norm_num at hleft
    linarith

/-- On the selected vertical line, membership in the tract is independent of all gate heights. -/
theorem mem_chamberTract_at_sample (L : BlockLayout) (t : ℕ → ℝ) (δ : GateIndex → ℝ)
    (n : ℕ) {z : ℂ} (hx : z.re = L.sample n) :
    z ∈ chamberTract L t δ ↔ heightAllowed n z.im := by
  constructor
  · intro hz
    by_contra hy
    apply hz.2.2 n
    refine ⟨?_, ?_, Or.inl hy⟩ <;> dsimp [BlockLayout.sample] at hx <;> linarith
  · intro hy
    refine ⟨?_, heightAllowed_bound hy, ?_⟩
    · have hb := L.base_nonneg n
      dsimp [BlockLayout.sample] at hx
      linarith
    · intro k hk
      by_cases hkn : k = n
      · subst k
        rcases hk.2.2 with hh | hl | hm | hr | ht
        · exact hh hy
        · dsimp [BlockLayout.sample] at hx
          linarith [hl.1]
        · dsimp [BlockLayout.sample] at hx
          linarith [hm.1]
        · dsimp [BlockLayout.sample] at hx
          linarith [hr.1]
        · dsimp [BlockLayout.sample] at hx
          linarith [ht.1]
      · have hout := L.sample_outside (Ne.symm hkn)
        have hlo := hk.1
        have hhi := hk.2.1
        rw [hx] at hlo hhi
        rcases hout with h | h <;> linarith

/-- The passage and full chamber slices at the selected line. -/
def fullSlice (L : BlockLayout) (n : ℕ) (i : SliceIndex n) : Set ℂ :=
  {z | z.re = L.sample n ∧ sliceBottom n i < z.im ∧ z.im < sliceTop n i}

theorem fullSlice_nonempty (L : BlockLayout) (n : ℕ) (i : SliceIndex n) :
    (fullSlice L n i).Nonempty := by
  refine ⟨⟨L.sample n, (sliceBottom n i + sliceTop n i) / 2⟩, rfl, ?_, ?_⟩
    <;> have hb := (slice_bounds n i).1 <;> dsimp <;> linarith

theorem fullSlice_subset_tract (L : BlockLayout) (t : ℕ → ℝ) (δ : GateIndex → ℝ)
    (n : ℕ) (i : SliceIndex n) : fullSlice L n i ⊆ chamberTract L t δ := by
  intro z hz
  exact (mem_chamberTract_at_sample L t δ n hz.1).mpr ⟨i, hz.2⟩

/-- The vertical section is exactly one passage and two chambers for every gate. -/
theorem chamberTract_vertical_section (L : BlockLayout) (t : ℕ → ℝ)
    (δ : GateIndex → ℝ) (n : ℕ) :
    chamberTract L t δ ∩ {z : ℂ | z.re = L.sample n} =
      ⋃ i : SliceIndex n, fullSlice L n i := by
  ext z
  constructor
  · rintro ⟨hz, hx⟩
    obtain ⟨i, hi⟩ := (mem_chamberTract_at_sample L t δ n hx).mp hz
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact ⟨fullSlice_subset_tract L t δ n i hi, hi.1⟩

#print axioms BlockLayout.sample_tendsto
#print axioms chamberTract_exp_injective
#print axioms mem_chamberTract_at_sample
#print axioms chamberTract_vertical_section

end

end MaxModulusPoints.Construction
