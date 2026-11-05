module

public import Mathlib.Algebra.Order.Floor.Semiring
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Construction.OpenChamberGeometry
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# The bounded region before a passage crosscut

The left part of the chamber tract can be cut at a passage sample.
Its boundary inside the tract consists only of that passage slice;
the chamber and passage walls exclude every other possible crossing.
This supplies the geometry for Pardo-Simón–Sixsmith, Proposition 4.2.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set Filter Metric

noncomputable section

theorem block_support_unique (p : Blueprint.BlockParameters) {n k : ℕ} {x : ℝ}
    (hn : Blueprint.blockPosition p n ≤ x ∧ x ≤ Blueprint.blockPosition p n + 1)
    (hk : Blueprint.blockPosition p k ≤ x ∧ x ≤ Blueprint.blockPosition p k + 1) : n = k := by
  rcases lt_trichotomy n k with hnk | hnk | hkn
  · have hm := (blockParametersLayout p).monotone_base (Nat.succ_le_of_lt hnk)
    have hg := (blockParametersLayout p).gap n
    change Blueprint.blockPosition p (n + 1) ≤ Blueprint.blockPosition p k at hm
    change Blueprint.blockPosition p n + 2 ≤ Blueprint.blockPosition p (n + 1) at hg
    linarith [hn.2, hk.1]
  · exact hnk
  · have hm := (blockParametersLayout p).monotone_base (Nat.succ_le_of_lt hkn)
    have hg := (blockParametersLayout p).gap k
    change Blueprint.blockPosition p (k + 1) ≤ Blueprint.blockPosition p n at hm
    change Blueprint.blockPosition p k + 2 ≤ Blueprint.blockPosition p (k + 1) at hg
    linarith [hk.2, hn.1]

theorem opening_support (p : Blueprint.BlockParameters) (n : ℕ) {z : ℂ}
    (hz : z ∈ Blueprint.openings p n) :
    Blueprint.blockPosition p n ≤ z.re ∧ z.re ≤ Blueprint.blockPosition p n + 1 := by
  rcases hz with ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩ <;> constructor <;> linarith

theorem gate_support (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (i : Blueprint.GateIndex) (j : Bool) {z : ℂ} (hz : z ∈ Blueprint.gate p δ i j) :
    Blueprint.blockPosition p i.1 ≤ z.re ∧ z.re ≤ Blueprint.blockPosition p i.1 + 1 :=
  ⟨by linarith [hz.1], hz.1.le⟩

theorem tract_subset_ambient (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i) :
    Blueprint.tract p δ ⊆ {z : ℂ | -2 < z.re ∧ |z.im| < Real.pi / 2} := by
  intro z hz
  rcases hz with (hbase | hopen) | hgate
  · exact hbase.1
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hopen
    have hx := (opening_support p n hn).1
    have hp := (blockParametersLayout p).base_nonneg n
    change 0 ≤ Blueprint.blockPosition p n at hp
    refine ⟨by linarith, ?_⟩
    rcases hn with ⟨_, hy⟩ | ⟨_, hy⟩ | ⟨_, hy⟩
    · dsimp [Blueprint.chamberBase] at hy
      linarith
    · linarith [p.tunnel_le_quarter n, Real.pi_gt_three]
    · linarith [p.tunnel_le_quarter n, Real.pi_gt_three]
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hgate
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    have hx := (gate_support p δ i j hj).1
    have hp := (blockParametersLayout p).base_nonneg i.1
    change 0 ≤ Blueprint.blockPosition p i.1 at hp
    refine ⟨by linarith, ?_⟩
    have hh := upperChamberHeight_bounds i
    have hy := hj.2
    rw [← upperChamberHeight_gate_center] at hy
    have hsign : |Blueprint.sideSign j * upperChamberHeight i| = upperChamberHeight i := by
      cases j <;> simp [Blueprint.sideSign, abs_of_pos hh.1]
    have htri := abs_add_le (z.im - Blueprint.sideSign j * upperChamberHeight i)
      (Blueprint.sideSign j * upperChamberHeight i)
    rw [sub_add_cancel, hsign] at htri
    have hd := hδ i
    rw [gateUpper_eq_chamberWidth] at hd
    linarith

/-- Before the sample line, a wall above the passage opening is not
restored by any opening or gate, including those in other blocks. -/
theorem left_section_wall_not_mem_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (n : ℕ) {z : ℂ}
    (hx : Blueprint.blockPosition p n ≤ z.re ∧ z.re ≤ Blueprint.slicePosition p n)
    (hy : Blueprint.chamberBase ≤ |z.im|) (hw : z ∈ Blueprint.walls p) :
    z ∉ Blueprint.tract p δ := by
  intro hz
  have hsupport : Blueprint.blockPosition p n ≤ z.re ∧ z.re ≤ Blueprint.blockPosition p n + 1 :=
    ⟨hx.1, by dsimp [Blueprint.slicePosition] at hx; linarith [hx.2]⟩
  rcases hz with (hb | ho) | hg
  · exact hb.2 hw
  · obtain ⟨k, hk⟩ := mem_iUnion.mp ho
    have hnk := block_support_unique p hsupport (opening_support p k hk)
    subst k
    rcases hk with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · linarith
    · dsimp [Blueprint.slicePosition] at hx
      linarith [hx.2]
    · dsimp [Blueprint.slicePosition] at hx
      linarith [hx.2]
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hg
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    have hnk := block_support_unique p hsupport (gate_support p δ i j hj)
    have he := hj.1
    rw [← hnk] at he
    dsimp [Blueprint.slicePosition] at hx
    linarith [hx.2]

theorem mem_frontier_of_left_support {S : Set ℂ} {a : ℝ}
    (hsupport : ∀ w ∈ S, a ≤ w.re) {z : ℂ} (hz : z ∈ S) (hx : z.re = a) :
    z ∈ frontier S := by
  refine ⟨subset_closure hz, ?_⟩
  intro hin
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hin)
  let w := z - ((r / 2 : ℝ) : ℂ)
  have hw : w ∈ ball z r := by
    rw [mem_ball, dist_eq_norm]
    have he : w - z = -((r / 2 : ℝ) : ℂ) := by dsimp [w]; ring
    rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    linarith
  have h := hsupport w (hball hw)
  change a ≤ z.re - r / 2 at h
  linarith

theorem mem_frontier_of_abs_im_support {S : Set ℂ} {b : ℝ}
    (hsupport : ∀ w ∈ S, |w.im| ≤ b) {z : ℂ} (hz : z ∈ S) (hy : |z.im| = b) :
    z ∈ frontier S := by
  refine ⟨subset_closure hz, ?_⟩
  intro hin
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hin)
  by_cases hsign : 0 ≤ z.im
  · let w := z + ((r / 2 : ℝ) : ℂ) * Complex.I
    have hw : w ∈ ball z r := by
      rw [mem_ball, dist_eq_norm]
      have he : w - z = ((r / 2 : ℝ) : ℂ) * Complex.I := by dsimp [w]; ring
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      linarith
    have h := (le_abs_self w.im).trans (hsupport w (hball hw))
    have he : w.im = z.im + r / 2 := by simp [w]
    rw [abs_of_nonneg hsign] at hy
    linarith
  · let w := z - ((r / 2 : ℝ) : ℂ) * Complex.I
    have hw : w ∈ ball z r := by
      rw [mem_ball, dist_eq_norm]
      have he : w - z = -(((r / 2 : ℝ) : ℂ) * Complex.I) := by dsimp [w]; ring
      rw [he, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      linarith
    have h := (neg_le_abs w.im).trans (hsupport w (hball hw))
    have he : w.im = z.im - r / 2 := by simp [w]
    rw [abs_of_neg (lt_of_not_ge hsign)] at hy
    linarith

theorem exists_chamber_height (n : ℕ) {y : ℝ}
    (hlo : Blueprint.chamberBase ≤ y) (hhi : y < Real.pi / 2) :
    ∃ m : Fin (n + 1), chamberBottom n m ≤ y ∧ y < chamberTop n m := by
  let d : ℝ := (n : ℝ) + 1
  have hd : 0 < d := by dsimp [d]; positivity
  have hy : 0 ≤ (y - Blueprint.chamberBase) * d := mul_nonneg (sub_nonneg.mpr hlo) hd.le
  have hy1 : (y - Blueprint.chamberBase) * d < d := by
    have h : y - Blueprint.chamberBase < 1 := by
      dsimp [Blueprint.chamberBase] at *
      linarith
    simpa only [one_mul] using mul_lt_mul_of_pos_right h hd
  let k := ⌊(y - Blueprint.chamberBase) * d⌋₊
  have hk : k < n + 1 := (Nat.floor_lt hy).mpr (by simpa [d] using hy1)
  have hl : (k : ℝ) / d ≤ y - Blueprint.chamberBase :=
    (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using Nat.floor_le hy)
  have hu : y - Blueprint.chamberBase < ((k : ℝ) + 1) / d :=
    (lt_div_iff₀ hd).mpr (by
      simpa only [mul_comm] using (Nat.lt_floor_add_one ((y - Blueprint.chamberBase) * d)))
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · have h : Blueprint.chamberBase + (k : ℝ) / d ≤ y := by linarith
    simpa [chamberBottom, chamberWidth, passageHalfHeight, Blueprint.chamberBase,
      d, div_eq_mul_inv] using h
  · have h : y < Blueprint.chamberBase + ((k : ℝ) + 1) / d := by linarith
    simpa [chamberTop, chamberWidth, passageHalfHeight, Blueprint.chamberBase,
      d, div_eq_mul_inv] using h

theorem mem_chamber_iff_coordinates (p : Blueprint.BlockParameters)
    (i : Blueprint.GateIndex) (j : Bool) (z : ℂ) :
    z ∈ Blueprint.chamber p i j ↔
      Blueprint.blockPosition p i.1 ≤ z.re ∧ z.re ≤ Blueprint.blockPosition p i.1 + 1 ∧
      chamberBottom i.1 i.2 ≤ Blueprint.sideSign j * z.im ∧
      Blueprint.sideSign j * z.im ≤ chamberTop i.1 i.2 := by
  simp [Blueprint.chamber, chamberBottom, chamberTop, chamberWidth, passageHalfHeight,
    Blueprint.chamberBase, div_eq_mul_inv]

theorem left_wall_mem_walls (p : Blueprint.BlockParameters) (n : ℕ) {z : ℂ}
    (hx : z.re = Blueprint.blockPosition p n)
    (hy : Blueprint.chamberBase ≤ |z.im|) (hyhi : |z.im| < Real.pi / 2) :
    z ∈ Blueprint.walls p := by
  obtain ⟨m, hmlo, hmhi⟩ := exists_chamber_height n hy hyhi
  have hsign : ∃ j : Bool, Blueprint.sideSign j * z.im = |z.im| := by
    by_cases h : 0 ≤ z.im
    · exact ⟨true, by simp [Blueprint.sideSign, abs_of_nonneg h]⟩
    · exact ⟨false, by simp [Blueprint.sideSign, abs_of_neg (lt_of_not_ge h)]⟩
  obtain ⟨j, hj⟩ := hsign
  have hz : z ∈ Blueprint.chamber p ⟨n, m⟩ j := by
    rw [mem_chamber_iff_coordinates, hj]
    exact ⟨hx.ge, by linarith, hmlo, hmhi.le⟩
  have hf := mem_frontier_of_left_support (fun w (hw : w ∈ Blueprint.chamber p ⟨n, m⟩ j) => hw.1) hz hx
  exact mem_iUnion.mpr ⟨n, Or.inr (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨j, hf⟩⟩)⟩

theorem left_wall_tract_height (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i) (n : ℕ) {z : ℂ}
    (hz : z ∈ Blueprint.tract p δ) (hx : z.re = Blueprint.blockPosition p n) :
    |z.im| < Blueprint.chamberBase := by
  by_contra hnot
  have hy : Blueprint.chamberBase ≤ |z.im| := le_of_not_gt hnot
  have hw := left_wall_mem_walls p n hx hy (tract_subset_ambient p δ hδ hz).2
  apply left_section_wall_not_mem_tract p δ n ⟨hx.ge, ?_⟩ hy hw hz
  dsimp [Blueprint.slicePosition]
  linarith

theorem passage_horizontal_wall_not_mem_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (n : ℕ) {z : ℂ}
    (hx : Blueprint.blockPosition p n ≤ z.re ∧ z.re ≤ Blueprint.slicePosition p n)
    (hy : |z.im| = Blueprint.chamberBase) : z ∉ Blueprint.tract p δ := by
  have hz : z ∈ Blueprint.passage p n := by
    refine ⟨hx.1, ?_, hy.le⟩
    dsimp [Blueprint.slicePosition] at hx
    linarith [hx.2]
  have hf := mem_frontier_of_abs_im_support
    (fun w (hw : w ∈ Blueprint.passage p n) => hw.2.2) hz hy
  exact left_section_wall_not_mem_tract p δ n hx hy.ge
    (mem_iUnion.mpr ⟨n, Or.inl (Or.inl hf)⟩)

def passageCut (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ) (n : ℕ) : Set ℂ :=
  Blueprint.tract p δ ∩ ({z : ℂ | z.re < Blueprint.blockPosition p n} ∪
    {z : ℂ | z.re < Blueprint.slicePosition p n ∧ |z.im| < Blueprint.chamberBase})

theorem passageCut_isOpen (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (n : ℕ) (hV : IsOpen (Blueprint.tract p δ)) : IsOpen (passageCut p δ n) :=
  hV.inter ((isOpen_lt Complex.continuous_re continuous_const).union
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)))

theorem mem_passageCut_of_re_lt (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (n : ℕ) {z : ℂ} (hz : z ∈ Blueprint.tract p δ) (hx : z.re < Blueprint.blockPosition p n) :
    z ∈ passageCut p δ n := ⟨hz, Or.inl hx⟩

theorem passageCut_isBounded (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i) (n : ℕ) : Bornology.IsBounded (passageCut p δ n) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|Blueprint.slicePosition p n| + 2 + Real.pi / 2, ?_⟩
  intro z hz
  have ha := tract_subset_ambient p δ hδ hz.1
  have hx : z.re < Blueprint.slicePosition p n := by
    rcases hz.2 with h | h
    · change z.re < Blueprint.blockPosition p n at h
      dsimp [Blueprint.slicePosition]
      linarith
    · exact h.1
  have hr : |z.re| ≤ |Blueprint.slicePosition p n| + 2 := abs_le.mpr
    ⟨by linarith [abs_nonneg (Blueprint.slicePosition p n), ha.1],
      by linarith [le_abs_self (Blueprint.slicePosition p n)]⟩
  calc
    ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := congrArg norm (Complex.re_add_im z).symm
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by simp
    _ ≤ _ := by linarith [ha.2]

theorem passageCut_frontier_inside (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i) (n : ℕ)
    (hV : IsOpen (Blueprint.tract p δ)) {z : ℂ}
    (hz : z ∈ frontier (passageCut p δ n)) (hzV : z ∈ Blueprint.tract p δ) :
    z ∈ Blueprint.passageSlice p n := by
  let E : Set ℂ := {w : ℂ | w.re ≤ Blueprint.blockPosition p n} ∪
    {w : ℂ | w.re ≤ Blueprint.slicePosition p n ∧ |w.im| ≤ Blueprint.chamberBase}
  have hE : IsClosed E := (isClosed_le Complex.continuous_re continuous_const).union
    ((isClosed_le Complex.continuous_re continuous_const).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hsub : passageCut p δ n ⊆ E := by
    intro w hw
    change w.re ≤ Blueprint.blockPosition p n ∨
      w.re ≤ Blueprint.slicePosition p n ∧ |w.im| ≤ Blueprint.chamberBase
    rcases hw.2 with h | h
    · exact Or.inl (le_of_lt (show w.re < Blueprint.blockPosition p n from h))
    · exact Or.inr ⟨h.1.le, h.2.le⟩
  have hzE : z ∈ E := by simpa only [hE.closure_eq] using closure_mono hsub hz.1
  have hnot : z ∉ passageCut p δ n := by
    simpa only [(passageCut_isOpen p δ n hV).interior_eq] using hz.2
  have hnotlt : ¬ z.re < Blueprint.blockPosition p n := fun h => hnot ⟨hzV, Or.inl h⟩
  have hlo : Blueprint.blockPosition p n ≤ z.re := le_of_not_gt hnotlt
  rcases hzE with he | he
  · have hx : z.re = Blueprint.blockPosition p n := le_antisymm he hlo
    have hy := left_wall_tract_height p δ hδ n hzV hx
    apply (hnot ⟨hzV, Or.inr ⟨?_, hy⟩⟩).elim
    dsimp [Blueprint.slicePosition]
    linarith
  · have hy : |z.im| < Blueprint.chamberBase := lt_of_le_of_ne he.2 (by
      intro hy
      exact passage_horizontal_wall_not_mem_tract p δ n ⟨hlo, he.1⟩ hy hzV)
    have hx : z.re = Blueprint.slicePosition p n := le_antisymm he.1 (by
      by_contra h
      exact hnot ⟨hzV, Or.inr ⟨lt_of_not_ge h, hy⟩⟩)
    exact ⟨hx, hy⟩

#print axioms tract_subset_ambient
#print axioms left_wall_tract_height
#print axioms passageCut_isBounded
#print axioms passageCut_frontier_inside

end

end MaxModulusPoints.Construction
