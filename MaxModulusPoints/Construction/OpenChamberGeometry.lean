import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Construction.StarredSegments
import MaxModulusPoints.Construction.StripClearance
import MaxModulusPoints.Construction.Tract
import MaxModulusPoints.Construction.TractMembership
/-!
# Clearance around fully open chambers

The path in Pardo-Simón–Sixsmith, Proposition 4.1, runs vertically along
the clean slice and then horizontally through the centre of a fully open
gate. Its clearance depends only on the chamber height.
-/

namespace MaxModulusPoints.Construction

open Set Metric Filter

noncomputable section

def upperChamberHeight (i : Blueprint.GateIndex) : ℝ :=
  chamberBottom i.1 i.2 + chamberWidth i.1 / 2

theorem upperChamberHeight_bounds (i : Blueprint.GateIndex) :
    0 < upperChamberHeight i ∧
      upperChamberHeight i + chamberWidth i.1 / 2 ≤ Real.pi / 2 := by
  have hb := chamber_bounds i.1 i.2
  have hw := chamberWidth_pos i.1
  have hp := passageHalfHeight_pos
  dsimp [upperChamberHeight, chamberBottom, chamberTop] at *
  constructor <;> linarith

theorem upperChamberHeight_gate_center (i : Blueprint.GateIndex) :
    upperChamberHeight i = Blueprint.chamberBase +
      (2 * (i.2.val : ℝ) + 1) / (2 * ((i.1 : ℝ) + 1)) := by
  simp only [upperChamberHeight, chamberBottom, chamberWidth, passageHalfHeight,
    Blueprint.chamberBase, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem gateUpper_eq_chamberWidth (i : Blueprint.GateIndex) :
    Blueprint.gateUpper i = chamberWidth i.1 := by
  simp [Blueprint.gateUpper, chamberWidth]

theorem chamber_frontier_coordinates (p : Blueprint.BlockParameters)
    (i : Blueprint.GateIndex) (j : Bool) {z : ℂ}
    (hz : z ∈ frontier (Blueprint.chamber p i j)) :
    Blueprint.blockPosition p i.1 ≤ z.re ∧ z.re ≤ Blueprint.blockPosition p i.1 + 1 ∧
      chamberBottom i.1 i.2 ≤ Blueprint.sideSign j * z.im ∧
      Blueprint.sideSign j * z.im ≤ chamberTop i.1 i.2 ∧
      (z.re = Blueprint.blockPosition p i.1 ∨ z.re = Blueprint.blockPosition p i.1 + 1 ∨
        Blueprint.sideSign j * z.im = chamberBottom i.1 i.2 ∨
        Blueprint.sideSign j * z.im = chamberTop i.1 i.2) := by
  have heq : Blueprint.chamber p i j = {w : ℂ |
      Blueprint.blockPosition p i.1 ≤ w.re ∧ w.re ≤ Blueprint.blockPosition p i.1 + 1 ∧
      chamberBottom i.1 i.2 ≤ Blueprint.sideSign j * w.im ∧
      Blueprint.sideSign j * w.im ≤ chamberTop i.1 i.2} := by
    simp [Blueprint.chamber, chamberBottom, chamberTop, chamberWidth,
      passageHalfHeight, Blueprint.chamberBase, div_eq_mul_inv]
  have hc : Continuous (fun w : ℂ => Blueprint.sideSign j * w.im) :=
    continuous_const.mul Complex.continuous_im
  have hclosed : IsClosed (Blueprint.chamber p i j) := by
    rw [heq]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)))
  have hmem := frontier_subset_closure hz
  rw [hclosed.closure_eq, heq] at hmem
  refine ⟨hmem.1, hmem.2.1, hmem.2.2.1, hmem.2.2.2, ?_⟩
  by_contra hside
  push Not at hside
  have hs : Blueprint.blockPosition p i.1 < z.re ∧
      z.re < Blueprint.blockPosition p i.1 + 1 ∧
      chamberBottom i.1 i.2 < Blueprint.sideSign j * z.im ∧
      Blueprint.sideSign j * z.im < chamberTop i.1 i.2 :=
    ⟨lt_of_le_of_ne hmem.1 hside.1.symm,
      lt_of_le_of_ne hmem.2.1 hside.2.1,
      lt_of_le_of_ne hmem.2.2.1 hside.2.2.1.symm,
      lt_of_le_of_ne hmem.2.2.2 hside.2.2.2⟩
  have hopen : IsOpen {w : ℂ | Blueprint.blockPosition p i.1 < w.re ∧
      w.re < Blueprint.blockPosition p i.1 + 1 ∧
      chamberBottom i.1 i.2 < Blueprint.sideSign j * w.im ∧
      Blueprint.sideSign j * w.im < chamberTop i.1 i.2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)))
  apply hz.2
  rw [heq]
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hopen.mem_nhds hs)
    (fun w hw => ⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.le⟩))

/-- In the two-unit region to the right of one block's left wall, only
that block can contribute a wall. -/
theorem wall_block_unique (p : Blueprint.BlockParameters) {n k : ℕ} {z : ℂ}
    (hx : Blueprint.blockPosition p n < z.re ∧ z.re < Blueprint.blockPosition p n + 2)
    (hw : z ∈ frontier (Blueprint.passage p k) ∪ frontier (Blueprint.tunnel p k) ∪
      ⋃ m : Fin (k + 1), ⋃ j : Bool, frontier (Blueprint.chamber p ⟨k, m⟩ j)) : k = n := by
  have hs := block_wall_support p k hw
  rcases lt_trichotomy k n with hkn | hkn | hnk
  · have hm := (blockParametersLayout p).monotone_base (Nat.succ_le_of_lt hkn)
    have hg := (blockParametersLayout p).gap k
    change Blueprint.blockPosition p (k + 1) ≤ Blueprint.blockPosition p n at hm
    change Blueprint.blockPosition p k + 2 ≤ Blueprint.blockPosition p (k + 1) at hg
    linarith [hx.1, hs.2]
  · exact hkn
  · have hm := (blockParametersLayout p).monotone_base (Nat.succ_le_of_lt hnk)
    have hg := (blockParametersLayout p).gap n
    change Blueprint.blockPosition p (n + 1) ≤ Blueprint.blockPosition p k at hm
    change Blueprint.blockPosition p n + 2 ≤ Blueprint.blockPosition p (n + 1) at hg
    linarith [hx.2, hs.1]

/-- The open chamber's full horizontal corridor, including its gate, is
contained in the literal union-of-frontiers tract. -/
theorem open_chamber_corridor_mem (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex)
    (hδ : δ i = Blueprint.gateUpper i) {z : ℂ}
    (hx : Blueprint.blockPosition p i.1 < z.re ∧ z.re < Blueprint.blockPosition p i.1 + 2)
    (hy : chamberBottom i.1 i.2 < z.im ∧ z.im < chamberTop i.1 i.2) :
    z ∈ Blueprint.tract p δ := by
  have hb := chamber_bounds i.1 i.2
  have hpos : 0 < z.im := lt_trans passageHalfHeight_pos (hb.1.trans_lt hy.1)
  by_cases hright : z.re = Blueprint.blockPosition p i.1 + 1
  · apply Or.inr
    refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨true, hright, ?_⟩⟩
    rw [hδ, gateUpper_eq_chamberWidth, ← upperChamberHeight_gate_center]
    simp only [Blueprint.sideSign, ite_true, one_mul]
    apply abs_lt.mpr
    dsimp [upperChamberHeight, chamberBottom, chamberTop] at *
    constructor <;> linarith
  · refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
    · have hp := (blockParametersLayout p).base_nonneg i.1
      change 0 ≤ Blueprint.blockPosition p i.1 at hp
      linarith [hx.1]
    · rw [abs_of_pos hpos]
      exact hy.2.trans_le hb.2.2
    · intro hw
      obtain ⟨k, hk⟩ := mem_iUnion.mp hw
      have hki := wall_block_unique p hx hk
      subst k
      rcases hk with (hp | ht) | hc
      · have h := (frontier_absRectangle_bounds hp).2.2.1
        rw [abs_of_pos hpos] at h
        change z.im ≤ passageHalfHeight at h
        linarith [hb.1, hy.1]
      · have h := (frontier_absRectangle_bounds ht).2.2.1
        rw [abs_of_pos hpos] at h
        have hbase : (1 : ℝ) / 8 < passageHalfHeight := by
          dsimp [passageHalfHeight]
          linarith [Real.pi_gt_three]
        linarith [p.tunnel_le_quarter i.1, hb.1, hy.1]
      · obtain ⟨m, hm⟩ := mem_iUnion.mp hc
        obtain ⟨j, hj⟩ := mem_iUnion.mp hm
        have h := chamber_frontier_coordinates p ⟨i.1, m⟩ j hj
        cases j
        · simp only [Blueprint.sideSign, Bool.false_eq_true, ite_false, neg_mul, one_mul] at h
          linarith [(chamber_bounds i.1 m).1, passageHalfHeight_pos]
        · simp only [Blueprint.sideSign, ite_true, one_mul] at h
          rcases lt_trichotomy m i.2 with hmi | hmi | him
          · linarith [chamberTop_le_bottom hmi, hy.1]
          · subst m
            rcases h.2.2.2.2 with hl | hr | hlo | hhi
            · linarith [hx.1]
            · exact hright hr
            · linarith [hy.1]
            · linarith [hy.2]
          · linarith [chamberTop_le_bottom him, hy.2]

def chamberClearance (n : ℕ) : ℝ := chamberWidth n / 8

theorem chamberClearance_pos (n : ℕ) : 0 < chamberClearance n :=
  div_pos (chamberWidth_pos n) (by norm_num)

theorem chamberWidth_le_one (n : ℕ) : chamberWidth n ≤ 1 := by
  dsimp [chamberWidth]
  exact (div_le_one (by positivity)).mpr (by norm_cast; omega)

/-- A whole clearance ball about any point of the horizontal leg lies in
the tract, independently of all the other gates. -/
theorem horizontal_chamber_clearance (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex)
    (hδ : δ i = Blueprint.gateUpper i) {x : ℝ}
    (hx : x ∈ Icc (Blueprint.blockPosition p i.1 + 1 / 4)
      (Blueprint.blockPosition p i.1 + 3 / 2)) :
    ball (⟨x, upperChamberHeight i⟩ : ℂ) (chamberClearance i.1) ⊆ Blueprint.tract p δ := by
  intro z hz
  have hn : ‖z - (⟨x, upperChamberHeight i⟩ : ℂ)‖ < chamberWidth i.1 / 8 := by
    simpa only [mem_ball, dist_eq_norm, chamberClearance] using hz
  have hr := (Complex.abs_re_le_norm (z - (⟨x, upperChamberHeight i⟩ : ℂ))).trans_lt hn
  have hi := (Complex.abs_im_le_norm (z - (⟨x, upperChamberHeight i⟩ : ℂ))).trans_lt hn
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  have hw := chamberWidth_le_one i.1
  have hwp := chamberWidth_pos i.1
  apply open_chamber_corridor_mem p δ i hδ
  · exact ⟨by linarith [(abs_lt.mp hr).1, hx.1],
      by linarith [(abs_lt.mp hr).2, hx.2]⟩
  · dsimp [upperChamberHeight, chamberBottom, chamberTop] at *
    exact ⟨by linarith [(abs_lt.mp hi).1], by linarith [(abs_lt.mp hi).2]⟩

/-- The clean vertical leg has the same clearance radius, even at the
height of the topmost chamber. -/
theorem vertical_chamber_clearance (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex) {y : ℝ}
    (hy : y ∈ Icc 0 (upperChamberHeight i)) :
    ball (⟨Blueprint.blockPosition p i.1 + 3 / 2, y⟩ : ℂ)
      (chamberClearance i.1) ⊆ Blueprint.tract p δ := by
  intro z hz
  have hn : ‖z - (⟨Blueprint.blockPosition p i.1 + 3 / 2, y⟩ : ℂ)‖ <
      chamberWidth i.1 / 8 := by
    simpa only [mem_ball, dist_eq_norm, chamberClearance] using hz
  have hr := (Complex.abs_re_le_norm
    (z - (⟨Blueprint.blockPosition p i.1 + 3 / 2, y⟩ : ℂ))).trans_lt hn
  have hi := (Complex.abs_im_le_norm
    (z - (⟨Blueprint.blockPosition p i.1 + 3 / 2, y⟩ : ℂ))).trans_lt hn
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  have hw := chamberWidth_le_one i.1
  have hwp := chamberWidth_pos i.1
  have hh := upperChamberHeight_bounds i
  have hx : Blueprint.blockPosition p i.1 + 1 < z.re ∧
      z.re < Blueprint.blockPosition p i.1 + 2 :=
    ⟨by linarith [(abs_lt.mp hr).1], by linarith [(abs_lt.mp hr).2]⟩
  refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
  · have hp := (blockParametersLayout p).base_nonneg i.1
    change 0 ≤ Blueprint.blockPosition p i.1 at hp
    linarith [hx.1]
  · exact abs_lt.mpr ⟨by linarith [(abs_lt.mp hi).1, hy.1, Real.pi_gt_three],
      by linarith [(abs_lt.mp hi).2, hy.2, hh.2]⟩
  · intro hwalls
    obtain ⟨k, hk⟩ := mem_iUnion.mp hwalls
    have hki := wall_block_unique p ⟨by linarith [hx.1], hx.2⟩ hk
    subst k
    linarith [(block_wall_support p i.1 hk).2, hx.1]

#print axioms open_chamber_corridor_mem
#print axioms horizontal_chamber_clearance
#print axioms vertical_chamber_clearance

end

end MaxModulusPoints.Construction
