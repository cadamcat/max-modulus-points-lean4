module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.StripCoordinates
public import MaxModulusPoints.Construction.Tract

/-!
# Real-axis and slice membership in the chamber tract

The rectangle frontiers in Pardo-Simón–Sixsmith, §4, leave the real axis
connected through the three passage and tunnel openings. The passage slice
lies inside its rectangle, and the clean slice misses every closed block.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set Filter

noncomputable section

theorem blockPosition_succ (p : Blueprint.BlockParameters) (n : ℕ) :
    Blueprint.blockPosition p (n + 1) = Blueprint.blockPosition p n + p.gap (n + 1) + 1 := by
  simp only [Blueprint.blockPosition, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- The concrete block positions satisfy the separated-layout inequalities. -/
def blockParametersLayout (p : Blueprint.BlockParameters) : BlockLayout where
  base := Blueprint.blockPosition p
  start_nonneg := by
    simpa [Blueprint.blockPosition] using
      (le_trans (show (0 : ℝ) ≤ 1 by norm_num) (p.gap_ge_one 0))
  gap := by
    intro n
    rw [blockPosition_succ]
    linarith [p.gap_ge_one (n + 1)]

theorem frontier_absRectangle_bounds {a b h : ℝ} {z : ℂ}
    (hz : z ∈ frontier {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ |w.im| ≤ h}) :
    a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ h ∧
      (z.re = a ∨ z.re = b ∨ |z.im| = h) := by
  have hclosed : IsClosed {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ |w.im| ≤ h} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hmem : a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ h := by
    simpa [hclosed.closure_eq] using (frontier_subset_closure hz)
  refine ⟨hmem.1, hmem.2.1, hmem.2.2, ?_⟩
  by_contra hside
  have hstrict : a < z.re ∧ z.re < b ∧ |z.im| < h := by
    push Not at hside
    exact ⟨lt_of_le_of_ne hmem.1 hside.1.symm,
      lt_of_le_of_ne hmem.2.1 hside.2.1,
      lt_of_le_of_ne hmem.2.2 hside.2.2⟩
  have hopen : IsOpen {w : ℂ | a < w.re ∧ w.re < b ∧ |w.im| < h} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hinterior : z ∈ interior {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ |w.im| ≤ h} :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (hopen.mem_nhds hstrict)
      (fun w hw => ⟨hw.1.le, hw.2.1.le, hw.2.2.le⟩))
  exact hz.2 hinterior

theorem chamber_frontier_bounds (p : Blueprint.BlockParameters)
    (i : Blueprint.GateIndex) (j : Bool) {z : ℂ}
    (hz : z ∈ frontier (Blueprint.chamber p i j)) :
    Blueprint.blockPosition p i.1 ≤ z.re ∧ z.re ≤ Blueprint.blockPosition p i.1 + 1 ∧
      Blueprint.chamberBase ≤ |z.im| := by
  have hcoord : Continuous (fun w : ℂ => Blueprint.sideSign j * w.im) :=
    continuous_const.mul Complex.continuous_im
  have hclosed : IsClosed (Blueprint.chamber p i j) :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const hcoord).inter (isClosed_le hcoord continuous_const)))
  have hmem : z ∈ Blueprint.chamber p i j := by
    simpa only [hclosed.closure_eq] using (frontier_subset_closure hz)
  refine ⟨hmem.1, hmem.2.1, ?_⟩
  have hnonneg : 0 ≤ (i.2.val : ℝ) / ((i.1 : ℝ) + 1) := by positivity
  have hlower := hmem.2.2.1
  cases j <;> simp only [Blueprint.sideSign, Bool.false_eq_true, ite_false, ite_true,
    neg_mul, one_mul] at hlower
  · linarith [neg_le_abs z.im]
  · linarith [le_abs_self z.im]

theorem block_wall_support (p : Blueprint.BlockParameters) (n : ℕ) {z : ℂ}
    (hz : z ∈ frontier (Blueprint.passage p n) ∪ frontier (Blueprint.tunnel p n) ∪
      ⋃ m : Fin (n + 1), ⋃ j : Bool, frontier (Blueprint.chamber p ⟨n, m⟩ j)) :
    Blueprint.blockPosition p n ≤ z.re ∧ z.re ≤ Blueprint.blockPosition p n + 1 := by
  rcases hz with (hp | ht) | hc
  · have h := frontier_absRectangle_bounds hp
    exact ⟨h.1, by linarith [h.2.1]⟩
  · have h := frontier_absRectangle_bounds ht
    exact ⟨by linarith [h.1], h.2.1⟩
  · obtain ⟨m, hm⟩ := mem_iUnion.mp hc
    obtain ⟨j, hj⟩ := mem_iUnion.mp hm
    have h := chamber_frontier_bounds p ⟨n, m⟩ j hj
    exact ⟨h.1, h.2.1⟩

/-- Every real point on a removed wall is restored by one of the three openings. -/
theorem real_wall_mem_openings (p : Blueprint.BlockParameters) {x : ℝ}
    (hx : (x : ℂ) ∈ Blueprint.walls p) : ∃ n, (x : ℂ) ∈ Blueprint.openings p n := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  have hbase : 0 < Blueprint.chamberBase := passageHalfHeight_pos
  have ht : 0 < p.tunnelHeight n / 2 := half_pos (p.tunnel_pos n)
  refine ⟨n, ?_⟩
  rcases hn with (hp | htunnel) | hc
  · have h := frontier_absRectangle_bounds hp
    rcases h.2.2.2 with ha | hb | hh
    · exact Or.inl ⟨ha, by simpa using hbase⟩
    · exact Or.inr (Or.inl ⟨hb, by simpa using ht⟩)
    · simp only [Complex.ofReal_im, abs_zero] at hh
      linarith
  · have h := frontier_absRectangle_bounds htunnel
    rcases h.2.2.2 with ha | hb | hh
    · exact Or.inr (Or.inl ⟨ha, by simpa using ht⟩)
    · exact Or.inr (Or.inr ⟨hb, by simpa using ht⟩)
    · simp only [Complex.ofReal_im, abs_zero] at hh
      linarith
  · obtain ⟨m, hm⟩ := mem_iUnion.mp hc
    obtain ⟨j, hj⟩ := mem_iUnion.mp hm
    have h := (chamber_frontier_bounds p ⟨n, m⟩ j hj).2.2
    simp only [Complex.ofReal_im, abs_zero] at h
    linarith

theorem real_mem_tract (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    {x : ℝ} (hx : -2 < x) : (x : ℂ) ∈ Blueprint.tract p δ := by
  by_cases hw : (x : ℂ) ∈ Blueprint.walls p
  · obtain ⟨n, hn⟩ := real_wall_mem_openings p hw
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, hn⟩))
  · refine Or.inl (Or.inl ⟨⟨hx, ?_⟩, hw⟩)
    simpa using Real.pi_div_two_pos

/-- The full passage slice is contained in the tract, for every gate family. -/
theorem passageSlice_subset_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (n : ℕ) :
    Blueprint.passageSlice p n ⊆ Blueprint.tract p δ := by
  intro z hz
  have hpos : 0 ≤ Blueprint.blockPosition p n := (blockParametersLayout p).base_nonneg n
  have hx : z.re = Blueprint.blockPosition p n + 1 / 4 := hz.1
  have hy : |z.im| < Blueprint.chamberBase := hz.2
  refine Or.inl (Or.inl ⟨⟨by linarith, ?_⟩, ?_⟩)
  · exact hy.trans (by dsimp [Blueprint.chamberBase]; linarith)
  · intro hw
    obtain ⟨k, hk⟩ := mem_iUnion.mp hw
    by_cases hkn : k = n
    · subst k
      rcases hk with (hp | ht) | hc
      · have h := frontier_absRectangle_bounds hp
        rcases h.2.2.2 with ha | hb | hh <;> linarith
      · have h := frontier_absRectangle_bounds ht
        linarith [h.1]
      · obtain ⟨m, hm⟩ := mem_iUnion.mp hc
        obtain ⟨j, hj⟩ := mem_iUnion.mp hm
        linarith [(chamber_frontier_bounds p ⟨n, m⟩ j hj).2.2]
    · have hsupport := block_wall_support p k hk
      have hout := (blockParametersLayout p).sample_outside (Ne.symm hkn)
      change Blueprint.blockPosition p n + 1 / 4 < Blueprint.blockPosition p k ∨
        Blueprint.blockPosition p k + 1 < Blueprint.blockPosition p n + 1 / 4 at hout
      rcases hout with hleft | hright <;> linarith [hsupport.1, hsupport.2]

theorem cleanSlice_outside_blocks (p : Blueprint.BlockParameters) (n k : ℕ) :
    Blueprint.blockPosition p n + 3 / 2 < Blueprint.blockPosition p k ∨
      Blueprint.blockPosition p k + 1 < Blueprint.blockPosition p n + 3 / 2 := by
  by_cases hkn : k ≤ n
  · right
    have hmono := (blockParametersLayout p).monotone_base hkn
    change Blueprint.blockPosition p k ≤ Blueprint.blockPosition p n at hmono
    linarith
  · left
    have hgap := (blockParametersLayout p).gap n
    have hmono := (blockParametersLayout p).monotone_base
      (Nat.succ_le_of_lt (Nat.lt_of_not_ge hkn))
    change Blueprint.blockPosition p n + 2 ≤ Blueprint.blockPosition p (n + 1) at hgap
    change Blueprint.blockPosition p (n + 1) ≤ Blueprint.blockPosition p k at hmono
    linarith

theorem cleanSlice_subset_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (n : ℕ) :
    Blueprint.cleanSlice p n ⊆ Blueprint.tract p δ := by
  intro z hz
  have hpos : 0 ≤ Blueprint.blockPosition p n := (blockParametersLayout p).base_nonneg n
  have hx : z.re = Blueprint.blockPosition p n + 3 / 2 := hz.1
  refine Or.inl (Or.inl ⟨⟨by linarith, hz.2⟩, ?_⟩)
  intro hw
  obtain ⟨k, hk⟩ := mem_iUnion.mp hw
  have hsupport := block_wall_support p k hk
  rcases cleanSlice_outside_blocks p n k with hleft | hright <;>
    linarith [hsupport.1, hsupport.2]

/-- The tunnel comparison now needs only the declared passage slice; all
domain membership of the passage and clean reference points is proved. -/
theorem passage_bound_at_clean_reference (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ))
    {n : ℕ} {w : ℂ} (hw : w ∈ Blueprint.passageSlice p n)
    {D : ℝ} (hD : 0 ≤ D)
    (hheight : D ≤ 1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi) :
    (G.toFun w).re ≤ Real.exp (-ψ.lowerRate * D) *
      (G.toFun (Blueprint.blockPosition p n + 3 / 2 : ℝ)).re := by
  have href : ((Blueprint.blockPosition p n + 3 / 2 : ℝ) : ℂ) ∈ Blueprint.cleanSlice p n :=
    ⟨rfl, by simpa using Real.pi_div_two_pos⟩
  exact logModel_passage_bound hbottleneck ψ p δ hδ G href
    (cleanSlice_subset_tract p δ n href) hw (passageSlice_subset_tract p δ n hw) hD hheight

#print axioms real_mem_tract
#print axioms passageSlice_subset_tract
#print axioms cleanSlice_subset_tract
#print axioms passage_bound_at_clean_reference

end

end MaxModulusPoints.Construction
