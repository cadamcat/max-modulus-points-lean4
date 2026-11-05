module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Construction.ClosedChamberGeometry
public import MaxModulusPoints.Construction.OpenChamberGeometry
public import MaxModulusPoints.Construction.PassageCut
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# Fixed rectangular windows around slice endpoints

The endpoint half-discs in Pardo-Simón–Sixsmith, Proposition 4.4, fit
inside passage or chamber rectangles. Their diameters lie on horizontal
walls which no admissible gate restores.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set

noncomputable section

/-- A fixed rectangle near a sample line, with its two horizontal sides
removed from every admissible tract. -/
structure SliceWindow (p : Blueprint.BlockParameters) (n : ℕ) (a b : ℝ) : Prop where
  height_pos : a < b
  inside : ∀ (δ : Blueprint.GateIndex → ℝ) (_G : Blueprint.LogModel (Blueprint.tract p δ)),
    ∀ z : ℂ, |z.re - Blueprint.slicePosition p n| < 1 / 8 → a < z.im → z.im < b →
      z ∈ Blueprint.tract p δ
  wall : ∀ (δ : Blueprint.GateIndex → ℝ), (∀ i, δ i ≤ Blueprint.gateUpper i) →
    ∀ _G : Blueprint.LogModel (Blueprint.tract p δ),
    ∀ z : ℂ, |z.re - Blueprint.slicePosition p n| < 1 / 8 →
      (z.im = a ∨ z.im = b) → z ∉ Blueprint.tract p δ

theorem SliceWindow.reflect {p : Blueprint.BlockParameters} {n : ℕ} {a b : ℝ}
    (W : SliceWindow p n a b) : SliceWindow p n (-b) (-a) where
  height_pos := neg_lt_neg W.height_pos
  inside := by
    intro δ G z hx hlo hhi
    have hz := W.inside δ G (star z) (by simpa using hx)
      (by simpa using neg_lt_neg hhi) (by simpa using neg_lt_neg hlo)
    simpa using G.symmetric_domain (star z) hz
  wall := by
    intro δ hδ G z hx hy hz
    apply W.wall δ hδ G (star z) (by simpa using hx) ?_ (G.symmetric_domain z hz)
    rcases hy with hy | hy
    · exact Or.inr (by simp [hy])
    · exact Or.inl (by simp [hy])

theorem upper_chamber_horizontal_wall_not_mem (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (hδ : ∀ k, δ k ≤ Blueprint.gateUpper k)
    (i : Blueprint.GateIndex) {z : ℂ}
    (hx : |z.re - Blueprint.slicePosition p i.1| < 1 / 8)
    (hy : z.im = chamberBottom i.1 i.2 ∨ z.im = chamberTop i.1 i.2) :
    z ∉ Blueprint.tract p δ := by
  have hx' := abs_lt.mp hx
  dsimp [Blueprint.slicePosition] at hx'
  have hcoord : Blueprint.blockPosition p i.1 < z.re ∧
      z.re < Blueprint.blockPosition p i.1 + 1 := ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hfront : z ∈ frontier (Blueprint.chamber p i true) := by
    refine ⟨subset_closure ?_, ?_⟩
    · rw [mem_chamber_iff_coordinates]
      simp only [Blueprint.sideSign, ite_true, one_mul]
      rcases hy with hy | hy
      · exact ⟨hcoord.1.le, hcoord.2.le, hy.ge, by linarith [(chamber_bounds i.1 i.2).2.1]⟩
      · exact ⟨hcoord.1.le, hcoord.2.le, by linarith [(chamber_bounds i.1 i.2).2.1], hy.le⟩
    · rw [upper_chamber_interior]
      intro hin
      rcases hy with hy | hy <;> linarith [hin.2.2.1, hin.2.2.2]
  apply upper_chamber_frontier_not_mem_tract p δ hδ i hfront
  intro hg
  linarith [hg.1]

theorem upperChamberWindow (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) :
    SliceWindow p i.1 (chamberBottom i.1 i.2) (chamberTop i.1 i.2) where
  height_pos := (chamber_bounds i.1 i.2).2.1
  inside := by
    intro δ G z hx hlo hhi
    apply upper_chamber_interior_subset_tract p δ i
    rw [upper_chamber_interior]
    have hx' := abs_lt.mp hx
    dsimp [Blueprint.slicePosition] at hx'
    exact ⟨by linarith [hx'.1], by linarith [hx'.2], hlo, hhi⟩
  wall := by
    intro δ hδ G z hx hy
    exact upper_chamber_horizontal_wall_not_mem p δ hδ i hx hy

theorem passage_window_mem_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (n : ℕ) {z : ℂ}
    (hx : |z.re - Blueprint.slicePosition p n| < 1 / 8)
    (hy : |z.im| < Blueprint.chamberBase) : z ∈ Blueprint.tract p δ := by
  have hx' := abs_lt.mp hx
  dsimp [Blueprint.slicePosition] at hx'
  have hpos := (blockParametersLayout p).base_nonneg n
  change 0 ≤ Blueprint.blockPosition p n at hpos
  refine Or.inl (Or.inl ⟨⟨by linarith [hx'.1], ?_⟩, ?_⟩)
  · exact hy.trans (by dsimp [Blueprint.chamberBase]; linarith)
  · intro hw
    obtain ⟨k, hk⟩ := mem_iUnion.mp hw
    have hkn := wall_block_unique p ⟨by linarith [hx'.1], by linarith [hx'.2]⟩ hk
    subst k
    rcases hk with (hp | ht) | hc
    · have h := frontier_absRectangle_bounds hp
      rcases h.2.2.2 with h | h | h <;> linarith [hx'.1, hx'.2]
    · have h := frontier_absRectangle_bounds ht
      linarith [h.1, hx'.2]
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hc
      obtain ⟨j, hj⟩ := mem_iUnion.mp hm
      linarith [(chamber_frontier_bounds p ⟨n, m⟩ j hj).2.2]

theorem passageWindow (p : Blueprint.BlockParameters) (n : ℕ) :
    SliceWindow p n (-passageHalfHeight) passageHalfHeight where
  height_pos := by linarith [passageHalfHeight_pos]
  inside := by
    intro δ G z hx hlo hhi
    exact passage_window_mem_tract p δ n hx (abs_lt.mpr ⟨hlo, hhi⟩)
  wall := by
    intro δ hδ G z hx hy
    have hupper (w : ℂ) (hwx : |w.re - Blueprint.slicePosition p n| < 1 / 8)
        (hwy : w.im = passageHalfHeight) : w ∉ Blueprint.tract p δ := by
      apply upper_chamber_horizontal_wall_not_mem p δ hδ ⟨n, 0⟩ hwx
      exact Or.inl (by simpa [chamberBottom] using hwy)
    rcases hy with hy | hy
    · intro hz
      exact hupper (star z) (by simpa using hx) (by simp [hy]) (G.symmetric_domain z hz)
    · exact hupper z hx hy

/-- Each full slice has a fixed window, including the reflected chambers. -/
theorem fullSliceWindow (p : Blueprint.BlockParameters) (n : ℕ) (i : SliceIndex n) :
    SliceWindow p n (sliceBottom n i) (sliceTop n i) := by
  rcases i with _ | ⟨s, m⟩
  · exact passageWindow p n
  · cases s
    · exact upperChamberWindow p ⟨n, m⟩
    · exact (upperChamberWindow p ⟨n, m⟩).reflect

#print axioms upper_chamber_horizontal_wall_not_mem
#print axioms passage_window_mem_tract
#print axioms fullSliceWindow

end

end MaxModulusPoints.Construction
