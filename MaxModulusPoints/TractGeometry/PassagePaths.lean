module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.BlockPositions
public import MaxModulusPoints.TractGeometry.GapPaths
public import MaxModulusPoints.TractGeometry.RectangleFrontiers
public import MaxModulusPoints.TractGeometry.Walls

/-!
# Vertical paths inside the passages

The interior of each passage avoids all walls. Moving its imaginary coordinate
toward zero gives a path inside the tract to the real axis.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_passage_joined (p : BlockParameters) (δ : GateIndex → ℝ) (n : ℕ) {z : ℂ}
    (hl : blockPosition p n < z.re) (hr : z.re < blockPosition p n + 1 / 2)
    (hy : |z.im| < chamberBase) : JoinedIn (tract p δ) z (z.re : ℂ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  have ha : 1 ≤ a := by
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    have hg := blockPosition_growth p (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero] at hg
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 1 ≤ blockPosition p n
    linarith
  have hb : b < Real.pi / 2 := by dsimp [b, chamberBase]; linarith
  have hinside {w : ℂ} (hwl : a < w.re) (hwr : w.re < a + 1 / 2)
      (hwy : |w.im| < b) : w ∈ tract p δ := by
    refine Or.inl (Or.inl ⟨⟨by linarith, lt_trans hwy hb⟩, ?_⟩)
    intro hw
    have hlocal : w ∈ blockWalls p n :=
      (walls_localization p n (by change a - 1 < w.re; linarith)
        (by change w.re < a + 2; linarith)).mp hw
    rcases abs_lt.mp hwy with ⟨hyl, hyu⟩
    rcases hlocal with (hp | ht) | hc
    · have hrect := rectangle_frontier_bounds a (a + 1 / 2) (-b) b
        (by simpa only [passage, abs_le] using hp)
      rcases hrect.2 with h | h | h | h <;> linarith
    · have hrect := rectangle_frontier_bounds (a + 1 / 2) (a + 1)
        (-(p.tunnelHeight n / 2)) (p.tunnelHeight n / 2)
        (by simpa only [tunnel, abs_le] using ht)
      linarith [hrect.1.1]
    · rcases mem_iUnion.mp hc with ⟨m, hm⟩
      rcases mem_iUnion.mp hm with ⟨j, hj⟩
      have hclosed : IsClosed (chamber p ⟨n, m⟩ j) :=
        (isClosed_le continuous_const Complex.continuous_re).inter
          ((isClosed_le Complex.continuous_re continuous_const).inter
            ((isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)).inter
              (isClosed_le (continuous_const.mul Complex.continuous_im) continuous_const)))
      have hlow : b + (m.val : ℝ) / ((n : ℝ) + 1) ≤ sideSign j * w.im :=
        (hclosed.frontier_subset hj).2.2.1
      have hfrac : 0 ≤ (m.val : ℝ) / ((n : ℝ) + 1) := by positivity
      cases j <;> simp [sideSign] at hlow <;> linarith
  let f : ℝ → ℂ := fun t => ⟨z.re, (1 - t) * z.im⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk ((continuous_const.sub continuous_id).mul continuous_const))
  refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
  · apply Complex.ext <;> simp [f]
  · apply Complex.ext <;> simp [f]
  · rintro w ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have ht1 : 1 - t ≤ 1 := by linarith [ht.1]
    have habs : |(1 - t) * z.im| ≤ |z.im| := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    exact hinside hl hr (lt_of_le_of_lt habs hy)

end MaxModulusPoints.TractGeometry
