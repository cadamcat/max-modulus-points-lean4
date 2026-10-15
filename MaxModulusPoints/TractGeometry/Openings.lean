import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.BlockPositions
import MaxModulusPoints.TractGeometry.RectangleFrontiers
import MaxModulusPoints.TractGeometry.Walls
/-!
# Interior neighborhoods of the passage and tunnel openings

Each restored vertical opening has an open rectangular neighborhood contained
in the tract.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem openings_subset_interior (p : BlockParameters) (δ : GateIndex → ℝ) (n : ℕ) :
    openings p n ⊆ interior (tract p δ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let t : ℝ := p.tunnelHeight n / 2
  have ha : 1 ≤ a := by
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    have hg := blockPosition_growth p (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero] at hg
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 1 ≤ blockPosition p n
    linarith
  have htb : t < b := by
    have ht := p.tunnel_le_quarter n
    have hpi := Real.pi_gt_three
    dsimp [t, b, chamberBase]
    linarith
  let R (x r : ℝ) : Set ℂ :=
    {w | x - 1 / 4 < w.re ∧ w.re < x + 1 / 4 ∧ |w.im| < r}
  let U : Set ℂ := (R a b ∪ R (a + 1 / 2) t) ∪ R (a + 1) t
  have hRopen (x r : ℝ) : IsOpen (R x r) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im.abs continuous_const))
  have hUopen : IsOpen U :=
    ((hRopen a b).union (hRopen (a + 1 / 2) t)).union (hRopen (a + 1) t)
  have hcontains : openings p n ⊆ U := by
    intro z hz
    rcases hz with hz | hz | hz
    · have hx : z.re = a := hz.1
      refine Or.inl (Or.inl ⟨?_, ?_, hz.2⟩) <;> linarith
    · have hx : z.re = a + 1 / 2 := hz.1
      refine Or.inl (Or.inr ⟨?_, ?_, hz.2⟩) <;> linarith
    · have hx : z.re = a + 1 := hz.1
      refine Or.inr ⟨?_, ?_, hz.2⟩ <;> linarith
  have hchamber (m : Fin (n + 1)) (j : Bool) : IsClosed (chamber p ⟨n, m⟩ j) :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)).inter
          (isClosed_le (continuous_const.mul Complex.continuous_im) continuous_const)))
  have hno_chamber {w : ℂ} (hy : |w.im| < b) (m : Fin (n + 1)) (j : Bool)
      (hw : w ∈ frontier (chamber p ⟨n, m⟩ j)) : False := by
    have hm := (hchamber m j).frontier_subset hw
    have hlow : b + (m.val : ℝ) / ((n : ℝ) + 1) ≤ sideSign j * w.im := hm.2.2.1
    have hfrac : 0 ≤ (m.val : ℝ) / ((n : ℝ) + 1) := by positivity
    rcases abs_lt.mp hy with ⟨hyl, hyu⟩
    cases j <;> simp [sideSign] at hlow <;> linarith
  have hsplit {w : ℂ} (hy : |w.im| < b) (hw : w ∈ blockWalls p n) :
      w ∈ frontier (passage p n) ∨ w ∈ frontier (tunnel p n) := by
    rcases hw with (hw | hw) | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · rcases mem_iUnion.mp hw with ⟨m, hm⟩
      rcases mem_iUnion.mp hm with ⟨j, hj⟩
      exact False.elim (hno_chamber hy m j hj)
  have hp {w : ℂ} (hw : w ∈ frontier (passage p n)) :
      (a ≤ w.re ∧ w.re ≤ a + 1 / 2 ∧ -b ≤ w.im ∧ w.im ≤ b) ∧
        (w.re = a ∨ w.re = a + 1 / 2 ∨ w.im = -b ∨ w.im = b) := by
    apply rectangle_frontier_bounds a (a + 1 / 2) (-b) b
    simpa only [passage, abs_le] using hw
  have ht {w : ℂ} (hw : w ∈ frontier (tunnel p n)) :
      (a + 1 / 2 ≤ w.re ∧ w.re ≤ a + 1 ∧ -t ≤ w.im ∧ w.im ≤ t) ∧
        (w.re = a + 1 / 2 ∨ w.re = a + 1 ∨ w.im = -t ∨ w.im = t) := by
    apply rectangle_frontier_bounds (a + 1 / 2) (a + 1) (-t) t
    simpa only [tunnel, abs_le] using hw
  have hUsub : U ⊆ tract p δ := by
    intro w hw
    have hcommon : a - 1 / 4 < w.re ∧ w.re < a + 5 / 4 ∧ |w.im| < b := by
      rcases hw with (hw | hw) | hw
      · rcases hw with ⟨hl, hr, hy⟩
        exact ⟨hl, by linarith, hy⟩
      · rcases hw with ⟨hl, hr, hy⟩
        exact ⟨by linarith, by linarith, lt_trans hy htb⟩
      · rcases hw with ⟨hl, hr, hy⟩
        exact ⟨by linarith, by linarith, lt_trans hy htb⟩
    have hamb : -2 < w.re ∧ |w.im| < Real.pi / 2 := by
      constructor
      · linarith [hcommon.1]
      · have hy := hcommon.2.2
        dsimp [b, chamberBase] at hy
        linarith
    by_cases hwall : w ∈ walls p
    · have hbwall : w ∈ blockWalls p n :=
        (walls_localization p n (by change a - 1 < w.re; linarith [hcommon.1])
          (by change w.re < a + 2; linarith [hcommon.2.1])).mp hwall
      have hs := hsplit hcommon.2.2 hbwall
      have ho : w ∈ openings p n := by
        rcases hw with (hw | hw) | hw
        · have hy := abs_lt.mp hw.2.2
          have hre : w.re = a := by
            rcases hs with hs | hs
            · rcases (hp hs).2 with h | h | h | h <;> linarith [hw.1, hw.2.1]
            · have hx := (ht hs).1.1
              linarith [hw.2.1]
          exact Or.inl ⟨hre, hw.2.2⟩
        · have hy := abs_lt.mp hw.2.2
          have hyb := abs_lt.mp hcommon.2.2
          have hre : w.re = a + 1 / 2 := by
            rcases hs with hs | hs
            · rcases (hp hs).2 with h | h | h | h <;> linarith [hw.1, hw.2.1]
            · rcases (ht hs).2 with h | h | h | h <;> linarith [hw.1, hw.2.1]
          exact Or.inr (Or.inl ⟨hre, hw.2.2⟩)
        · have hy := abs_lt.mp hw.2.2
          have hre : w.re = a + 1 := by
            rcases hs with hs | hs
            · have hx := (hp hs).1.2.1
              linarith [hw.1]
            · rcases (ht hs).2 with h | h | h | h <;> linarith [hw.1, hw.2.1]
          exact Or.inr (Or.inr ⟨hre, hw.2.2⟩)
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, ho⟩))
    · exact Or.inl (Or.inl ⟨hamb, hwall⟩)
  exact hcontains.trans (interior_maximal hUsub hUopen)

end MaxModulusPoints.TractGeometry
