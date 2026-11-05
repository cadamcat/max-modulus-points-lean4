module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.GateHeights
public import MaxModulusPoints.TractGeometry.RectangleFrontiers
public import MaxModulusPoints.TractGeometry.RestoredWalls
public import MaxModulusPoints.TractGeometry.Walls

/-!
# The restored part of a chamber's right edge

On each positive chamber's closed right edge, the only tract points are
those in that chamber's own gate. Gates in other layers lie strictly
outside the chamber's height interval.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem positive_chamber_right_mem_tract_iff (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (i : GateIndex) {z : ℂ}
    (hx : z.re = blockPosition p i.1 + 1)
    (hl : chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) ≤ z.im)
    (hu : z.im ≤ chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1)) :
    z ∈ tract p δ ↔ z ∈ gate p δ i true := by
  rcases i with ⟨n, m⟩
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let d : ℝ := (n : ℝ) + 1
  change z.re = a + 1 at hx
  change b + (m.val : ℝ) / d ≤ z.im at hl
  change z.im ≤ b + ((m.val : ℝ) + 1) / d at hu
  have hd : 0 < d := by
    dsimp only [d]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  have hb : 0 < b := by
    dsimp only [b, chamberBase]
    linarith [Real.pi_gt_three]
  have htb : p.tunnelHeight n / 2 < b := by
    have ht := p.tunnel_le_quarter n
    dsimp only [b, chamberBase]
    linarith [Real.pi_gt_three]
  have hmdiv : 0 ≤ (m.val : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hd.le
  have hbase : b ≤ z.im := by linarith
  have habs : b ≤ |z.im| := hbase.trans (le_abs_self _)
  have hrect : z ∈ frontier {w : ℂ | a ≤ w.re ∧ w.re ≤ a + 1 ∧
      b + (m.val : ℝ) / d ≤ w.im ∧ w.im ≤ b + ((m.val : ℝ) + 1) / d} :=
    (rectangle_mem_frontier_iff a (a + 1) (b + (m.val : ℝ) / d)
      (b + ((m.val : ℝ) + 1) / d)).mpr
        ⟨⟨by linarith, hx.le, hl, hu⟩, Or.inr (Or.inl hx)⟩
  have hfront : z ∈ frontier (chamber p ⟨n, m⟩ true) := by
    simpa only [chamber, sideSign, Bool.true_eq, ite_true, one_mul, a, b, d]
      using hrect
  have hwall : z ∈ blockWalls p n :=
    Or.inr (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨true, hfront⟩⟩)
  constructor
  · intro hmem
    rcases (blockWalls_mem_tract_iff p δ n hwall).mp hmem with hopen | ⟨k, j, hg⟩
    · rcases hopen with ho | ho | ho
      · have h : |z.im| < b := ho.2
        linarith
      · have h : |z.im| < p.tunnelHeight n / 2 := ho.2
        linarith
      · have h : |z.im| < p.tunnelHeight n / 2 := ho.2
        linarith
    · have hheight := gate_height_bounds p δ ⟨n, k⟩ j (hδ ⟨n, k⟩) hg
      cases j with
      | false =>
        have hglo : b + (k.val : ℝ) / d < -z.im := by
          simpa [sideSign, b, d] using hheight.1
        have hkdiv : 0 ≤ (k.val : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hd.le
        exfalso
        linarith
      | true =>
        have hglo : b + (k.val : ℝ) / d < z.im := by
          simpa only [sideSign, Bool.true_eq, ite_true, one_mul, b, d]
            using hheight.1
        have hghi : z.im < b + ((k.val : ℝ) + 1) / d := by
          simpa only [sideSign, Bool.true_eq, ite_true, one_mul, b, d]
            using hheight.2
        rcases lt_trichotomy k.val m.val with hkm | hkm | hmk
        · have hcast : (k.val : ℝ) + 1 ≤ (m.val : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hkm
          have hdiv := div_le_div_of_nonneg_right hcast hd.le
          exfalso
          linarith
        · have heq : k = m := Fin.ext hkm
          subst k
          exact hg
        · have hcast : (m.val : ℝ) + 1 ≤ (k.val : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hmk
          have hdiv := div_le_div_of_nonneg_right hcast hd.le
          exfalso
          linarith
  · intro hg
    exact Or.inr (mem_iUnion.mpr ⟨⟨n, m⟩, mem_iUnion.mpr ⟨true, hg⟩⟩)

end MaxModulusPoints.TractGeometry
