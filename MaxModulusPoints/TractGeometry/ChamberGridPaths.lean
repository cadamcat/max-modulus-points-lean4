import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.ChamberWallPaths
import MaxModulusPoints.TractGeometry.ExteriorPaths
import MaxModulusPoints.TractGeometry.GateHeights
import MaxModulusPoints.TractGeometry.RectangleFrontiers
import MaxModulusPoints.TractGeometry.RestoredWalls
import MaxModulusPoints.TractGeometry.Symmetry
import MaxModulusPoints.TractGeometry.Walls
/-!
# Paths along the horizontal chamber walls

Every chamber grid segment avoids the restored openings and gates. Horizontal
paths join its points to the left chamber edges and hence to the exterior of
the tract. Conjugation supplies the paths on both sides of the real axis.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem chamber_grid_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n k : ℕ) (hk : k ≤ n + 1) (j : Bool) {z : ℂ}
    (hl : blockPosition p n ≤ z.re) (hr : z.re ≤ blockPosition p n + 1)
    (hy : sideSign j * z.im = chamberBase + (k : ℝ) / ((n : ℝ) + 1)) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let d : ℝ := (n : ℝ) + 1
  let c : ℝ := b + (k : ℝ) / d
  have hd : 0 < d := by
    dsimp only [d]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  have hb : 0 < b := by
    dsimp only [b, chamberBase]
    linarith [Real.pi_gt_three]
  have hfrac : 0 ≤ (k : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hd.le
  have hcbase : b ≤ c := by dsimp only [c]; linarith
  have hcpos : 0 < c := lt_of_lt_of_le hb hcbase
  have htb : p.tunnelHeight n / 2 < b := by
    have ht := p.tunnel_le_quarter n
    dsimp only [b, chamberBase]
    linarith [Real.pi_gt_three]
  have hpositive {w : ℂ} (hwl : a ≤ w.re) (hwr : w.re ≤ a + 1) (hwy : w.im = c) :
      JoinedIn (tract p δ)ᶜ w (-3 : ℂ) := by
    by_cases hkn : k < n + 1
    · let S : Set ℂ := {u | u.re ∈ Icc a (a + 1) ∧ u.im = c}
      have hstep : c ≤ b + ((k : ℝ) + 1) / d := by
        have hdiv := div_le_div_of_nonneg_right
          (show (k : ℝ) ≤ (k : ℝ) + 1 by linarith) hd.le
        dsimp only [c]
        linarith
      have hS : S ⊆ (tract p δ)ᶜ := by
        intro u hu hmem
        have hrect : u ∈ frontier {v : ℂ | a ≤ v.re ∧ v.re ≤ a + 1 ∧
            c ≤ v.im ∧ v.im ≤ b + ((k : ℝ) + 1) / d} :=
          (rectangle_mem_frontier_iff a (a + 1) c (b + ((k : ℝ) + 1) / d)).mpr
            ⟨⟨hu.1.1, hu.1.2, hu.2.ge, hu.2.le.trans hstep⟩,
              Or.inr (Or.inr (Or.inl hu.2))⟩
        have hfront : u ∈ frontier (chamber p ⟨n, ⟨k, hkn⟩⟩ true) := by
          simpa only [chamber, sideSign, Bool.true_eq, ite_true, one_mul, a, b, c, d]
            using hrect
        have hwall : u ∈ blockWalls p n :=
          Or.inr (mem_iUnion.mpr ⟨⟨k, hkn⟩, mem_iUnion.mpr ⟨true, hfront⟩⟩)
        have huabs : |u.im| = c := by rw [hu.2, abs_of_pos hcpos]
        rcases (blockWalls_mem_tract_iff p δ n hwall).mp hmem with hopen | ⟨m, s, hg⟩
        · rcases hopen with ho | ho | ho
          · have hab : |u.im| < b := ho.2
            rw [huabs] at hab
            linarith
          · have hab : |u.im| < p.tunnelHeight n / 2 := ho.2
            rw [huabs] at hab
            linarith
          · have hab : |u.im| < p.tunnelHeight n / 2 := ho.2
            rw [huabs] at hab
            linarith
        · exact (gate_avoids_grid p δ ⟨n, m⟩ s (hδ ⟨n, m⟩) hg k) huabs
      have hconv : Convex ℝ S :=
        ((convex_Icc a (a + 1)).linear_preimage Complex.reLm).inter
          ((convex_singleton c).linear_preimage Complex.imLm)
      let q : ℂ := ⟨a, c⟩
      have hwS : w ∈ S := ⟨⟨hwl, hwr⟩, hwy⟩
      have hqS : q ∈ S := ⟨⟨le_rfl, by change a ≤ a + 1; linarith⟩, rfl⟩
      have hhor : JoinedIn (tract p δ)ᶜ w q :=
        ((hconv.isPathConnected ⟨w, hwS⟩).joinedIn w hwS q hqS).mono hS
      exact hhor.trans (positive_chamber_left_compl_joined p δ hδ n rfl hcbase)
    · have hknEq : k = n + 1 := le_antisymm hk (le_of_not_gt hkn)
      have hncast : (k : ℝ) = d := by
        dsimp only [d]
        exact_mod_cast hknEq
      have htop : c = Real.pi / 2 := by
        dsimp only [c]
        rw [hncast, div_self (ne_of_gt hd)]
        dsimp only [b, chamberBase]
        ring
      exact tract_compl_exterior_joined p δ hδ (Or.inr (by
        rw [hwy, htop]
        exact le_abs_self _))
  cases j with
  | true =>
    exact hpositive hl hr (by simpa [sideSign] using hy)
  | false =>
    have href : JoinedIn (tract p δ)ᶜ (star z) (-3 : ℂ) :=
      hpositive (by simpa only [Complex.star_def, Complex.conj_re] using hl)
        (by simpa only [Complex.star_def, Complex.conj_re] using hr)
        (by simpa [sideSign, Complex.star_def] using hy)
    have hconj : Continuous (star : ℂ → ℂ) := Complex.conjCLE.continuous
    have hmap := href.map hconj.continuousOn
    have hback : JoinedIn (tract p δ)ᶜ (star (star z)) (star (-3 : ℂ)) := hmap.mono (by
      rintro w ⟨v, hv, rfl⟩ hmem
      apply hv
      simpa only [star_star] using tract_star_mem p δ hmem)
    simpa [Complex.star_def] using hback

end MaxModulusPoints.TractGeometry
