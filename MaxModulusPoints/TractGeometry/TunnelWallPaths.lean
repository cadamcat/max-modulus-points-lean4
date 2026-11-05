module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.GateHeights
public import MaxModulusPoints.TractGeometry.PassageWallPaths
public import MaxModulusPoints.TractGeometry.RectangleFrontiers
public import MaxModulusPoints.TractGeometry.RestoredWalls
public import MaxModulusPoints.TractGeometry.Walls

/-!
# Complement paths from tunnel frontiers

The portions of a tunnel frontier outside the tract lie on its horizontal
walls. Those walls join the passage's right wall at their left endpoints.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tunnel_frontier_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ) {z : ℂ}
    (hfront : z ∈ frontier (tunnel p n)) (hz : z ∉ tract p δ) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let t : ℝ := p.tunnelHeight n / 2
  have ht : 0 < t := div_pos (p.tunnel_pos n) (by norm_num)
  have htb : t < b := by
    have hbound := p.tunnel_le_quarter n
    dsimp only [t, b, chamberBase]
    linarith [Real.pi_gt_three]
  have hhor {w : ℂ} (hwl : a + 1 / 2 ≤ w.re) (hwr : w.re ≤ a + 1)
      (hwy : |w.im| = t) : JoinedIn (tract p δ)ᶜ w (-3 : ℂ) := by
    let S : Set ℂ := {u | u.re ∈ Icc (a + 1 / 2) (a + 1) ∧ u.im = w.im}
    have hS : S ⊆ (tract p δ)ᶜ := by
      intro u hu hmem
      have hyu : |u.im| = t := by rw [hu.2]; exact hwy
      have huy := abs_le.mp hyu.le
      have hside : u.im = -t ∨ u.im = t := by
        by_cases hnonneg : 0 ≤ u.im
        · exact Or.inr (by simpa only [abs_of_nonneg hnonneg] using hyu)
        · have hnonpos : u.im ≤ 0 := le_of_not_ge hnonneg
          rw [abs_of_nonpos hnonpos] at hyu
          exact Or.inl (by linarith)
      have hrect : u ∈ frontier {v : ℂ | a + 1 / 2 ≤ v.re ∧ v.re ≤ a + 1 ∧
          -t ≤ v.im ∧ v.im ≤ t} :=
        (rectangle_mem_frontier_iff (a + 1 / 2) (a + 1) (-t) t).mpr
          ⟨⟨hu.1.1, hu.1.2, huy.1, huy.2⟩,
            Or.inr (Or.inr hside)⟩
      have hutunnel : u ∈ frontier (tunnel p n) := by
        simpa only [tunnel, abs_le, a, t] using hrect
      have hwall : u ∈ blockWalls p n := Or.inl (Or.inr hutunnel)
      rcases (blockWalls_mem_tract_iff p δ n hwall).mp hmem with hopen | ⟨k, j, hg⟩
      · rcases hopen with ho | ho | ho
        · have hre : u.re = a := ho.1
          linarith [hu.1.1]
        · have hheight : |u.im| < t := ho.2
          rw [hyu] at hheight
          exact (lt_irrefl t) hheight
        · have hheight : |u.im| < t := ho.2
          rw [hyu] at hheight
          exact (lt_irrefl t) hheight
      · have hglo := (gate_height_bounds p δ ⟨n, k⟩ j (hδ ⟨n, k⟩) hg).1
        change b + (k.val : ℝ) / ((n : ℝ) + 1) < sideSign j * u.im at hglo
        have hfrac : 0 ≤ (k.val : ℝ) / ((n : ℝ) + 1) :=
          div_nonneg (Nat.cast_nonneg _)
            (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one).le
        have hsign : sideSign j * u.im ≤ |u.im| := by
          cases j with
          | false => simpa [sideSign] using neg_le_abs u.im
          | true => simpa [sideSign] using le_abs_self u.im
        rw [hyu] at hsign
        linarith
    have hconv : Convex ℝ S :=
      ((convex_Icc (a + 1 / 2) (a + 1)).linear_preimage Complex.reLm).inter
        ((convex_singleton w.im).linear_preimage Complex.imLm)
    let q : ℂ := ⟨a + 1 / 2, w.im⟩
    have hwS : w ∈ S := ⟨⟨hwl, hwr⟩, rfl⟩
    have hqS : q ∈ S := ⟨⟨le_rfl, by change a + 1 / 2 ≤ a + 1; linarith⟩, rfl⟩
    have hpath : JoinedIn (tract p δ)ᶜ w q :=
      ((hconv.isPathConnected ⟨w, hwS⟩).joinedIn w hwS q hqS).mono hS
    have hpassage : JoinedIn (tract p δ)ᶜ q (-3 : ℂ) :=
      passage_right_compl_joined p δ hδ n rfl hwy.ge (hwy.le.trans htb.le)
    exact hpath.trans hpassage
  have hrect : z ∈ frontier {w : ℂ | a + 1 / 2 ≤ w.re ∧ w.re ≤ a + 1 ∧
      -t ≤ w.im ∧ w.im ≤ t} := by
    simpa only [tunnel, abs_le, a, t] using hfront
  obtain ⟨⟨hxl, hxr, hyl, hyu⟩, hside⟩ :=
    rectangle_frontier_bounds (a + 1 / 2) (a + 1) (-t) t hrect
  have habs : |z.im| ≤ t := abs_le.mpr ⟨hyl, hyu⟩
  have hheight : |z.im| = t := by
    apply le_antisymm habs
    apply le_of_not_gt
    intro hlt
    rcases hside with hleft | hright | hlower | hupper
    · apply hz
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, Or.inr (Or.inl ⟨hleft, hlt⟩)⟩))
    · apply hz
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, Or.inr (Or.inr ⟨hright, hlt⟩)⟩))
    · rw [hlower, abs_neg, abs_of_pos ht] at hlt
      exact (lt_irrefl t) hlt
    · rw [hupper, abs_of_pos ht] at hlt
      exact (lt_irrefl t) hlt
  exact hhor hxl hxr hheight

end MaxModulusPoints.TractGeometry
