module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.ChamberFrontierPaths
public import MaxModulusPoints.TractGeometry.ChamberGridPaths
public import MaxModulusPoints.TractGeometry.RectangleFrontiers
public import MaxModulusPoints.TractGeometry.RestoredWalls
public import MaxModulusPoints.TractGeometry.Symmetry
public import MaxModulusPoints.TractGeometry.Walls

/-!
# Complement paths along passage walls

Above and below the central opening, the right wall of a passage joins
vertically to the chamber grid and hence to the exterior of the tract.
Every other frontier point outside the tract lies on the base grid.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem passage_right_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ) {z : ℂ}
    (hx : z.re = blockPosition p n + 1 / 2)
    (hl : p.tunnelHeight n / 2 ≤ |z.im|) (hu : |z.im| ≤ chamberBase) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let t : ℝ := p.tunnelHeight n / 2
  have ht : 0 < t := div_pos (p.tunnel_pos n) (by norm_num)
  have hb : 0 < b := by
    dsimp only [b, chamberBase]
    linarith [Real.pi_gt_three]
  have hpositive {v : ℂ} (hvx : v.re = a + 1 / 2)
      (hvl : t ≤ v.im) (hvu : v.im ≤ b) : JoinedIn (tract p δ)ᶜ v (-3 : ℂ) := by
    let S : Set ℂ := {w | w.re = a + 1 / 2 ∧ w.im ∈ Icc t b}
    have hS : S ⊆ (tract p δ)ᶜ := by
      intro w hw hmem
      have hwy : 0 ≤ w.im := ht.le.trans hw.2.1
      have habs : |w.im| = w.im := abs_of_nonneg hwy
      have hrect : w ∈ frontier {q : ℂ | a ≤ q.re ∧ q.re ≤ a + 1 / 2 ∧
          -b ≤ q.im ∧ q.im ≤ b} :=
        (rectangle_mem_frontier_iff a (a + 1 / 2) (-b) b).mpr
          ⟨⟨by linarith [hw.1], hw.1.le, by linarith, hw.2.2⟩,
            Or.inr (Or.inl hw.1)⟩
      have hfront : w ∈ frontier (passage p n) := by
        simpa only [passage, abs_le, a, b] using hrect
      have hwall : w ∈ blockWalls p n := Or.inl (Or.inl hfront)
      rcases (blockWalls_mem_tract_iff p δ n hwall).mp hmem with hopen | ⟨k, j, hg⟩
      · rcases hopen with ho | ho | ho
        · have hre : w.re = a := ho.1
          linarith [hw.1]
        · have hheight : |w.im| < t := ho.2
          rw [habs] at hheight
          linarith [hw.2.1]
        · have hre : w.re = a + 1 := ho.1
          linarith [hw.1]
      · have hre : w.re = a + 1 := hg.1
        linarith [hw.1]
    have hconv : Convex ℝ S :=
      ((convex_singleton (a + 1 / 2)).linear_preimage Complex.reLm).inter
        ((convex_Icc t b).linear_preimage Complex.imLm)
    let q : ℂ := ⟨a + 1 / 2, b⟩
    have hvS : v ∈ S := ⟨hvx, hvl, hvu⟩
    have hqS : q ∈ S := ⟨rfl, hvl.trans hvu, le_rfl⟩
    have hvert : JoinedIn (tract p δ)ᶜ v q :=
      ((hconv.isPathConnected ⟨v, hvS⟩).joinedIn v hvS q hqS).mono hS
    have hgrid : JoinedIn (tract p δ)ᶜ q (-3 : ℂ) :=
      chamber_grid_compl_joined p δ hδ n 0 (Nat.zero_le _) true
        (by change a ≤ a + 1 / 2; linarith)
        (by change a + 1 / 2 ≤ a + 1; linarith)
        (by simp [q, b, sideSign])
    exact hvert.trans hgrid
  by_cases hznonneg : 0 ≤ z.im
  · exact hpositive hx (by simpa only [abs_of_nonneg hznonneg] using hl)
      (by simpa only [abs_of_nonneg hznonneg] using hu)
  · have hznonpos : z.im ≤ 0 := le_of_not_ge hznonneg
    have href : JoinedIn (tract p δ)ᶜ (star z) (-3 : ℂ) :=
      hpositive (by simpa only [Complex.star_def, Complex.conj_re] using hx)
        (by simpa only [Complex.star_def, Complex.conj_im, abs_of_nonpos hznonpos] using hl)
        (by simpa only [Complex.star_def, Complex.conj_im, abs_of_nonpos hznonpos] using hu)
    have hconj : Continuous (star : ℂ → ℂ) := Complex.conjCLE.continuous
    have hmap := href.map hconj.continuousOn
    have hback : JoinedIn (tract p δ)ᶜ (star (star z)) (star (-3 : ℂ)) := hmap.mono (by
      rintro w ⟨v, hv, rfl⟩ hmem
      apply hv
      simpa only [star_star] using tract_star_mem p δ hmem)
    simpa [Complex.star_def] using hback

theorem passage_frontier_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ) {z : ℂ}
    (hfront : z ∈ frontier (passage p n)) (hz : z ∉ tract p δ) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let t : ℝ := p.tunnelHeight n / 2
  have hrect : z ∈ frontier {w : ℂ | a ≤ w.re ∧ w.re ≤ a + 1 / 2 ∧
      -b ≤ w.im ∧ w.im ≤ b} := by
    simpa only [passage, abs_le, a, b] using hfront
  obtain ⟨⟨hxl, hxr, hyl, hyu⟩, hside⟩ :=
    rectangle_frontier_bounds a (a + 1 / 2) (-b) b hrect
  have habs : |z.im| ≤ b := abs_le.mpr ⟨hyl, hyu⟩
  have hgrid (hyabs : |z.im| = b) : JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
    by_cases hnonneg : 0 ≤ z.im
    · exact chamber_grid_compl_joined p δ hδ n 0 (Nat.zero_le _) true hxl
        (by change z.re ≤ a + 1; linarith)
        (by simpa [sideSign, abs_of_nonneg hnonneg, b] using hyabs)
    · have hnonpos : z.im ≤ 0 := le_of_not_ge hnonneg
      exact chamber_grid_compl_joined p δ hδ n 0 (Nat.zero_le _) false hxl
        (by change z.re ≤ a + 1; linarith)
        (by simpa [sideSign, abs_of_nonpos hnonpos, b] using hyabs)
  rcases hside with hleft | hright | hlower | hupper
  · have hnot : ¬ |z.im| < b := by
      intro hlt
      apply hz
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, Or.inl ⟨hleft, hlt⟩⟩))
    exact hgrid (le_antisymm habs (le_of_not_gt hnot))
  · have hlow : t ≤ |z.im| := by
      apply le_of_not_gt
      intro hlt
      apply hz
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, Or.inr (Or.inl ⟨hright, hlt⟩)⟩))
    exact passage_right_compl_joined p δ hδ n hright hlow habs
  · exact chamber_grid_compl_joined p δ hδ n 0 (Nat.zero_le _) false hxl
      (by change z.re ≤ a + 1; linarith)
      (by simp [sideSign, hlower, b])
  · exact chamber_grid_compl_joined p δ hδ n 0 (Nat.zero_le _) true hxl
      (by change z.re ≤ a + 1; linarith)
      (by simp [sideSign, hupper, b])

end MaxModulusPoints.TractGeometry
