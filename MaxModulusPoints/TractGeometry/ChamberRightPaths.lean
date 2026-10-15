import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.ChamberGridPaths
import MaxModulusPoints.TractGeometry.ChamberRightWalls
import MaxModulusPoints.TractGeometry.Symmetry
/-!
# Complement paths on chamber right edges

A point on a chamber's right edge outside its gate can move vertically
away from the gate center to a horizontal grid wall. That wall joins the
point to the exterior of the tract.
Conjugation gives the corresponding paths in negative chambers.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem positive_chamber_right_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (i : GateIndex) {z : ℂ}
    (hx : z.re = blockPosition p i.1 + 1)
    (hl : chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) ≤ z.im)
    (hu : z.im ≤ chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1))
    (hz : z ∉ tract p δ) : JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  rcases i with ⟨n, m⟩
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let d : ℝ := (n : ℝ) + 1
  let l : ℝ := b + (m.val : ℝ) / d
  let u : ℝ := b + ((m.val : ℝ) + 1) / d
  let c : ℝ := b + (2 * (m.val : ℝ) + 1) / (2 * d)
  change z.re = a + 1 at hx
  change l ≤ z.im at hl
  change z.im ≤ u at hu
  have hnotgate : z ∉ gate p δ ⟨n, m⟩ true := by
    intro hg
    exact hz ((positive_chamber_right_mem_tract_iff p δ hδ ⟨n, m⟩ hx hl hu).mpr hg)
  have hdist : δ ⟨n, m⟩ / 2 ≤ |z.im - c| := by
    apply le_of_not_gt
    intro h
    apply hnotgate
    exact ⟨hx, by simpa only [sideSign, Bool.true_eq, ite_true, one_mul, b, c, d] using h⟩
  by_cases hzc : z.im ≤ c
  · let S : Set ℂ := {w | w.re = a + 1 ∧ w.im ∈ Icc l z.im}
    have hS : S ⊆ (tract p δ)ᶜ := by
      intro w hw hmem
      have hg := (positive_chamber_right_mem_tract_iff p δ hδ ⟨n, m⟩
        hw.1 hw.2.1 (hw.2.2.trans hu)).mp hmem
      have hgate : |w.im - c| < δ ⟨n, m⟩ / 2 := by
        simpa only [sideSign, Bool.true_eq, ite_true, one_mul, b, c, d] using hg.2
      have hwdist : w.im ≤ c := hw.2.2.trans hzc
      rw [abs_of_nonpos (sub_nonpos.mpr hwdist)] at hgate
      rw [abs_of_nonpos (sub_nonpos.mpr hzc)] at hdist
      linarith [hw.2.2]
    have hconv : Convex ℝ S :=
      ((convex_singleton (a + 1)).linear_preimage Complex.reLm).inter
        ((convex_Icc l z.im).linear_preimage Complex.imLm)
    let q : ℂ := ⟨a + 1, l⟩
    have hzS : z ∈ S := ⟨hx, hl, le_rfl⟩
    have hqS : q ∈ S := ⟨rfl, le_rfl, hl⟩
    have hvert : JoinedIn (tract p δ)ᶜ z q :=
      ((hconv.isPathConnected ⟨z, hzS⟩).joinedIn z hzS q hqS).mono hS
    have hgrid : JoinedIn (tract p δ)ᶜ q (-3 : ℂ) :=
      chamber_grid_compl_joined p δ hδ n m.val m.isLt.le true
        (by change a ≤ a + 1; linarith) (by exact le_rfl)
        (by simp [q, l, b, d, sideSign])
    exact hvert.trans hgrid
  · have hcz : c ≤ z.im := le_of_not_ge hzc
    let S : Set ℂ := {w | w.re = a + 1 ∧ w.im ∈ Icc z.im u}
    have hS : S ⊆ (tract p δ)ᶜ := by
      intro w hw hmem
      have hg := (positive_chamber_right_mem_tract_iff p δ hδ ⟨n, m⟩
        hw.1 (hl.trans hw.2.1) hw.2.2).mp hmem
      have hgate : |w.im - c| < δ ⟨n, m⟩ / 2 := by
        simpa only [sideSign, Bool.true_eq, ite_true, one_mul, b, c, d] using hg.2
      have hwdist : c ≤ w.im := hcz.trans hw.2.1
      rw [abs_of_nonneg (sub_nonneg.mpr hwdist)] at hgate
      rw [abs_of_nonneg (sub_nonneg.mpr hcz)] at hdist
      linarith [hw.2.1]
    have hconv : Convex ℝ S :=
      ((convex_singleton (a + 1)).linear_preimage Complex.reLm).inter
        ((convex_Icc z.im u).linear_preimage Complex.imLm)
    let q : ℂ := ⟨a + 1, u⟩
    have hzS : z ∈ S := ⟨hx, le_rfl, hu⟩
    have hqS : q ∈ S := ⟨rfl, hu, le_rfl⟩
    have hvert : JoinedIn (tract p δ)ᶜ z q :=
      ((hconv.isPathConnected ⟨z, hzS⟩).joinedIn z hzS q hqS).mono hS
    have hgrid : JoinedIn (tract p δ)ᶜ q (-3 : ℂ) :=
      chamber_grid_compl_joined p δ hδ n (m.val + 1) (Nat.succ_le_of_lt m.isLt) true
        (by change a ≤ a + 1; linarith) (by exact le_rfl)
        (by simp [q, u, b, d, sideSign])
    exact hvert.trans hgrid

theorem chamber_right_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (i : GateIndex) (j : Bool) {z : ℂ}
    (hx : z.re = blockPosition p i.1 + 1)
    (hl : chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) ≤ sideSign j * z.im)
    (hu : sideSign j * z.im ≤
      chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1))
    (hz : z ∉ tract p δ) : JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  cases j with
  | true =>
    exact positive_chamber_right_compl_joined p δ hδ i hx
      (by simpa [sideSign] using hl) (by simpa [sideSign] using hu) hz
  | false =>
    have hzstar : star z ∉ tract p δ := by
      intro hmem
      apply hz
      simpa only [star_star] using tract_star_mem p δ hmem
    have href : JoinedIn (tract p δ)ᶜ (star z) (-3 : ℂ) :=
      positive_chamber_right_compl_joined p δ hδ i
        (by simpa only [Complex.star_def, Complex.conj_re] using hx)
        (by simpa [sideSign, Complex.star_def] using hl)
        (by simpa [sideSign, Complex.star_def] using hu) hzstar
    have hconj : Continuous (star : ℂ → ℂ) := Complex.conjCLE.continuous
    have hmap := href.map hconj.continuousOn
    have hback : JoinedIn (tract p δ)ᶜ (star (star z)) (star (-3 : ℂ)) := hmap.mono (by
      rintro w ⟨v, hv, rfl⟩ hmem
      apply hv
      simpa only [star_star] using tract_star_mem p δ hmem)
    simpa [Complex.star_def] using hback

end MaxModulusPoints.TractGeometry
