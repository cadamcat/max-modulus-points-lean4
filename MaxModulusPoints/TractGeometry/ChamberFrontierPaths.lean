import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.ChamberGridPaths
import MaxModulusPoints.TractGeometry.ChamberRightPaths
import MaxModulusPoints.TractGeometry.ChamberWallPaths
import MaxModulusPoints.TractGeometry.RectangleFrontiers
import MaxModulusPoints.TractGeometry.Symmetry
/-!
# Complement paths from chamber frontiers

Every point of a chamber frontier that remains outside the tract joins
the exterior through a left edge, a right edge, or a horizontal grid wall.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem chamber_frontier_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (i : GateIndex) (j : Bool) {z : ℂ}
    (hfront : z ∈ frontier (chamber p i j)) (hz : z ∉ tract p δ) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  rcases i with ⟨n, m⟩
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let d : ℝ := (n : ℝ) + 1
  let l : ℝ := b + (m.val : ℝ) / d
  let u : ℝ := b + ((m.val : ℝ) + 1) / d
  have hpositive {w : ℂ} (hwfront : w ∈ frontier (chamber p ⟨n, m⟩ true))
      (hw : w ∉ tract p δ) : JoinedIn (tract p δ)ᶜ w (-3 : ℂ) := by
    have hrect : w ∈ frontier {v : ℂ | a ≤ v.re ∧ v.re ≤ a + 1 ∧
        l ≤ v.im ∧ v.im ≤ u} := by
      simpa only [chamber, sideSign, Bool.true_eq, ite_true, one_mul, a, b, d, l, u]
        using hwfront
    obtain ⟨⟨hxl, hxr, hyl, hyu⟩, hside⟩ :=
      rectangle_frontier_bounds a (a + 1) l u hrect
    rcases hside with hleft | hright | hlower | hupper
    · have hd : 0 < d := by
        dsimp only [d]
        exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
      have hfrac : 0 ≤ (m.val : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hd.le
      have hbase : b ≤ w.im := by
        dsimp only [l] at hyl
        linarith
      exact positive_chamber_left_compl_joined p δ hδ n hleft hbase
    · exact positive_chamber_right_compl_joined p δ hδ ⟨n, m⟩ hright hyl hyu hw
    · exact chamber_grid_compl_joined p δ hδ n m.val m.isLt.le true hxl hxr
        (by simpa [sideSign, l, b, d] using hlower)
    · exact chamber_grid_compl_joined p δ hδ n (m.val + 1)
        (Nat.succ_le_of_lt m.isLt) true hxl hxr
        (by simpa [sideSign, u, b, d] using hupper)
  cases j with
  | true => exact hpositive hfront hz
  | false =>
    let e : ℂ ≃ₜ ℂ := Complex.conjCLE.toHomeomorph
    have hc : e ⁻¹' chamber p ⟨n, m⟩ true = chamber p ⟨n, m⟩ false := by
      ext w
      change (star w ∈ chamber p ⟨n, m⟩ true) ↔ w ∈ chamber p ⟨n, m⟩ false
      simp [chamber, sideSign]
    have hstarfront : star z ∈ frontier (chamber p ⟨n, m⟩ true) := by
      change z ∈ e ⁻¹' frontier (chamber p ⟨n, m⟩ true)
      rw [e.preimage_frontier, hc]
      exact hfront
    have hzstar : star z ∉ tract p δ := by
      intro hmem
      apply hz
      simpa only [star_star] using tract_star_mem p δ hmem
    have href : JoinedIn (tract p δ)ᶜ (star z) (-3 : ℂ) := hpositive hstarfront hzstar
    have hconj : Continuous (star : ℂ → ℂ) := Complex.conjCLE.continuous
    have hmap := href.map hconj.continuousOn
    have hback : JoinedIn (tract p δ)ᶜ (star (star z)) (star (-3 : ℂ)) := hmap.mono (by
      rintro w ⟨v, hv, rfl⟩ hmem
      apply hv
      simpa only [star_star] using tract_star_mem p δ hmem)
    simpa [Complex.star_def] using hback

end MaxModulusPoints.TractGeometry
