import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.BlockPositions
import MaxModulusPoints.TractGeometry.RectangleFrontiers
import MaxModulusPoints.TractGeometry.StripContainment
import MaxModulusPoints.TractGeometry.Symmetry
import MaxModulusPoints.TractGeometry.Walls
/-!
# Interior neighborhoods of the chamber gates

A gate lies strictly between consecutive horizontal chamber walls. An open
rectangle across its vertical wall is therefore contained in the tract.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem positive_gate_subset_interior (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (i : GateIndex) :
    gate p δ i true ⊆ interior (tract p δ) := by
  let n : ℕ := i.1
  let v : ℝ := i.2.val
  let a : ℝ := blockPosition p n
  let d : ℝ := (n : ℝ) + 1
  let b : ℝ := chamberBase
  let t : ℝ := p.tunnelHeight n / 2
  let c : ℝ := b + (2 * v + 1) / (2 * d)
  have hd : 0 < d := by dsimp [d]; positivity
  have hv : 0 ≤ v := Nat.cast_nonneg _
  have ha : 1 ≤ a := by
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    have hg := blockPosition_growth p (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero] at hg
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 1 ≤ blockPosition p n
    linarith
  have hb : 0 < b := by
    dsimp [b, chamberBase]
    linarith [Real.pi_gt_three]
  have htb : t < b := by
    have ht := p.tunnel_le_quarter n
    dsimp [t, b, chamberBase]
    linarith [Real.pi_gt_three]
  have hδi : δ i ≤ 1 / d := hδ i
  have hhalf : δ i / 2 ≤ 1 / (2 * d) := by
    calc
      δ i / 2 ≤ (1 / d) / 2 := div_le_div_of_nonneg_right hδi (by norm_num)
      _ = 1 / (2 * d) := by field_simp <;> ring
  have hcenterL : c = b + v / d + 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd] <;> ring
  have hcenterU : c = b + (v + 1) / d - 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd] <;> ring
  let U : Set ℂ :=
    {w | a + 3 / 4 < w.re ∧ w.re < a + 5 / 4 ∧ |w.im - c| < δ i / 2}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt (Complex.continuous_im.sub continuous_const).abs continuous_const))
  have hcontains : gate p δ i true ⊆ U := by
    intro z hz
    have hx : z.re = a + 1 := hz.1
    have hy : |z.im - c| < δ i / 2 := by simpa [sideSign] using hz.2
    exact ⟨by linarith, by linarith, hy⟩
  have hlayer {w : ℂ} (hw : w ∈ U) :
      b + v / d < w.im ∧ w.im < b + (v + 1) / d := by
    have hg := abs_lt.mp hw.2.2
    constructor <;> linarith
  have hgrid {w : ℂ} (hw : w ∈ U) (k : ℕ) : w.im ≠ b + (k : ℝ) / d := by
    intro heq
    have hy := hlayer hw
    by_cases hk : k ≤ i.2.val
    · have hk' : (k : ℝ) ≤ v := by
        dsimp only [v]
        exact_mod_cast hk
      have hdiv := div_le_div_of_nonneg_right hk' hd.le
      linarith
    · have hklt : i.2.val < k := lt_of_not_ge hk
      have hk' : v + 1 ≤ (k : ℝ) := by
        dsimp only [v]
        exact_mod_cast Nat.succ_le_of_lt hklt
      have hdiv := div_le_div_of_nonneg_right hk' hd.le
      linarith
  have hpassage : IsClosed (passage p n) :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le Complex.continuous_im.abs continuous_const))
  have htunnel : IsClosed (tunnel p n) :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le Complex.continuous_im.abs continuous_const))
  have hchamber (m : Fin (n + 1)) (j : Bool) : IsClosed (chamber p ⟨n, m⟩ j) :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)).inter
          (isClosed_le (continuous_const.mul Complex.continuous_im) continuous_const)))
  have hUsub : U ⊆ tract p δ := by
    intro w hw
    have hyb : b < w.im := by
      have hq : 0 ≤ v / d := div_nonneg hv hd.le
      linarith [(hlayer hw).1]
    let q : ℂ := ⟨a + 1, w.im⟩
    have hqgate : q ∈ gate p δ i true := by
      constructor
      · rfl
      · simpa [sideSign, q] using hw.2.2
    have hqtract : q ∈ tract p δ :=
      Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨true, hqgate⟩⟩)
    have him : |w.im| < Real.pi / 2 := tract_im_lt p δ hδ (z := q) hqtract
    have hamb : -2 < w.re ∧ |w.im| < Real.pi / 2 := ⟨by linarith [hw.1], him⟩
    by_cases hwall : w ∈ walls p
    · have hbwall : w ∈ blockWalls p n :=
        (walls_localization p n (by change a - 1 < w.re; linarith [hw.1])
          (by change w.re < a + 2; linarith [hw.2.1])).mp hwall
      have hre : w.re = a + 1 := by
        rcases hbwall with (hwpass | hwtun) | hwch
        · have hm := hpassage.frontier_subset hwpass
          have hle : |w.im| ≤ b := hm.2.2
          have hup := (abs_le.mp hle).2
          linarith
        · have hm := htunnel.frontier_subset hwtun
          have hle : |w.im| ≤ t := hm.2.2
          have hup := (abs_le.mp hle).2
          linarith
        · rcases mem_iUnion.mp hwch with ⟨m, hm⟩
          rcases mem_iUnion.mp hm with ⟨j, hj⟩
          cases j
          · have hm := (hchamber m false).frontier_subset hj
            have hlo : b + (m.val : ℝ) / d ≤ -w.im := by
              simpa [sideSign] using hm.2.2.1
            have hfrac : 0 ≤ (m.val : ℝ) / d := by positivity
            linarith
          · have hrect := rectangle_frontier_bounds a (a + 1)
              (b + (m.val : ℝ) / d) (b + ((m.val : ℝ) + 1) / d)
              (by simpa [chamber, sideSign] using hj)
            rcases hrect.2 with heq | heq | heq | heq
            · linarith [hw.1]
            · exact heq
            · exact False.elim (hgrid hw m.val heq)
            · apply False.elim
              apply hgrid hw (m.val + 1)
              simpa only [Nat.cast_add, Nat.cast_one] using heq
      have hgate : w ∈ gate p δ i true := by
        constructor
        · exact hre
        · simpa [sideSign] using hw.2.2
      exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨true, hgate⟩⟩)
    · exact Or.inl (Or.inl ⟨hamb, hwall⟩)
  exact hcontains.trans (interior_maximal hUsub hUopen)

theorem gate_subset_interior (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (i : GateIndex) (j : Bool) :
    gate p δ i j ⊆ interior (tract p δ) := by
  cases j with
  | true => exact positive_gate_subset_interior p δ hδ i
  | false =>
    let e : ℂ ≃ₜ ℂ := Complex.conjCLE.toHomeomorph
    have hpre : e ⁻¹' tract p δ = tract p δ := by
      ext z
      change star z ∈ tract p δ ↔ z ∈ tract p δ
      constructor
      · intro hz
        simpa only [star_star] using tract_star_mem p δ hz
      · exact tract_star_mem p δ
    have hinterior : e ⁻¹' interior (tract p δ) = interior (tract p δ) := by
      rw [e.preimage_interior, hpre]
    intro z hz
    let c : ℝ := chamberBase + (2 * (i.2.val : ℝ) + 1) /
      (2 * ((i.1 : ℝ) + 1))
    have hy : |z.im + c| < δ i / 2 := by
      simpa only [sideSign, Bool.false_eq_true, ite_false, neg_one_mul,
        sub_neg_eq_add] using hz.2
    have hgate : star z ∈ gate p δ i true := by
      constructor
      · simpa only [Complex.star_def, Complex.conj_re] using hz.1
      · change |-z.im - (1 : ℝ) * c| < δ i / 2
        rw [one_mul, show -z.im - c = -(z.im + c) by ring, abs_neg]
        exact hy
    have hin : z ∈ e ⁻¹' interior (tract p δ) :=
      positive_gate_subset_interior p δ hδ i hgate
    rwa [hinterior] at hin

end MaxModulusPoints.TractGeometry
