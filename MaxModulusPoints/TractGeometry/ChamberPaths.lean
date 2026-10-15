import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.BlockPositions
import MaxModulusPoints.TractGeometry.GapPaths
import MaxModulusPoints.TractGeometry.RectangleFrontiers
import MaxModulusPoints.TractGeometry.ShoulderPaths
import MaxModulusPoints.TractGeometry.StripContainment
import MaxModulusPoints.TractGeometry.Symmetry
import MaxModulusPoints.TractGeometry.Walls
/-!
# Paths inside the chamber layers

A positive chamber lies between consecutive grid heights. Vertical interpolation
to its center remains strictly inside the same layer and avoids every wall.
At the center height, paths continue through positive gates and descend through
the next gap to the real axis.
Complex conjugation supplies the corresponding paths in negative chambers.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem positive_chamber_joined_center (p : BlockParameters) (δ : GateIndex → ℝ)
    (i : GateIndex) {z : ℂ} (hl : blockPosition p i.1 < z.re)
    (hr : z.re < blockPosition p i.1 + 1)
    (hyl : chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) < z.im)
    (hyu : z.im < chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1)) :
    JoinedIn (tract p δ) z
      (⟨z.re, chamberBase + (2 * (i.2.val : ℝ) + 1) /
        (2 * ((i.1 : ℝ) + 1))⟩ : ℂ) := by
  let n : ℕ := i.1
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let v : ℝ := i.2.val
  let d : ℝ := (n : ℝ) + 1
  let t : ℝ := p.tunnelHeight n / 2
  let c : ℝ := b + (2 * v + 1) / (2 * d)
  change a < z.re at hl
  change z.re < a + 1 at hr
  change b + v / d < z.im at hyl
  change z.im < b + (v + 1) / d at hyu
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
  have hvtop : v + 1 ≤ d := by
    dsimp only [v, d, n]
    exact_mod_cast Nat.succ_le_iff.mpr i.2.isLt
  have htop : (v + 1) / d ≤ 1 := (div_le_one hd).mpr hvtop
  have hvfrac : 0 ≤ v / d := div_nonneg hv hd.le
  have hbtop : b + 1 = Real.pi / 2 := by dsimp [b, chamberBase]; ring
  have hcenterL : c = b + v / d + 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd]
    ring
  have hcenterU : c = b + (v + 1) / d - 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd]
    ring
  have hhalf : 0 < 1 / (2 * d) := by positivity
  have hcenter : c ∈ Ioo (b + v / d) (b + (v + 1) / d) := by
    constructor <;> linarith
  have hgrid {w : ℂ} (hwl : b + v / d < w.im)
      (hwu : w.im < b + (v + 1) / d) (k : ℕ) : w.im ≠ b + (k : ℝ) / d := by
    intro heq
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
  have hinside {w : ℂ} (hwl : a < w.re) (hwr : w.re < a + 1)
      (hwyl : b + v / d < w.im) (hwyu : w.im < b + (v + 1) / d) :
      w ∈ tract p δ := by
    have hyb : b < w.im := by linarith
    have hypos : 0 < w.im := lt_trans hb hyb
    have hym : w.im < Real.pi / 2 := by linarith
    refine Or.inl (Or.inl ⟨⟨by linarith, ?_⟩, ?_⟩)
    · rwa [abs_of_pos hypos]
    · intro hw
      have hlocal : w ∈ blockWalls p n :=
        (walls_localization p n (by change a - 1 < w.re; linarith)
          (by change w.re < a + 2; linarith)).mp hw
      rcases hlocal with (hp | ht) | hc
      · have hrect := rectangle_frontier_bounds a (a + 1 / 2) (-b) b
          (by simpa only [passage, abs_le] using hp)
        linarith [hrect.1.2.2.2]
      · have hrect := rectangle_frontier_bounds (a + 1 / 2) (a + 1) (-t) t
          (by simpa only [tunnel, abs_le] using ht)
        linarith [hrect.1.2.2.2]
      · rcases mem_iUnion.mp hc with ⟨m, hm⟩
        rcases mem_iUnion.mp hm with ⟨j, hj⟩
        cases j
        · have hclosed : IsClosed (chamber p ⟨n, m⟩ false) :=
            (isClosed_le continuous_const Complex.continuous_re).inter
              ((isClosed_le Complex.continuous_re continuous_const).inter
                ((isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)).inter
                  (isClosed_le (continuous_const.mul Complex.continuous_im) continuous_const)))
          have hlo : b + (m.val : ℝ) / d ≤ -w.im := by
            simpa [sideSign] using (hclosed.frontier_subset hj).2.2.1
          have hfrac : 0 ≤ (m.val : ℝ) / d := by positivity
          linarith
        · have hrect := rectangle_frontier_bounds a (a + 1)
            (b + (m.val : ℝ) / d) (b + ((m.val : ℝ) + 1) / d)
            (by simpa [chamber, sideSign] using hj)
          rcases hrect.2 with heq | heq | heq | heq
          · linarith
          · linarith
          · exact hgrid hwyl hwyu m.val heq
          · apply hgrid hwyl hwyu (m.val + 1)
            simpa only [Nat.cast_add, Nat.cast_one] using heq
  let f : ℝ → ℂ := fun s => ⟨z.re, (1 - s) * z.im + s * c⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk
        (((continuous_const.sub continuous_id).mul continuous_const).add
          (continuous_id.mul continuous_const)))
  refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
  · apply Complex.ext <;> simp [f]
  · apply Complex.ext <;> simp [f, c, b, v, d, n]
  · rintro w ⟨s, hs, rfl⟩
    have hstart : z.im ∈ Ioo (b + v / d) (b + (v + 1) / d) := ⟨hyl, hyu⟩
    have hcoord : (f s).im ∈ Ioo (b + v / d) (b + (v + 1) / d) := by
      change (1 - s) * z.im + s * c ∈ Ioo (b + v / d) (b + (v + 1) / d)
      simpa only [smul_eq_mul] using
        (convex_Ioo (b + v / d) (b + (v + 1) / d) :
          Convex ℝ (Ioo (b + v / d) (b + (v + 1) / d)))
          hstart hcenter (sub_nonneg.mpr hs.2) hs.1 (by ring)
    exact hinside hl hr hcoord.1 hcoord.2

theorem positive_chamber_center_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ j, δ j ≤ gateUpper j) (i : GateIndex) (hpos : 0 < δ i) {x : ℝ}
    (hl : blockPosition p i.1 < x) (hr : x ≤ blockPosition p i.1 + 1) :
    JoinedIn (tract p δ)
      (⟨x, chamberBase + (2 * (i.2.val : ℝ) + 1) /
        (2 * ((i.1 : ℝ) + 1))⟩ : ℂ)
      ((blockPosition p i.1 + 3 / 2 : ℝ) : ℂ) := by
  let n : ℕ := i.1
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let v : ℝ := i.2.val
  let d : ℝ := (n : ℝ) + 1
  let c : ℝ := b + (2 * v + 1) / (2 * d)
  change a < x at hl
  change x ≤ a + 1 at hr
  have hd : 0 < d := by dsimp [d]; positivity
  have ha : 1 ≤ a := by
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    have hg := blockPosition_growth p (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero] at hg
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 1 ≤ blockPosition p n
    linarith
  have hcenterL : c = b + v / d + 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd]
    ring
  have hcenterU : c = b + (v + 1) / d - 1 / (2 * d) := by
    dsimp only [c]
    field_simp [ne_of_gt hd]
    ring
  have hhalf : 0 < 1 / (2 * d) := by positivity
  have hcenter : c ∈ Ioo (b + v / d) (b + (v + 1) / d) := by
    constructor <;> linarith
  have hgate {w : ℂ} (hre : w.re = a + 1) (him : w.im = c) : w ∈ tract p δ := by
    have hg : w ∈ gate p δ i true := by
      constructor
      · exact hre
      · change |w.im - (1 : ℝ) * c| < δ i / 2
        rw [one_mul, him, sub_self, abs_zero]
        exact half_pos hpos
    exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨true, hg⟩⟩)
  have hcm : |c| < Real.pi / 2 :=
    tract_im_lt p δ hδ (z := ⟨a + 1, c⟩) (hgate rfl rfl)
  have hinside {w : ℂ} (hwl : a < w.re) (hwr : w.re < a + 2) (him : w.im = c) :
      w ∈ tract p δ := by
    rcases lt_trichotomy w.re (a + 1) with hlt | heq | hgt
    · exact (positive_chamber_joined_center p δ i (z := w) hwl hlt
        (by change b + v / d < w.im; rw [him]; exact hcenter.1)
        (by change w.im < b + (v + 1) / d; rw [him]; exact hcenter.2)).source_mem
    · exact hgate heq him
    · refine Or.inl (Or.inl ⟨⟨by linarith, ?_⟩, ?_⟩)
      · rw [him]
        exact hcm
      · intro hw
        have hlocal : w ∈ blockWalls p n :=
          (walls_localization p n (by change a - 1 < w.re; linarith)
            (by change w.re < a + 2; exact hwr)).mp hw
        have hbound : w.re ≤ a + 1 := (blockWalls_re_bounds p n hlocal).2
        linarith
  let q : ℂ := ⟨a + 3 / 2, c⟩
  let f : ℝ → ℂ := fun s => ⟨(1 - s) * x + s * (a + 3 / 2), c⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)).prodMk continuous_const)
  have hhor : JoinedIn (tract p δ) (⟨x, c⟩ : ℂ) q := by
    refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
    · apply Complex.ext <;> simp [f]
    · apply Complex.ext <;> simp [f, q]
    · rintro w ⟨s, hs, rfl⟩
      have hstart : x ∈ Ioo a (a + 2) := ⟨hl, by linarith⟩
      have hend : a + 3 / 2 ∈ Ioo a (a + 2) := by constructor <;> linarith
      have hcoord : (f s).re ∈ Ioo a (a + 2) := by
        change (1 - s) * x + s * (a + 3 / 2) ∈ Ioo a (a + 2)
        simpa only [smul_eq_mul] using
          (convex_Ioo a (a + 2) : Convex ℝ (Ioo a (a + 2)))
            hstart hend (sub_nonneg.mpr hs.2) hs.1 (by ring)
      exact hinside hcoord.1 hcoord.2 rfl
  have hqgap : ∀ k, q.re < blockPosition p k ∨ blockPosition p k + 1 < q.re := by
    intro k
    by_cases hk : k ≤ n
    · right
      have hg := blockPosition_growth p hk
      have hc : (k : ℝ) ≤ n := by exact_mod_cast hk
      change blockPosition p k + 1 < a + 3 / 2
      change blockPosition p k + 2 * ((n : ℝ) - (k : ℝ)) ≤ a at hg
      linarith
    · left
      have hnk : n < k := lt_of_not_ge hk
      have hg := blockPosition_growth p hnk.le
      have hc : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hnk
      change a + 3 / 2 < blockPosition p k
      change a + 2 * ((k : ℝ) - (n : ℝ)) ≤ blockPosition p k at hg
      linarith
  have hvert : JoinedIn (tract p δ) q ((a + 3 / 2 : ℝ) : ℂ) :=
    tract_gap_joined p δ (z := q) (by change -2 < a + 3 / 2; linarith) hcm hqgap
  exact hhor.trans hvert

theorem tract_chamber_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ k, δ k ≤ gateUpper k) (i : GateIndex) (hpos : 0 < δ i) (j : Bool)
    {z : ℂ} (hl : blockPosition p i.1 < z.re) (hr : z.re < blockPosition p i.1 + 1)
    (hyl : chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) < sideSign j * z.im)
    (hyu : sideSign j * z.im < chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1)) :
    JoinedIn (tract p δ) z ((blockPosition p i.1 + 3 / 2 : ℝ) : ℂ) := by
  have hpositive {w : ℂ} (hwl : blockPosition p i.1 < w.re)
      (hwr : w.re < blockPosition p i.1 + 1)
      (hwyl : chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) < w.im)
      (hwyu : w.im < chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1)) :
      JoinedIn (tract p δ) w ((blockPosition p i.1 + 3 / 2 : ℝ) : ℂ) :=
    (positive_chamber_joined_center p δ i hwl hwr hwyl hwyu).trans
      (positive_chamber_center_joined p δ hδ i hpos hwl hwr.le)
  cases j with
  | true =>
    exact hpositive hl hr (by simpa [sideSign] using hyl) (by simpa [sideSign] using hyu)
  | false =>
    have href : JoinedIn (tract p δ) (star z)
        ((blockPosition p i.1 + 3 / 2 : ℝ) : ℂ) :=
      hpositive (by simpa only [Complex.star_def, Complex.conj_re] using hl)
        (by simpa only [Complex.star_def, Complex.conj_re] using hr)
        (by simpa [sideSign, Complex.star_def] using hyl)
        (by simpa [sideSign, Complex.star_def] using hyu)
    have hconj : Continuous (star : ℂ → ℂ) := Complex.conjCLE.continuous
    have hmap := href.map hconj.continuousOn
    have hback := hmap.mono (by
      rintro w ⟨v, hv, rfl⟩
      exact tract_star_mem p δ hv)
    simpa [Complex.star_def] using hback

end MaxModulusPoints.TractGeometry
