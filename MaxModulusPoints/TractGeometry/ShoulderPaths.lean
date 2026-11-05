module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.BlockPositions
public import MaxModulusPoints.TractGeometry.GapPaths
public import MaxModulusPoints.TractGeometry.RectangleFrontiers
public import MaxModulusPoints.TractGeometry.TunnelPaths
public import MaxModulusPoints.TractGeometry.Walls

/-!
# Paths from the regions beside a passage

Between the tunnel and the chamber base, points to the right of the passage
can move horizontally into the next gap and then vertically to the real axis.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_shoulder_joined (p : BlockParameters) (δ : GateIndex → ℝ) (n : ℕ) {z : ℂ}
    (hl : blockPosition p n + 1 / 2 < z.re) (hr : z.re < blockPosition p n + 1)
    (hyt : p.tunnelHeight n / 2 < |z.im|) (hyb : |z.im| < chamberBase) :
    JoinedIn (tract p δ) z ((blockPosition p n + 3 / 2 : ℝ) : ℂ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let t : ℝ := p.tunnelHeight n / 2
  change a + 1 / 2 < z.re at hl
  change z.re < a + 1 at hr
  change t < |z.im| at hyt
  change |z.im| < b at hyb
  have ha : 1 ≤ a := by
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    have hg := blockPosition_growth p (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero] at hg
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    change 1 ≤ blockPosition p n
    linarith
  have hb : b < Real.pi / 2 := by dsimp [b, chamberBase]; linarith
  have hinside {w : ℂ} (hwl : a + 1 / 2 < w.re) (hwr : w.re < a + 2)
      (hwyt : t < |w.im|) (hwyb : |w.im| < b) : w ∈ tract p δ := by
    refine Or.inl (Or.inl ⟨⟨by linarith, lt_trans hwyb hb⟩, ?_⟩)
    intro hw
    have hlocal : w ∈ blockWalls p n :=
      (walls_localization p n (by change a - 1 < w.re; linarith)
        (by change w.re < a + 2; exact hwr)).mp hw
    rcases hlocal with (hp | ht) | hc
    · have hrect := rectangle_frontier_bounds a (a + 1 / 2) (-b) b
        (by simpa only [passage, abs_le] using hp)
      linarith [hrect.1.2.1]
    · have hrect := rectangle_frontier_bounds (a + 1 / 2) (a + 1) (-t) t
        (by simpa only [tunnel, abs_le] using ht)
      have hbound : |w.im| ≤ t := abs_le.mpr hrect.1.2.2
      linarith
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
      rcases abs_lt.mp hwyb with ⟨hyl, hyu⟩
      cases j <;> simp [sideSign] at hlow <;> linarith
  let q : ℂ := ⟨a + 3 / 2, z.im⟩
  let f : ℝ → ℂ := fun s => ⟨(1 - s) * z.re + s * (a + 3 / 2), z.im⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)).prodMk continuous_const)
  have hhor : JoinedIn (tract p δ) z q := by
    refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
    · apply Complex.ext <;> simp [f]
    · apply Complex.ext <;> simp [f, q]
    · rintro w ⟨s, hs, rfl⟩
      have hstart : z.re ∈ Ioo (a + 1 / 2) (a + 2) := ⟨hl, by linarith⟩
      have hend : a + 3 / 2 ∈ Ioo (a + 1 / 2) (a + 2) := by
        constructor <;> linarith
      have hcoord : (f s).re ∈ Ioo (a + 1 / 2) (a + 2) := by
        change (1 - s) * z.re + s * (a + 3 / 2) ∈ Ioo (a + 1 / 2) (a + 2)
        simpa only [smul_eq_mul] using
          (convex_Ioo (a + 1 / 2) (a + 2) : Convex ℝ (Ioo (a + 1 / 2) (a + 2)))
            hstart hend (sub_nonneg.mpr hs.2) hs.1 (by ring)
      exact hinside hcoord.1 hcoord.2 hyt hyb
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
    tract_gap_joined p δ (z := q) (by change -2 < a + 3 / 2; linarith)
      (lt_trans hyb hb) hqgap
  exact hhor.trans hvert

end MaxModulusPoints.TractGeometry
