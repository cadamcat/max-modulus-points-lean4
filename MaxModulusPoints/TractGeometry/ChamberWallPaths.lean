import Mathlib.Algebra.Order.Floor.Semiring
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.ExteriorPaths
import MaxModulusPoints.TractGeometry.RectangleFrontiers
import MaxModulusPoints.TractGeometry.RestoredWalls
import MaxModulusPoints.TractGeometry.StripContainment
import MaxModulusPoints.TractGeometry.Symmetry
import MaxModulusPoints.TractGeometry.Walls
/-!
# Paths along the chamber walls

The left edges of the positive chambers continue vertically to the upper
boundary of the ambient strip. They meet no restored openings or gates, so
their points connect to the exterior within the tract complement. Conjugation
gives the corresponding paths on the negative chamber edges.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem positive_chamber_left_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ) {z : ℂ}
    (hx : z.re = blockPosition p n) (hy : chamberBase ≤ z.im) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  let a : ℝ := blockPosition p n
  let b : ℝ := chamberBase
  let d : ℝ := (n : ℝ) + 1
  let S : Set ℂ := {w | w.re = a ∧ b ≤ w.im}
  have hd : 0 < d := by dsimp [d]; positivity
  have hS : S ⊆ (tract p δ)ᶜ := by
    intro w hw hmem
    change w.re = a ∧ b ≤ w.im at hw
    by_cases htop : w.im < Real.pi / 2
    · let t : ℝ := (w.im - b) * d
      let k : ℕ := ⌊t⌋₊
      have ht0 : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hw.2) hd.le
      have htbound : t < d := by
        have hsmall : w.im - b < 1 := by
          dsimp only [b, chamberBase]
          linarith
        simpa only [one_mul] using mul_lt_mul_of_pos_right hsmall hd
      have hk : k < n + 1 := (Nat.floor_lt ht0).mpr (by
        simpa only [Nat.cast_add, Nat.cast_one] using htbound)
      have hle : (k : ℝ) / d ≤ w.im - b :=
        (div_le_iff₀ hd).mpr (Nat.floor_le ht0)
      have hlt : w.im - b < ((k : ℝ) + 1) / d :=
        (lt_div_iff₀ hd).mpr (Nat.lt_floor_add_one t)
      have hlo : b + (k : ℝ) / d ≤ w.im := by linarith
      have hhi : w.im ≤ b + ((k : ℝ) + 1) / d := by linarith
      have hrect : w ∈ frontier {v : ℂ | a ≤ v.re ∧ v.re ≤ a + 1 ∧
          b + (k : ℝ) / d ≤ v.im ∧ v.im ≤ b + ((k : ℝ) + 1) / d} :=
        (rectangle_mem_frontier_iff a (a + 1) (b + (k : ℝ) / d)
          (b + ((k : ℝ) + 1) / d)).mpr
          ⟨⟨by linarith [hw.1], by linarith [hw.1], hlo, hhi⟩, Or.inl hw.1⟩
      have hfront : w ∈ frontier (chamber p ⟨n, ⟨k, hk⟩⟩ true) := by
        simpa only [chamber, sideSign, Bool.true_eq, ite_true, one_mul, a, b, d] using hrect
      have hwall : w ∈ blockWalls p n :=
        Or.inr (mem_iUnion.mpr ⟨⟨k, hk⟩, mem_iUnion.mpr ⟨true, hfront⟩⟩)
      rcases (blockWalls_mem_tract_iff p δ n hwall).mp hmem with hopen | ⟨m, j, hg⟩
      · rcases hopen with h | h | h
        · exact (not_lt_of_ge (hw.2.trans (le_abs_self _))) h.2
        · have hre : w.re = a + 1 / 2 := h.1
          linarith [hw.1]
        · have hre : w.re = a + 1 := h.1
          linarith [hw.1]
      · have hre : w.re = a + 1 := hg.1
        linarith [hw.1]
    · have him : Real.pi / 2 ≤ |w.im| := (le_of_not_gt htop).trans (le_abs_self _)
      exact (not_lt_of_ge him) (tract_im_lt p δ hδ hmem)
  have hconv : Convex ℝ S :=
    ((convex_singleton a).linear_preimage Complex.reLm).inter
      ((convex_Ici b).linear_preimage Complex.imLm)
  let q : ℂ := ⟨a, Real.pi / 2⟩
  have hzS : z ∈ S := ⟨hx, hy⟩
  have hqS : q ∈ S := by
    refine ⟨rfl, ?_⟩
    dsimp only [q, b, chamberBase]
    linarith
  have hvertical : JoinedIn (tract p δ)ᶜ z q :=
    ((hconv.isPathConnected ⟨z, hzS⟩).joinedIn z hzS q hqS).mono hS
  have houter : JoinedIn (tract p δ)ᶜ q (-3 : ℂ) :=
    tract_compl_exterior_joined p δ hδ (Or.inr (by
      change Real.pi / 2 ≤ |Real.pi / 2|
      exact le_abs_self _))
  exact hvertical.trans houter

theorem chamber_left_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ) (j : Bool) {z : ℂ}
    (hx : z.re = blockPosition p n) (hy : chamberBase ≤ sideSign j * z.im) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  cases j with
  | true =>
    exact positive_chamber_left_compl_joined p δ hδ n hx (by simpa [sideSign] using hy)
  | false =>
    have href : JoinedIn (tract p δ)ᶜ (star z) (-3 : ℂ) :=
      positive_chamber_left_compl_joined p δ hδ n
        (by simpa only [Complex.star_def, Complex.conj_re] using hx)
        (by simpa [sideSign, Complex.star_def] using hy)
    have hconj : Continuous (star : ℂ → ℂ) := Complex.conjCLE.continuous
    have hmap := href.map hconj.continuousOn
    have hback : JoinedIn (tract p δ)ᶜ (star (star z)) (star (-3 : ℂ)) := hmap.mono (by
      rintro w ⟨v, hv, rfl⟩ hmem
      apply hv
      simpa only [star_star] using tract_star_mem p δ hmem)
    simpa [Complex.star_def] using hback

end MaxModulusPoints.TractGeometry
