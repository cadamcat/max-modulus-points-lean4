module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import MaxModulusPoints.Blueprint.Data

/-!
# Strip containment of the chamber and gate tracts

The tract of Pardo-Simón–Sixsmith, §4, lies to the right of the line with
real coordinate `-2`, in the horizontal strip with imaginary part between
`-π / 2` and `π / 2`.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_re_gt (p : BlockParameters) (δ : GateIndex → ℝ) {z : ℂ}
    (hz : z ∈ tract p δ) : -2 < z.re := by
  have hpos : ∀ n, 0 ≤ blockPosition p n := by
    intro n
    unfold blockPosition
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => le_trans zero_le_one (p.gap_ge_one k))
      (Nat.cast_nonneg n)
  rcases hz with (hz | hz) | hz
  · exact hz.1.1
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    rcases hn with hn | hn | hn <;> linarith [hpos n, hn.1]
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    linarith [hpos i.1, hj.1]

theorem tract_im_lt (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) {z : ℂ} (hz : z ∈ tract p δ) :
    |z.im| < Real.pi / 2 := by
  rcases hz with (hz | hz) | hz
  · exact hz.1.2
  · rcases mem_iUnion.mp hz with ⟨n, hn⟩
    rcases hn with hn | hn | hn
    · have hb := hn.2
      dsimp [chamberBase] at hb
      linarith
    · have ht := p.tunnel_le_quarter n
      have hpi := Real.two_le_pi
      linarith [hn.2]
    · have ht := p.tunnel_le_quarter n
      have hpi := Real.two_le_pi
      linarith [hn.2]
  · rcases mem_iUnion.mp hz with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨j, hj⟩
    have hd : 0 < (i.1 : ℝ) + 1 := by positivity
    have hv : (i.2.val : ℝ) + 1 ≤ (i.1 : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_iff.mpr i.2.isLt
    have hv0 : 0 ≤ (i.2.val : ℝ) := Nat.cast_nonneg _
    have hδ' := hδ i
    dsimp [gateUpper] at hδ'
    have hδmul : δ i * ((i.1 : ℝ) + 1) ≤ 1 :=
      (le_div_iff₀ hd).mp hδ'
    have hfrac :
        (2 * (i.2.val : ℝ) + 1) / (2 * ((i.1 : ℝ) + 1)) + δ i / 2 ≤ 1 := by
      have hq : (2 * (i.2.val : ℝ) + 1) / (2 * ((i.1 : ℝ) + 1)) ≤
          1 - δ i / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * ((i.1 : ℝ) + 1))).mpr
        nlinarith
      linarith
    have hc : 0 < chamberBase +
        (2 * (i.2.val : ℝ) + 1) / (2 * ((i.1 : ℝ) + 1)) := by
      have hpi := Real.two_le_pi
      have hq : 0 < (2 * (i.2.val : ℝ) + 1) / (2 * ((i.1 : ℝ) + 1)) := by positivity
      dsimp [chamberBase]
      linarith
    have hδone : δ i ≤ 1 := by
      apply le_trans hδ' ((div_le_one hd).mpr ?_)
      have hn : 0 ≤ (i.1 : ℝ) := Nat.cast_nonneg _
      linarith
    have hpi := Real.two_le_pi
    have hj' := abs_lt.mp hj.2
    cases j <;> simp [sideSign] at hj' <;>
      apply abs_lt.mpr <;> dsimp [chamberBase] at * <;> constructor <;> linarith

theorem tract_exp_injective (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) : InjOn Complex.exp (tract p δ) := by
  intro z hz w hw hzw
  have hz' := abs_lt.mp (tract_im_lt p δ hδ hz)
  have hw' := abs_lt.mp (tract_im_lt p δ hδ hw)
  have hpi := Real.pi_pos
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi (by linarith) (by linarith)
    (by linarith) (by linarith) hzw

end MaxModulusPoints.TractGeometry
