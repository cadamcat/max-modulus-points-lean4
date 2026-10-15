import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import MaxModulusPoints.Blueprint.Data
/-!
# Maximal vertical segments in a narrow tunnel

At an interior real coordinate of a tunnel, the vertical component through
the real axis is precisely the open segment between the two tunnel walls.
-/

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint

/-- The central vertical segment of a tunnel is a full vertical component of
the chamber and gate tract. Its endpoints remain excluded for every choice
of gate parameters. -/
theorem tunnel_vertical_component (p : BlockParameters) (δ : GateIndex → ℝ)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1) :
    connectedComponentIn (tract p δ ∩ {z : ℂ | z.re = s}) (s : ℂ) =
      {z : ℂ | z.re = s ∧ |z.im| < p.tunnelHeight n / 2} := by
  have hheight : 0 < p.tunnelHeight n / 2 := half_pos (p.tunnel_pos n)
  have hchamber : p.tunnelHeight n / 2 < chamberBase := by
    dsimp [chamberBase]
    linarith [Real.pi_gt_three, p.tunnel_le_quarter n]
  have hposition : 0 ≤ blockPosition p n := by
    unfold blockPosition
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => le_trans zero_le_one (p.gap_ge_one k))
      (Nat.cast_nonneg n)
  have hstep (k : ℕ) : blockPosition p k + 2 ≤ blockPosition p (k + 1) := by
    simp only [blockPosition, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linarith [p.gap_ge_one (k + 1)]
  have hmono : Monotone (blockPosition p) :=
    monotone_nat_of_le_succ fun k => by linarith [hstep k]
  have hindex (k : ℕ) (hl : blockPosition p k ≤ s)
      (hu : s ≤ blockPosition p k + 1) : k = n := by
    rcases lt_trichotomy k n with hk | hk | hk
    · have hm := hmono (Nat.succ_le_of_lt hk)
      linarith [hstep k]
    · exact hk
    · have hm := hmono (Nat.succ_le_of_lt hk)
      linarith [hstep n]
  have hfrontbox (k : ℕ) (S : Set ℂ)
      (hS : S ⊆ {z : ℂ | blockPosition p k ≤ z.re ∧ z.re ≤ blockPosition p k + 1}) :
      frontier S ⊆ {z : ℂ | blockPosition p k ≤ z.re ∧
        z.re ≤ blockPosition p k + 1} :=
    frontier_subset_closure.trans (closure_minimal hS
      ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)))
  have hwallbox (k : ℕ) {z : ℂ}
      (hz : z ∈ frontier (passage p k) ∪ frontier (tunnel p k) ∪
        ⋃ m : Fin (k + 1), ⋃ j : Bool, frontier (chamber p ⟨k, m⟩ j)) :
      blockPosition p k ≤ z.re ∧ z.re ≤ blockPosition p k + 1 := by
    rcases hz with (hz | hz) | hz
    · exact hfrontbox k (passage p k) (fun q hq => ⟨hq.1, by linarith [hq.2.1]⟩) hz
    · exact hfrontbox k (tunnel p k) (fun q hq => ⟨by linarith [hq.1], hq.2.1⟩) hz
    · rcases mem_iUnion.mp hz with ⟨m, hm⟩
      rcases mem_iUnion.mp hm with ⟨j, hj⟩
      exact hfrontbox k (chamber p ⟨k, m⟩ j) (fun _ hq => ⟨hq.1, hq.2.1⟩) hj
  have hinside {z : ℂ} (hzre : z.re = s)
      (hzim : |z.im| < p.tunnelHeight n / 2) : z ∈ tract p δ := by
    refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
    · linarith [hs.1]
    · dsimp [chamberBase] at hchamber
      linarith
    · intro hz
      rcases mem_iUnion.mp hz with ⟨k, hk⟩
      have hbox := hwallbox k hk
      rw [hzre] at hbox
      have hkn := hindex k hbox.1 hbox.2
      subst k
      rcases hk with (hk | hk) | hk
      · have hu : z.re ≤ blockPosition p n + 1 / 2 :=
          closure_minimal (fun _ hq => hq.2.1)
            (isClosed_le Complex.continuous_re continuous_const)
            (frontier_subset_closure hk)
        linarith [hs.1]
      · have hint : z ∈ interior (tunnel p n) := by
          refine mem_interior.mpr
            ⟨{q : ℂ | blockPosition p n + 1 / 2 < q.re ∧
              q.re < blockPosition p n + 1 ∧ |q.im| < p.tunnelHeight n / 2},
              (fun _ hq => ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩), ?_, ?_⟩
          · exact (isOpen_lt continuous_const Complex.continuous_re).inter
              ((isOpen_lt Complex.continuous_re continuous_const).inter
                (isOpen_lt Complex.continuous_im.abs continuous_const))
          · exact ⟨by simpa [hzre] using hs.1, by simpa [hzre] using hs.2, hzim⟩
        exact (mem_frontier_iff_notMem_interior (interior_subset hint)).mp hk hint
      · rcases mem_iUnion.mp hk with ⟨m, hm⟩
        rcases mem_iUnion.mp hm with ⟨j, hj⟩
        have hl : chamberBase + (m.val : ℝ) / ((n : ℝ) + 1) ≤ sideSign j * z.im :=
          closure_minimal (fun _ hq => hq.2.2.1)
            (isClosed_le continuous_const (continuous_const.mul Complex.continuous_im))
            (frontier_subset_closure hj)
        have hfrac : 0 ≤ (m.val : ℝ) / ((n : ℝ) + 1) := by positivity
        have hsign : sideSign j * z.im ≤ |z.im| := by
          cases j
          · simpa [sideSign] using neg_le_abs z.im
          · simpa [sideSign] using le_abs_self z.im
        linarith
  have hboundary {z : ℂ} (hzre : z.re = s)
      (hzim : |z.im| = p.tunnelHeight n / 2) : z ∉ tract p δ := by
    have hzmem : z ∈ tunnel p n :=
      ⟨by linarith [hs.1], by linarith [hs.2], hzim.le⟩
    have hzfront : z ∈ frontier (tunnel p n) := by
      apply (mem_frontier_iff_notMem_interior hzmem).mpr
      intro hint
      have hstrip : z ∈ interior (Complex.im ⁻¹'
          Icc (-(p.tunnelHeight n / 2)) (p.tunnelHeight n / 2)) :=
        interior_mono (fun _ hq => abs_le.mp hq.2.2) hint
      rw [Complex.interior_preimage_im, interior_Icc] at hstrip
      have hlt : |z.im| < p.tunnelHeight n / 2 := abs_lt.mpr hstrip
      linarith
    intro hz
    rcases hz with (hz | hz) | hz
    · exact hz.2 (mem_iUnion.mpr ⟨n, Or.inl (Or.inr hzfront)⟩)
    · rcases mem_iUnion.mp hz with ⟨k, hk⟩
      have hbox : blockPosition p k ≤ s ∧ s ≤ blockPosition p k + 1 := by
        rcases hk with hk | hk | hk <;> rw [hzre] at hk <;>
          exact ⟨by linarith [hk.1], by linarith [hk.1]⟩
      have hkn := hindex k hbox.1 hbox.2
      subst k
      rcases hk with hk | hk | hk <;> rw [hzre] at hk <;> linarith [hk.1, hs.1, hs.2]
    · rcases mem_iUnion.mp hz with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨j, hj⟩
      have hre : s = blockPosition p i.1 + 1 := by simpa [hzre] using hj.1
      have hin := hindex i.1 (by linarith) (by linarith)
      rw [hin] at hre
      linarith [hs.2]
  let S : Set ℂ := {z : ℂ | z.re = s ∧ |z.im| < p.tunnelHeight n / 2}
  have hSbase : (s : ℂ) ∈ S := by simpa [S] using hheight
  have hSsubset : S ⊆ tract p δ ∩ {z : ℂ | z.re = s} :=
    fun _ hz => ⟨hinside hz.1 hz.2, hz.1⟩
  have hSpreconnected : IsPreconnected S := by
    have hconvex : Convex ℝ S := by
      have heq : S = (Complex.re ⁻¹' {s}) ∩
          (Complex.im ⁻¹' Ioo (-(p.tunnelHeight n / 2)) (p.tunnelHeight n / 2)) := by
        ext z
        simp [S, abs_lt]
      rw [heq]
      exact ((convex_singleton s).linear_preimage Complex.reCLM.toLinearMap).inter
        ((convex_Ioo (-(p.tunnelHeight n / 2)) (p.tunnelHeight n / 2)).linear_preimage
          Complex.imCLM.toLinearMap)
    exact hconvex.isPreconnected
  apply subset_antisymm
  · intro z hz
    have hzmem := connectedComponentIn_subset
      (tract p δ ∩ {q : ℂ | q.re = s}) (s : ℂ) hz
    refine ⟨hzmem.2, abs_lt.mpr ⟨?_, ?_⟩⟩
    · by_contra hn
      have hzle : z.im ≤ -(p.tunnelHeight n / 2) := le_of_not_gt hn
      obtain ⟨q, hq, hqim⟩ := isPreconnected_connectedComponentIn.intermediate_value
        hz (mem_connectedComponentIn (hSsubset hSbase)) Complex.continuous_im.continuousOn
        ⟨hzle, by simp only [Complex.ofReal_im]; linarith⟩
      have hqmem := connectedComponentIn_subset
        (tract p δ ∩ {r : ℂ | r.re = s}) (s : ℂ) hq
      exact hboundary hqmem.2 (by rw [hqim, abs_neg, abs_of_pos hheight]) hqmem.1
    · by_contra hn
      have hzge : p.tunnelHeight n / 2 ≤ z.im := le_of_not_gt hn
      obtain ⟨q, hq, hqim⟩ := isPreconnected_connectedComponentIn.intermediate_value
        (mem_connectedComponentIn (hSsubset hSbase)) hz Complex.continuous_im.continuousOn
        ⟨by simp only [Complex.ofReal_im]; linarith, hzge⟩
      have hqmem := connectedComponentIn_subset
        (tract p δ ∩ {r : ℂ | r.re = s}) (s : ℂ) hq
      exact hboundary hqmem.2 (by rw [hqim, abs_of_pos hheight]) hqmem.1
  · exact hSpreconnected.subset_connectedComponentIn hSbase hSsubset

end MaxModulusPoints.CrosscutDistortion
