module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.CrosscutDistortion.ConformalArea

/-!
# Real-part separation across a narrow tunnel

The passage and clean slices belong to the tract. The length–area bound
with additive constant one therefore implies the required crosscut
distortion estimate with additive constant `log 32 / π`.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint

private theorem wall_block_bounds (p : BlockParameters) (k : ℕ) {q : ℂ}
    (hq : q ∈ frontier (passage p k) ∪ frontier (tunnel p k) ∪
      ⋃ m : Fin (k + 1), ⋃ j : Bool, frontier (chamber p ⟨k, m⟩ j)) :
    blockPosition p k ≤ q.re ∧ q.re ≤ blockPosition p k + 1 := by
  have hfrontbox (S : Set ℂ)
      (hS : S ⊆ {z : ℂ | blockPosition p k ≤ z.re ∧ z.re ≤ blockPosition p k + 1}) :
      frontier S ⊆ {z : ℂ | blockPosition p k ≤ z.re ∧ z.re ≤ blockPosition p k + 1} :=
    frontier_subset_closure.trans (closure_minimal hS
      ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)))
  rcases hq with (hq | hq) | hq
  · exact hfrontbox (passage p k) (fun z hz => ⟨hz.1, by linarith [hz.2.1]⟩) hq
  · exact hfrontbox (tunnel p k) (fun z hz => ⟨by linarith [hz.1], hz.2.1⟩) hq
  · rcases mem_iUnion.mp hq with ⟨m, hm⟩
    rcases mem_iUnion.mp hm with ⟨j, hj⟩
    exact hfrontbox (chamber p ⟨k, m⟩ j) (fun _ hz => ⟨hz.1, hz.2.1⟩) hj

/-- Both distinguished open slices avoid every wall and lie in the tract,
regardless of the restored gate widths. -/
theorem distinguished_slices_subset_tract (p : BlockParameters) (δ : GateIndex → ℝ)
    (n : ℕ) : passageSlice p n ⊆ tract p δ ∧ cleanSlice p n ⊆ tract p δ := by
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
  constructor
  · intro q hq
    have hqre : q.re = blockPosition p n + 1 / 4 := hq.1
    have hqim : |q.im| < chamberBase := hq.2
    refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, ?_⟩)
    · linarith
    · dsimp [chamberBase] at hqim
      linarith
    · intro hwall
      rcases mem_iUnion.mp hwall with ⟨k, hk⟩
      have hbox := wall_block_bounds p k hk
      have hkn : k = n := by
        rcases lt_trichotomy k n with h | h | h
        · have hm := hmono (Nat.succ_le_of_lt h)
          linarith [hstep k]
        · exact h
        · have hm := hmono (Nat.succ_le_of_lt h)
          linarith [hstep n]
      subst k
      rcases hk with (hk | hk) | hk
      · have hint : q ∈ interior (passage p n) := by
          refine mem_interior.mpr
            ⟨{v : ℂ | blockPosition p n < v.re ∧
              v.re < blockPosition p n + 1 / 2 ∧ |v.im| < chamberBase},
              (fun _ hv => ⟨hv.1.le, hv.2.1.le, hv.2.2.le⟩), ?_, ?_⟩
          · exact (isOpen_lt continuous_const Complex.continuous_re).inter
              ((isOpen_lt Complex.continuous_re continuous_const).inter
                (isOpen_lt Complex.continuous_im.abs continuous_const))
          · exact ⟨by linarith, by linarith, hqim⟩
        exact (mem_frontier_iff_notMem_interior (interior_subset hint)).mp hk hint
      · have hl : blockPosition p n + 1 / 2 ≤ q.re :=
          closure_minimal (fun _ hv => hv.1)
            (isClosed_le continuous_const Complex.continuous_re)
            (frontier_subset_closure hk)
        linarith
      · rcases mem_iUnion.mp hk with ⟨m, hm⟩
        rcases mem_iUnion.mp hm with ⟨j, hj⟩
        have hl : chamberBase + (m.val : ℝ) / ((n : ℝ) + 1) ≤ sideSign j * q.im :=
          closure_minimal (fun _ hv => hv.2.2.1)
            (isClosed_le continuous_const (continuous_const.mul Complex.continuous_im))
            (frontier_subset_closure hj)
        have hfrac : 0 ≤ (m.val : ℝ) / ((n : ℝ) + 1) := by positivity
        have hsign : sideSign j * q.im ≤ |q.im| := by
          cases j
          · simpa [sideSign] using neg_le_abs q.im
          · simpa [sideSign] using le_abs_self q.im
        linarith
  · intro q hq
    have hqre : q.re = blockPosition p n + 3 / 2 := hq.1
    refine Or.inl (Or.inl ⟨⟨by linarith, hq.2⟩, ?_⟩)
    intro hwall
    rcases mem_iUnion.mp hwall with ⟨k, hk⟩
    have hbox := wall_block_bounds p k hk
    rcases le_or_gt k n with h | h
    · have hm := hmono h
      linarith
    · have hm := hmono (Nat.succ_le_of_lt h)
      linarith [hstep n]

/-- The logarithmic crosscut constant is at least one. -/
theorem one_le_log32_div_pi : 1 ≤ Real.log 32 / Real.pi := by
  have hlogtwo : (2 : ℝ) / 3 ≤ Real.log 2 := by
    convert Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) using 1 <;> norm_num
  have hlogpow : Real.log 32 = 5 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 5 using 1 <;> norm_num
  apply (le_div_iff₀ Real.pi_pos).mpr
  rw [hlogpow]
  linarith [Real.pi_lt_d2]

end MaxModulusPoints.CrosscutDistortion

namespace MaxModulusPoints.Blueprint.Packages

open MaxModulusPoints.CrosscutDistortion

/-- Real-part separation through a tunnel of length one half, with the
normalization and constant of the crosscut distortion estimate. -/
theorem bottleneck_estimates_proof : BottleneckEstimates := by
  intro p δ _hδ φ hφ0 hφre hφim n z hz w hw
  have hmem := distinguished_slices_subset_tract p δ n
  have hstrong := tunnel_separation_lower_bound_of_mem p δ φ hφ0 hφre hφim n w z
    hw hz (hmem.1 hw) (hmem.2 hz)
  linarith [one_le_log32_div_pi]

end MaxModulusPoints.Blueprint.Packages
