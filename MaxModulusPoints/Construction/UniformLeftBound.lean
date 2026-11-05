module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.BoundedMaximum
public import MaxModulusPoints.Construction.PassageCut
public import MaxModulusPoints.Construction.RealPathBounds
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# A uniform bound to the left of each vertical line

The left-region estimate of Pardo-Simón–Sixsmith, Proposition 4.2,
follows by cutting at a future passage. The real reference is uniformly
bounded by finite-path clearance, the bottleneck controls the passage,
and the bounded-domain maximum principle propagates this control leftward.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set

noncomputable section

theorem tunnel_separation_nonneg (p : Blueprint.BlockParameters) (n : ℕ) :
    0 ≤ 1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi := by
  have hrec : 2 ≤ 1 / (2 * p.tunnelHeight n) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (p.tunnel_pos n))).mpr
    nlinarith [p.tunnel_le_quarter n]
  have hlog2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hlog32 : Real.log 32 ≤ 5 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hratio : Real.log 32 / Real.pi ≤ 2 :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  linarith

/-- For fixed spacing and positive tunnel heights, one bound controls the
real part on the whole left region uniformly over every admissible gate family. -/
theorem uniform_left_value_bound (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) (p : Blueprint.BlockParameters) (T : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (δ : Blueprint.GateIndex → ℝ),
      (∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i) →
      ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
      ∀ z ∈ Blueprint.tract p δ, z.re ≤ T → (G.toFun z).re ≤ A := by
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have hbase := (blockParametersLayout p).base_lower n
  change 2 * (n : ℝ) ≤ Blueprint.blockPosition p n at hbase
  have hTbase : T < Blueprint.blockPosition p n := by
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  let R := Blueprint.blockPosition p n + 3 / 2
  have hR : -1 ≤ R := by
    have hp := (blockParametersLayout p).base_nonneg n
    change 0 ≤ Blueprint.blockPosition p n at hp
    dsimp [R]
    linarith
  obtain ⟨A, hA, hreal⟩ := uniform_real_value_bound ψ p hR
  refine ⟨A, hA, ?_⟩
  intro δ hδ G z hz hzT
  have hpass (w : ℂ) (hw : w ∈ Blueprint.passageSlice p n) : (G.toFun w).re ≤ A := by
    have h := passage_bound_at_clean_reference hbottleneck ψ p δ hδ G hw
      (le_refl (0 : ℝ)) (tunnel_separation_nonneg p n)
    simp only [mul_zero, Real.exp_zero, one_mul] at h
    exact h.trans (hreal δ G R ⟨hR, le_rfl⟩)
  have hbound := logModel_re_le_of_frontier_bound G
    (passageCut_isOpen p δ n G.open_domain) inter_subset_left
    (passageCut_isBounded p δ (fun i => (hδ i).2) n) hA.le
    (fun w hw hwV => hpass w
      (passageCut_frontier_inside p δ (fun i => (hδ i).2) n G.open_domain hw hwV))
  exact hbound z (mem_passageCut_of_re_lt p δ n hz (hzT.trans_lt hTbase))

#print axioms uniform_left_value_bound

end

end MaxModulusPoints.Construction
