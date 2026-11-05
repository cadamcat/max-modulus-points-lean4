module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.Blueprint.Interfaces.HalfDiscBarriers
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.EndpointBounds
public import MaxModulusPoints.Construction.OpenGateComparison
public import MaxModulusPoints.Construction.SliceWindows
public import MaxModulusPoints.Construction.StarredSegments
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# Fixed starred segments and a uniform endpiece ceiling

The endpoint radii in Pardo-Simón–Sixsmith, Proposition 4.4, allow a
single choice of compact segments before the gates are chosen. Each
open-chamber witness and each real passage witness can be retained.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set

noncomputable section

theorem real_sample_mem_starSlice (p : Blueprint.BlockParameters) (q : SliceCutoffs) (n : ℕ) :
    ((Blueprint.slicePosition p n : ℝ) : ℂ) ∈ starSlice (blockParametersLayout p) q n none := by
  refine ⟨rfl, ?_, ?_⟩
  · change -passageHalfHeight + q.passage n ≤ 0
    linarith [q.passage_small n]
  · change 0 ≤ passageHalfHeight - q.passage n
    linarith [q.passage_small n]

theorem fullSlice_subset_literal_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (G : Blueprint.LogModel (Blueprint.tract p δ))
    (n : ℕ) (i : SliceIndex n) :
    fullSlice (blockParametersLayout p) n i ⊆ Blueprint.tract p δ := by
  intro z hz
  have hx : z.re = Blueprint.slicePosition p n := hz.1
  exact (fullSliceWindow p n i).inside δ G z (by simp [hx]) hz.2.1 hz.2.2

/-- Cutoffs are fixed simultaneously below all endpoint radii, with the
same cutoff for reflected chambers and with the chosen witnesses retained. -/
theorem exists_uniform_starred_endpiece_bound
    (hbottleneck : Blueprint.BottleneckEstimates) (hhalf : Blueprint.HalfDiscBarriers)
    (ψ : Blueprint.StripMapData) (p : Blueprint.BlockParameters)
    (ξ : GateIndex → ℂ)
    (hξ : ∀ i, ξ i ∈ fullSlice (blockParametersLayout p) i.1 (some (false, i.2))) :
    ∃ q : SliceCutoffs,
      (∀ i, ξ i ∈ starSlice (blockParametersLayout p) q i.1 (some (false, i.2))) ∧
      ∀ (δ : Blueprint.GateIndex → ℝ),
        (∀ k, 0 < δ k ∧ δ k ≤ Blueprint.gateUpper k) →
      ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
      ∀ n i, ∀ z ∈ fullSlice (blockParametersLayout p) n i \
        starSlice (blockParametersLayout p) q n i, (G.toFun z).re ≤ 1 := by
  choose η hη hbound using fun n i => uniform_slice_endpoint_bound hbottleneck hhalf ψ p n i
  let ηC : GateIndex → ℝ := fun i => min (η i.1 (some (false, i.2))) (η i.1 (some (true, i.2)))
  obtain ⟨q, hqP, hqC, hqξ⟩ := exists_sliceCutoffs (blockParametersLayout p)
    (fun n => η n none) (fun n => hη n none) ηC
    (fun i => lt_min (hη _ _) (hη _ _)) ξ hξ
  refine ⟨q, hqξ, ?_⟩
  intro δ hδ G n i z hz
  have hsmall : q.amount n i ≤ η n i := by
    rcases i with _ | ⟨s, m⟩
    · exact hqP n
    · cases s
      · exact (hqC ⟨n, m⟩).trans (min_le_left _ _)
      · exact (hqC ⟨n, m⟩).trans (min_le_right _ _)
  apply hbound n i δ hδ G z hz.1
  rcases (not_mem_starSlice_iff (blockParametersLayout p) q n i hz.1).mp hz.2 with hlo | hhi
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The conformal endpiece bound survives the same approximation error used
in both gate comparisons. -/
theorem starred_endpiece_norm_bound (p : Blueprint.BlockParameters) (q : SliceCutoffs)
    (δ : Blueprint.GateIndex → ℝ) (G : Blueprint.LogModel (Blueprint.tract p δ))
    {M : ℝ} (hM : 0 ≤ M) (f : ℂ → ℂ)
    (happrox : ∀ z ∈ Blueprint.tract p δ, 1 < ‖Complex.exp z‖ →
      ‖f (Complex.exp z) - Complex.exp (G.toFun z)‖ ≤ M / ‖Complex.exp z‖)
    (hbound : ∀ n i, ∀ z ∈ fullSlice (blockParametersLayout p) n i \
      starSlice (blockParametersLayout p) q n i, (G.toFun z).re ≤ 1)
    (n : ℕ) (i : SliceIndex n) {z : ℂ}
    (hz : z ∈ fullSlice (blockParametersLayout p) n i \ starSlice (blockParametersLayout p) q n i) :
    ‖f (Complex.exp z)‖ ≤ Real.exp 1 + M := by
  have herr := approximation_error_on_sample p n hM happrox
    (fullSlice_subset_literal_tract p δ G n i hz.1) hz.1.1
  have hnorm := (abs_norm_sub_norm_le (f (Complex.exp z)) (Complex.exp (G.toFun z))).trans herr
  rw [Complex.norm_exp] at hnorm
  linarith [(abs_le.mp hnorm).2, Real.exp_le_exp.mpr (hbound n i z hz)]

#print axioms fullSlice_subset_literal_tract
#print axioms exists_uniform_starred_endpiece_bound
#print axioms starred_endpiece_norm_bound

end

end MaxModulusPoints.Construction
