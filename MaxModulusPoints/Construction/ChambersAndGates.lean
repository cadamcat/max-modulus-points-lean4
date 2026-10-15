import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
import MaxModulusPoints.Blueprint.Interfaces.HalfDiscBarriers
import MaxModulusPoints.Blueprint.Interfaces.KernelContinuity
import MaxModulusPoints.Blueprint.Interfaces.RectangleBarriers
import MaxModulusPoints.Blueprint.Interfaces.RempeApproximation
import MaxModulusPoints.Blueprint.Interfaces.StripMapData
import MaxModulusPoints.Blueprint.Interfaces.TractModels
import MaxModulusPoints.Challenge
import MaxModulusPoints.Construction.ClosedGateComparison
import MaxModulusPoints.Construction.FamilySegments
import MaxModulusPoints.Construction.LiteralSlices
import MaxModulusPoints.Construction.Maxima
import MaxModulusPoints.Construction.OpenChamberLocalization
import MaxModulusPoints.Construction.OpenGateComparison
import MaxModulusPoints.Construction.StarredBounds
import MaxModulusPoints.Construction.StarredSegments
import MaxModulusPoints.Construction.Tract
import MaxModulusPoints.Construction.TractMembership
/-!
# The chamber-and-gate shooting family

Pardo-Simón–Sixsmith, Propositions 4.1–4.4 and Lemma 4.5, construct
a continuous family with opposite gate-face inequalities. The strip,
bottleneck, barrier, conformal-model and approximation inputs are explicit.
All choices of tunnels, spacing, thresholds and starred segments precede
the choice of a gate parameter.
-/

namespace MaxModulusPoints.Blueprint.Packages

open Set
open Construction

noncomputable section

/-- Assemble the fixed compact slices and strict face estimates into the
shooting family used in Corollary 4.6. -/
theorem chambers_and_gates_proof
    (hmodels : TractModels) (hkernel : KernelContinuity)
    (happrox : RempeApproximation) (hstrip : Nonempty StripMapData)
    (hbottleneck : BottleneckEstimates) (hrectangle : RectangleBarriers)
    (hhalfdisc : HalfDiscBarriers) : Nonempty ShootingFamily := by
  classical
  obtain ⟨ψ⟩ := hstrip
  obtain ⟨M, hM, hrempe⟩ := happrox
  obtain ⟨τ, hτ, hopen⟩ := exists_open_gate_tunnels hbottleneck ψ hM.le
  obtain ⟨R, hR, hclosed⟩ := exists_closed_gate_thresholds hbottleneck hrectangle ψ hM.le
  let p : BlockParameters :=
    { gap := fun n => if n = 0 then R else 1
      tunnelHeight := τ
      gap_ge_one := by
        intro n
        split_ifs
        · exact hR
        · exact le_rfl
      tunnel_pos := fun n => (hτ n).1
      tunnel_le_quarter := fun n => (hτ n).2 }
  have hp : R ≤ p.gap 0 := by simp [p]
  obtain ⟨ε, hε, hclosed⟩ := hclosed p hp
  obtain ⟨q, hcentres, hendpieces⟩ := exists_uniform_starred_endpiece_bound hbottleneck hhalfdisc ψ p
    (upperChamberCentre p) (upperChamberCentre_mem_fullSlice p)
  have hεbounds : ∀ i, 0 < ε i ∧ ε i ≤ gateUpper i := fun i => ⟨(hε i).1, (hε i).2.le⟩
  have hadmissible (δ : ParameterBox ε gateUpper) :
      ∀ i, 0 < (δ i : ℝ) ∧ (δ i : ℝ) ≤ gateUpper i :=
    fun i => ⟨(hε i).1.trans_le (δ i).2.1, (δ i).2.2⟩
  let G : ∀ δ : ParameterBox ε gateUpper, LogModel (tract p (fun i => (δ i : ℝ))) :=
    fun δ => Classical.choice (hmodels p (fun i => (δ i : ℝ)) (hadmissible δ))
  obtain ⟨hdom, hk⟩ := hkernel p ε hεbounds G
  obtain ⟨F, hentire, hcontinuous, hsym, herror, houtside⟩ :=
    hrempe p ε hεbounds G hdom (fun δ => (hk δ).1) (fun δ => (hk δ).2.1)
  have hclosedFacts (δ : ParameterBox ε gateUpper) :=
    hclosed (fun i => (δ i : ℝ)) (hadmissible δ) (G δ) (F δ) (herror δ)
  have hopenFacts (δ : ParameterBox ε gateUpper) :=
    hopen p (fun _ => le_rfl) (fun i => (δ i : ℝ)) (hadmissible δ) (G δ) (F δ) (herror δ)
  have hpassageSubset (n : ℕ) : familySegment p q n none ⊆ passageSlice p n := by
    rw [← fullSlice_passage p n]
    exact starSlice_subset_full _ _ _ _
  refine ⟨{
    lower := ε
    upper := gateUpper
    lower_lt_upper := fun i => (hε i).2
    F := F
    entire := fun δ => (hentire δ).1
    not_monomial := fun δ => (hentire δ).2
    locally_uniform := hcontinuous
    x := slicePosition p
    x_escape := (blockParametersLayout p).sample_tendsto
    segment := familySegment p q
    compact_segment := familySegment_compact p q
    nonempty_segment := familySegment_nonempty p q
    vertical_segment := fun n i z hz => familySegment_vertical p q n i hz
    disjoint_images := fun n i j hij => familySegment_disjoint_images p q n hij
    reflected_maxima := fun δ n m => familySegment_reflected_maxima p q (F δ) (hsym δ) n m
    floor := Real.exp 1 + M + 2
    ceiling := Real.exp 1 + M + 1
    ceiling_lt_floor := by linarith
    passage_lower := ?_
    outside_upper := ?_
    open_gate := ?_
    closed_gate := ?_ }⟩
  · intro δ n
    have hnorm := (hclosedFacts δ).1 n
    have hmax : ‖F δ (Complex.exp (slicePosition p n : ℝ))‖ ≤
        sliceMaximum (familySegment p q n none) (F δ) :=
      le_compactMaximum (familySegment_compact p q n none)
        (((hentire δ).1.continuous.comp Complex.continuous_exp).norm.continuousOn)
        (real_sample_mem_starSlice p q n)
    exact hnorm.trans hmax
  · intro δ n z hz hstar
    have hb := circle_outside_starred_bound p q (fun i => (δ i : ℝ))
      (fun i => (δ i).2.2) (G δ) hM.le (F δ) (herror δ) (houtside δ)
      (hendpieces _ (hadmissible δ) (G δ)) n hz (by
        rwa [← familySegment_exp_union p q n])
    linarith
  · intro i δ hi
    have hcomp := compact_open_gate_comparison p i (hentire δ).1.continuous
      (familySegment_compact p q i.1 none) (familySegment_nonempty p q i.1 none)
      (hpassageSubset i.1) (familySegment_compact p q i.1 (some (i.2, true)))
      (hcentres i) (hopenFacts δ i hi)
    linarith
  · intro i δ hi
    have hcomp := compact_closed_gate_comparison p i (hentire δ).1.continuous
      (familySegment_compact p q i.1 none) (real_sample_mem_starSlice p q i.1)
      (familySegment_compact p q i.1 (some (i.2, true)))
      (familySegment_nonempty p q i.1 (some (i.2, true))) (fun z hz =>
        (hclosedFacts δ).2 i hi.le true z
          (upper_fullSlice_subset_chamber_interior p i (starSlice_subset_full _ _ _ _ hz)) hz.1)
    linarith

#print axioms chambers_and_gates_proof

end

end MaxModulusPoints.Blueprint.Packages
