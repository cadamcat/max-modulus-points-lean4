import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
import MaxModulusPoints.Blueprint.Interfaces.RectangleBarriers
import MaxModulusPoints.Blueprint.Interfaces.StripMapData
import MaxModulusPoints.Construction.ClosedChamberGeometry
import MaxModulusPoints.Construction.ClosedGate
import MaxModulusPoints.Construction.Maxima
import MaxModulusPoints.Construction.OpenGateComparison
import MaxModulusPoints.Construction.PassageLower
import MaxModulusPoints.Construction.Tract
import MaxModulusPoints.Construction.TractMembership
/-!
# Strict comparison at almost closed gates

Pardo-Simón–Sixsmith, Proposition 4.3, compares each almost closed chamber
with a passage witness. A sufficiently large initial gap supplies a common
passage floor, and the rectangle bound supplies the chamber ceiling.
The strict margin survives the uniform approximation error.
-/

namespace MaxModulusPoints.Construction

open Set

noncomputable section

theorem chamber_interior_subset_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex) (j : Bool)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) :
    interior (Blueprint.chamber p i j) ⊆ Blueprint.tract p δ := by
  cases j
  · intro z hz
    have heq : Blueprint.chamber p i false =
        Complex.conjCLE.toHomeomorph ⁻¹' Blueprint.chamber p i true := by
      ext w
      simp [Blueprint.chamber, Blueprint.sideSign]
    rw [heq, ← Complex.conjCLE.toHomeomorph.preimage_interior] at hz
    have hstar : star z ∈ Blueprint.tract p δ := upper_chamber_interior_subset_tract p δ i hz
    simpa using G.symmetric_domain (star z) hstar
  · exact upper_chamber_interior_subset_tract p δ i

/-- The coarse approximation constant suffices when the real witness is
chosen high enough. -/
theorem passage_norm_floor {f G : ℂ → ℂ} {w : ℂ} {M : ℝ}
    (hw : ‖f (Complex.exp w) - Complex.exp (G w)‖ ≤ M)
    (hlower : Real.exp 1 + 2 * M + 2 ≤ (G w).re) :
    Real.exp 1 + M + 2 ≤ ‖f (Complex.exp w)‖ := by
  have h := (abs_norm_sub_norm_le (f (Complex.exp w)) (Complex.exp (G w))).trans hw
  rw [Complex.norm_exp] at h
  linarith [(abs_le.mp h).1, Real.add_one_le_exp (G w).re]

theorem closed_gate_norm_margin {f G : ℂ → ℂ} {z w : ℂ} {M : ℝ}
    (hz : ‖f (Complex.exp z) - Complex.exp (G z)‖ ≤ M)
    (hw : ‖f (Complex.exp w) - Complex.exp (G w)‖ ≤ M)
    (hchamber : (G z).re ≤ 1)
    (hpassage : Real.exp 1 + 2 * M + 2 ≤ (G w).re) :
    ‖f (Complex.exp z)‖ + 1 < ‖f (Complex.exp w)‖ := by
  apply approximation_preserves_norm_margin hw hz
  have h := Real.exp_le_exp.mpr hchamber
  linarith [Real.add_one_le_exp (G w).re]

/-- Choose the initial gap, then all almost-closed thresholds. The resulting
strict comparison is uniform over all admissible gate functions. -/
theorem exists_closed_gate_thresholds (hbottleneck : Blueprint.BottleneckEstimates)
    (hrectangle : Blueprint.RectangleBarriers) (ψ : Blueprint.StripMapData)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p : Blueprint.BlockParameters, R ≤ p.gap 0 →
      ∃ ε : Blueprint.GateIndex → ℝ,
        (∀ i, 0 < ε i ∧ ε i < Blueprint.gateUpper i) ∧
        ∀ (δ : Blueprint.GateIndex → ℝ),
          (∀ k, 0 < δ k ∧ δ k ≤ Blueprint.gateUpper k) →
        ∀ (G : Blueprint.LogModel (Blueprint.tract p δ)) (f : ℂ → ℂ),
          (∀ z ∈ Blueprint.tract p δ, 1 < ‖Complex.exp z‖ →
            ‖f (Complex.exp z) - Complex.exp (G.toFun z)‖ ≤ M / ‖Complex.exp z‖) →
          (∀ n, Real.exp 1 + M + 2 ≤
            ‖f (Complex.exp (Blueprint.slicePosition p n : ℝ))‖) ∧
          ∀ i, δ i ≤ ε i → ∀ j : Bool,
          ∀ z ∈ interior (Blueprint.chamber p i j), z.re = Blueprint.slicePosition p i.1 →
            ‖f (Complex.exp z)‖ + 1 <
              ‖f (Complex.exp (Blueprint.slicePosition p i.1 : ℝ))‖ := by
  obtain ⟨R, hR, hlower⟩ := exists_initial_gap_for_passage_lower ψ (Real.exp 1 + 2 * M + 2)
  refine ⟨R, hR, ?_⟩
  intro p hp
  choose ε hε hεu hεbound using fun i => exists_almost_closed_gate_threshold hbottleneck hrectangle ψ p i
  refine ⟨ε, fun i => ⟨hε i, hεu i⟩, ?_⟩
  intro δ hδ G f happrox
  have hpass (n : ℕ) : ((Blueprint.slicePosition p n : ℝ) : ℂ) ∈ Blueprint.passageSlice p n :=
    ⟨rfl, by simpa [passageHalfHeight, Blueprint.chamberBase] using passageHalfHeight_pos⟩
  have herr (n : ℕ) :
      ‖f (Complex.exp (Blueprint.slicePosition p n : ℝ)) -
        Complex.exp (G.toFun (Blueprint.slicePosition p n : ℝ))‖ ≤ M :=
    approximation_error_on_sample p n hM happrox
      (passageSlice_subset_tract p δ n (hpass n)) rfl
  have hvalue (n : ℕ) : Real.exp 1 + 2 * M + 2 ≤
      (G.toFun (Blueprint.slicePosition p n : ℝ)).re :=
    hlower p hp δ (fun i => (hδ i).2) G n
  refine ⟨fun n => passage_norm_floor (herr n) (hvalue n), ?_⟩
  intro i hi j z hz hx
  exact closed_gate_norm_margin
    (approximation_error_on_sample p i.1 hM happrox (chamber_interior_subset_tract p δ i j G hz) hx)
    (herr i.1) (hεbound i δ hδ hi G j z hz hx) (hvalue i.1)

/-- Keeping the real passage witness in a compact segment preserves the
strict margin after taking both compact maxima. -/
theorem compact_closed_gate_comparison (p : Blueprint.BlockParameters)
    (i : Blueprint.GateIndex) {f : ℂ → ℂ} (hf : Continuous f)
    {P C : Set ℂ} (hP : IsCompact P)
    (hpassage : ((Blueprint.slicePosition p i.1 : ℝ) : ℂ) ∈ P)
    (hC : IsCompact C) (hne : C.Nonempty)
    (hcomp : ∀ z ∈ C, ‖f (Complex.exp z)‖ + 1 <
      ‖f (Complex.exp (Blueprint.slicePosition p i.1 : ℝ))‖) :
    Blueprint.sliceMaximum C f + 1 < Blueprint.sliceMaximum P f := by
  have hcont : Continuous (logModulus f) := (hf.comp Complex.continuous_exp).norm
  obtain ⟨z, hz, he⟩ := exists_compactMaximum hC hne hcont.continuousOn
  change compactMaximum (logModulus f) C + 1 < compactMaximum (logModulus f) P
  rw [← he]
  exact (hcomp z hz).trans_le (le_compactMaximum hP hcont.continuousOn hpassage)

#print axioms passage_norm_floor
#print axioms closed_gate_norm_margin
#print axioms exists_closed_gate_thresholds
#print axioms compact_closed_gate_comparison

end

end MaxModulusPoints.Construction
