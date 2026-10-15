import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
import MaxModulusPoints.Blueprint.Interfaces.ClosedGateInterval
import MaxModulusPoints.Blueprint.Interfaces.Rectangle
import MaxModulusPoints.Blueprint.Interfaces.RectangleBarriers
import MaxModulusPoints.Blueprint.Interfaces.StripMapData
import MaxModulusPoints.Construction.BoundaryLimits
import MaxModulusPoints.Construction.ClosedChamberGeometry
import MaxModulusPoints.Construction.OpenChamberGeometry
import MaxModulusPoints.Construction.Tract
import MaxModulusPoints.Construction.UniformLeftBound
/-!
# Uniform estimates for almost closed gates

Pardo-Simón–Sixsmith, Proposition 4.3, first bounds the real part of the
logarithmic map on a fixed chamber rectangle. The rectangle barrier then
makes its full sample slice small, uniformly over all other gates.
-/

namespace MaxModulusPoints.Construction

open Set Filter
open scoped Topology

noncomputable section

theorem boundaryUpper_comp {U V : Set ℂ} {G T : ℂ → ℂ} {ζ : ℂ} {B : ℝ}
    (hT : ContinuousWithinAt T U ζ) (hUV : MapsTo T U V)
    (h : Blueprint.BoundaryUpper V G (T ζ) B) :
    Blueprint.BoundaryUpper U (G ∘ T) ζ B := by
  intro ε hε
  exact (hT.tendsto_nhdsWithin hUV).eventually (h ε hε)

/-- A fixed positive constant times the gate height controls the full upper
chamber sample slice. Both constants are independent of all gates. -/
theorem uniform_upper_chamber_gate_bound (hbottleneck : Blueprint.BottleneckEstimates)
    (hrectangle : Blueprint.RectangleBarriers) (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ (δ : Blueprint.GateIndex → ℝ),
        (∀ k, 0 < δ k ∧ δ k ≤ Blueprint.gateUpper k) →
        δ i ≤ chamberWidth i.1 / 8 →
        ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
        ∀ z ∈ interior (Blueprint.chamber p i true),
          z.re = Blueprint.slicePosition p i.1 → (G.toFun z).re ≤ B * K * δ i := by
  have hw := chamberWidth_pos i.1
  obtain ⟨K, hK, hbarrier⟩ := hrectangle (chamberWidth i.1) (chamberWidth i.1 / 2)
    (chamberWidth i.1 / 8) hw (by positivity) (by linarith) (by linarith)
  obtain ⟨B, hB, hleft⟩ := uniform_left_value_bound hbottleneck ψ p
    (Blueprint.blockPosition p i.1 + 1)
  refine ⟨B, K, hB, hK, ?_⟩
  intro δ hδ hsmall G z hz hx
  let T := chamberTranslation p i
  have hmap : MapsTo T (Blueprint.rectangle (chamberWidth i.1)) (Blueprint.tract p δ) :=
    fun w hwrect => upper_chamber_interior_subset_tract p δ i (chamberTranslation_mapsTo p i hwrect)
  have hdiff : DifferentiableOn ℂ (G.toFun ∘ T) (Blueprint.rectangle (chamberWidth i.1)) :=
    G.holomorphic.comp (differentiable_id.add_const _).differentiableOn hmap
  have hbound (w : ℂ) (hwrect : w ∈ Blueprint.rectangle (chamberWidth i.1)) :
      ((G.toFun ∘ T) w).re ≤ B := by
    apply hleft δ hδ G (T w) (hmap hwrect)
    change w.re + Blueprint.blockPosition p i.1 ≤ Blueprint.blockPosition p i.1 + 1
    linarith [hwrect.2.1]
  have hboundary (ζ : ℂ) (hζ : ζ ∈ frontier (Blueprint.rectangle (chamberWidth i.1)) \
      Blueprint.closedGateInterval (chamberWidth i.1 / 2) (δ i)) :
      Blueprint.BoundaryUpper (Blueprint.rectangle (chamberWidth i.1)) (G.toFun ∘ T) ζ 0 := by
    exact boundaryUpper_comp (chamberTranslation_continuous p i).continuousAt.continuousWithinAt
      hmap (logModel_boundaryUpper_of_not_mem G
        (chamberTranslation_boundary_not_mem_tract p δ (fun k => (hδ k).2) i hζ))
  let w := z - (⟨Blueprint.blockPosition p i.1, chamberBottom i.1 i.2⟩ : ℂ)
  have hzcoord := hz
  rw [upper_chamber_interior] at hzcoord
  have hwrect : w ∈ Blueprint.rectangle (chamberWidth i.1) := by
    change 0 < z.re - Blueprint.blockPosition p i.1 ∧
      z.re - Blueprint.blockPosition p i.1 < 1 ∧
      0 < z.im - chamberBottom i.1 i.2 ∧
      z.im - chamberBottom i.1 i.2 < chamberWidth i.1
    refine ⟨by linarith [hzcoord.1], by linarith [hzcoord.2.1],
      by linarith [hzcoord.2.2.1], ?_⟩
    dsimp [chamberBottom, chamberTop] at hzcoord ⊢
    linarith [hzcoord.2.2.2]
  have hwre : w.re = 1 / 4 := by
    change z.re - Blueprint.blockPosition p i.1 = 1 / 4
    dsimp [Blueprint.slicePosition] at hx
    linarith
  have h := hbarrier (δ i) B (hδ i).1 hsmall hB (G.toFun ∘ T) hdiff hbound hboundary
    w hwrect hwre
  simpa only [Function.comp_apply, T, chamberTranslation, w, sub_add_cancel] using h

/-- One positive threshold per chamber makes both reflected sample slices
have real part at most one, uniformly over every other gate parameter. -/
theorem exists_almost_closed_gate_threshold (hbottleneck : Blueprint.BottleneckEstimates)
    (hrectangle : Blueprint.RectangleBarriers) (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) :
    ∃ ε : ℝ, 0 < ε ∧ ε < Blueprint.gateUpper i ∧
      ∀ (δ : Blueprint.GateIndex → ℝ),
        (∀ k, 0 < δ k ∧ δ k ≤ Blueprint.gateUpper k) → δ i ≤ ε →
        ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
        ∀ j : Bool, ∀ z ∈ interior (Blueprint.chamber p i j),
          z.re = Blueprint.slicePosition p i.1 → (G.toFun z).re ≤ 1 := by
  obtain ⟨B, K, hB, hK, hbound⟩ := uniform_upper_chamber_gate_bound hbottleneck hrectangle ψ p i
  have hw := chamberWidth_pos i.1
  let ε := min (chamberWidth i.1 / 16) (1 / (2 * (B * K)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεwidth : ε ≤ chamberWidth i.1 / 16 := min_le_left _ _
  have hεprod : ε ≤ 1 / (2 * (B * K)) := min_le_right _ _
  refine ⟨ε, hε, ?_, ?_⟩
  · rw [gateUpper_eq_chamberWidth]
    linarith [chamberWidth_pos i.1]
  · intro δ hδ hδi G j z hz hx
    have hsmall : δ i ≤ chamberWidth i.1 / 8 := by
      linarith [hδi.trans hεwidth, chamberWidth_pos i.1]
    have hproduct : B * K * δ i ≤ 1 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2 * (B * K))).mp (hδi.trans hεprod)
      nlinarith
    have hupper : ∀ w ∈ interior (Blueprint.chamber p i true),
        w.re = Blueprint.slicePosition p i.1 → (G.toFun w).re ≤ 1 := by
      intro w hw hwre
      exact (hbound δ hδ hsmall G w hw hwre).trans hproduct
    cases j
    · have hreflect : star z ∈ interior (Blueprint.chamber p i true) := by
        have heq : Blueprint.chamber p i false =
            Complex.conjCLE.toHomeomorph ⁻¹' Blueprint.chamber p i true := by
          ext w
          simp [Blueprint.chamber, Blueprint.sideSign]
        rw [heq, ← Complex.conjCLE.toHomeomorph.preimage_interior] at hz
        exact hz
      have h := hupper (star z) hreflect (by simpa using hx)
      have hzV : z ∈ Blueprint.tract p δ := by
        simpa using G.symmetric_domain (star z) (upper_chamber_interior_subset_tract p δ i hreflect)
      rw [G.symmetric_map z hzV] at h
      simpa using h
    · exact hupper z hz hx

#print axioms uniform_upper_chamber_gate_bound
#print axioms exists_almost_closed_gate_threshold

end

end MaxModulusPoints.Construction
