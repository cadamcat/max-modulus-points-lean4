import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.FiberContinuation.LogarithmicValues
/-!
# Compact capture of physical fibers

Away from the value at the origin, both physical coordinates are uniformly
bounded below. A bounded product then bounds them above. Spherical continuity
turns these bounds into compact fibers and exact capture near each target.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

variable {f : ℂ → ℂ} (d : NormalizedFunction f)

/-- The product and common-value target of an actual pair. -/
def fiberTarget (v : ℂ × ℂ) : ℂ × OnePoint ℂ :=
  (v.1 * v.2, logarithmicValue d.multiplicity d.g v.1)

/-- The closed locus where the two actual spherical values agree. -/
def equalValuePairs : Set (ℂ × ℂ) :=
  {v | logarithmicValue d.multiplicity d.g v.1 =
    logarithmicValue d.multiplicity (reflected d.g) v.2}

theorem continuous_fiberTarget : Continuous (fiberTarget d) :=
  (continuous_fst.mul continuous_snd).prodMk
    ((continuous_logarithmicValue d.entire d.at_zero d.multiplicity).comp continuous_fst)

theorem isClosed_equalValuePairs : IsClosed (equalValuePairs d) :=
  isClosed_eq
    ((continuous_logarithmicValue d.entire d.at_zero d.multiplicity).comp continuous_fst)
    ((continuous_logarithmicValue (entire_reflected d.entire)
      (reflected_zero_ne d.at_zero) d.multiplicity).comp continuous_snd)

theorem mem_physicalFiber_iff_target (v : ℂ × ℂ) (s : ℂ) (q : OnePoint ℂ) :
    v ∈ physicalFiber d s q ↔ v ∈ equalValuePairs d ∧ fiberTarget d v = (s, q) := by
  constructor
  · intro hv
    exact ⟨hv.2.1.trans hv.2.2.symm, Prod.ext hv.1 hv.2.1⟩
  · rintro ⟨heq, htarget⟩
    have hs : v.1 * v.2 = s := congrArg Prod.fst htarget
    have hq : logarithmicValue d.multiplicity d.g v.1 = q := congrArg Prod.snd htarget
    exact ⟨hs, hq, heq.symm.trans hq⟩

theorem isClosed_physicalFiber (s : ℂ) (q : OnePoint ℂ) :
    IsClosed (physicalFiber d s q) := by
  have heq : physicalFiber d s q = equalValuePairs d ∩ fiberTarget d ⁻¹' {(s, q)} := by
    ext v
    exact mem_physicalFiber_iff_target d v s q
  rw [heq]
  exact (isClosed_equalValuePairs d).inter
    (isClosed_singleton.preimage (continuous_fiberTarget d))

/-- Nearby fibers away from the omitted value lie in one fixed annulus product. -/
theorem exists_local_annulus_capture (s₀ : ℂ) (q₀ : OnePoint ℂ)
    (hq₀ : q₀ ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)) :
    ∃ (ε R : ℝ) (W : Set (ℂ × OnePoint ℂ)), 0 < ε ∧ 0 < R ∧ IsOpen W ∧
      (s₀, q₀) ∈ W ∧ ∀ y ∈ W, ∀ v ∈ physicalFiber d y.1 y.2,
        ε ≤ ‖v.1‖ ∧ ε ≤ ‖v.2‖ ∧ ‖v.1‖ ≤ R ∧ ‖v.2‖ ≤ R := by
  obtain ⟨V, M, hV, hM, hqV, hmM, hdis⟩ := t2_separation hq₀
  have hA : ∀ᶠ z in 𝓝 (0 : ℂ), logarithmicValue d.multiplicity d.g z ∈ M := by
    apply (continuous_logarithmicValue d.entire d.at_zero d.multiplicity).continuousAt.eventually
    simpa [logarithmicValue, d.at_zero] using hM.mem_nhds hmM
  have hB : ∀ᶠ z in 𝓝 (0 : ℂ),
      logarithmicValue d.multiplicity (reflected d.g) z ∈ M := by
    apply (continuous_logarithmicValue (entire_reflected d.entire)
      (reflected_zero_ne d.at_zero) d.multiplicity).continuousAt.eventually
    simpa [logarithmicValue, reflected_zero_ne d.at_zero] using hM.mem_nhds hmM
  obtain ⟨ε, hε, hsmall⟩ := nhds_basis_ball.eventually_iff.mp (hA.and hB)
  let S : ℝ := ‖s₀‖ + 1
  have hS : 0 < S := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  refine ⟨ε, S / ε, ball s₀ 1 ×ˢ V, hε, div_pos hS hε, isOpen_ball.prod hV,
    ⟨mem_ball_self zero_lt_one, hqV⟩, ?_⟩
  intro y hy v hv
  have hz : ε ≤ ‖v.1‖ := by
    by_contra hz
    have hin : v.1 ∈ ball (0 : ℂ) ε := by simpa using lt_of_not_ge hz
    have hval : y.2 ∈ M := hv.2.1 ▸ (hsmall hin).1
    exact Set.disjoint_left.mp hdis hy.2 hval
  have hw : ε ≤ ‖v.2‖ := by
    by_contra hw
    have hin : v.2 ∈ ball (0 : ℂ) ε := by simpa using lt_of_not_ge hw
    have hval : y.2 ∈ M := hv.2.2 ▸ (hsmall hin).2
    exact Set.disjoint_left.mp hdis hy.2 hval
  have hyS : ‖y.1‖ ≤ S := by
    have hdist : ‖y.1 - s₀‖ < 1 := by simpa [dist_eq_norm] using hy.1
    calc
      ‖y.1‖ = ‖(y.1 - s₀) + s₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖y.1 - s₀‖ + ‖s₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖s₀‖ := add_le_add hdist.le le_rfl
      _ = S := add_comm _ _
  have hprod : ‖v.1‖ * ‖v.2‖ = ‖y.1‖ := by rw [← norm_mul, hv.1]
  refine ⟨hz, hw, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩
  · exact (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans (hprod.le.trans hyS)
  · calc
      ‖v.2‖ * ε ≤ ‖v.2‖ * ‖v.1‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = ‖y.1‖ := (mul_comm _ _).trans hprod
      _ ≤ S := hyS

/-- Every fiber at a value other than the omitted value is compact. -/
theorem isCompact_physicalFiber (s : ℂ) (q : OnePoint ℂ)
    (hq : q ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)) :
    IsCompact (physicalFiber d s q) := by
  obtain ⟨ε, R, W, _, _, _, hcenter, hbound⟩ := exists_local_annulus_capture d s q hq
  apply ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset
    (isClosed_physicalFiber d s q)
  intro v hv
  obtain ⟨_, _, hz, hw⟩ := hbound (s, q) hcenter v hv
  exact ⟨by simpa using hz, by simpa using hw⟩

/-- Any open neighborhood of the full central fiber captures every nearby
actual pair. This includes a target with empty central fiber. -/
theorem exists_neighborhood_capturing_fiber (s : ℂ) (q : OnePoint ℂ)
    (hq : q ≠ ((d.multiplicity : ℂ) : OnePoint ℂ))
    (O : Set (ℂ × ℂ)) (hO : IsOpen O) (hcover : physicalFiber d s q ⊆ O) :
    ∃ W : Set (ℂ × OnePoint ℂ), IsOpen W ∧ (s, q) ∈ W ∧
      ∀ y ∈ W, physicalFiber d y.1 y.2 ⊆ O := by
  obtain ⟨ε, R, U, _, _, hU, hcenter, hbound⟩ := exists_local_annulus_capture d s q hq
  let C : Set (ℂ × ℂ) := closedBall 0 R ×ˢ closedBall 0 R
  let B : Set (ℂ × ℂ) := (C ∩ equalValuePairs d) ∩ Oᶜ
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) R)
  have hB : IsCompact B :=
    (hC.inter_right (isClosed_equalValuePairs d)).inter_right hO.isClosed_compl
  have hbad : IsClosed (fiberTarget d '' B) :=
    (hB.image (continuous_fiberTarget d)).isClosed
  have hnotbad : (s, q) ∉ fiberTarget d '' B := by
    rintro ⟨v, hv, htarget⟩
    exact hv.2 (hcover ((mem_physicalFiber_iff_target d v s q).mpr ⟨hv.1.2, htarget⟩))
  refine ⟨U \ fiberTarget d '' B, hU.sdiff hbad, ⟨hcenter, hnotbad⟩, ?_⟩
  intro y hy v hv
  by_contra hvO
  obtain ⟨_, _, hz, hw⟩ := hbound y hy.1 v hv
  have hvC : v ∈ C := ⟨by simpa using hz, by simpa using hw⟩
  obtain ⟨heq, htarget⟩ := (mem_physicalFiber_iff_target d v y.1 y.2).mp hv
  exact hy.2 ⟨v, ⟨⟨hvC, heq⟩, hvO⟩, htarget⟩

end MaxModulusPoints.FiberContinuation
