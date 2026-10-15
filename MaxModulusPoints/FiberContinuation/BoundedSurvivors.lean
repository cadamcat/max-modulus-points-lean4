import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Challenge
import MaxModulusPoints.FiberContinuation.CompactCapture
import MaxModulusPoints.FiberContinuation.FiniteCoordinates
import MaxModulusPoints.FiberContinuation.FiniteFibers
import MaxModulusPoints.FiberContinuation.LogarithmicValues
/-!
# Compact surviving physical pairs

A high-count fiber has a pair with both coordinates bounded away from zero.
A product bound therefore puts one surviving pair in a fixed compact annulus
product. Restricted compact capture and isolated zeros also hold at the value
at the origin; full-fiber properness is not needed for these statements.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

/-- The fixed compact annulus product for a bounded surviving pair. -/
def survivorCompact (ε S : ℝ) : Set (ℂ × ℂ) :=
  (closedBall 0 (S / ε) ×ˢ closedBall 0 (S / ε)) ∩
    {v | ε ≤ ‖v.1‖ ∧ ε ≤ ‖v.2‖}

theorem isCompact_survivorCompact (ε S : ℝ) : IsCompact (survivorCompact ε S) :=
  ((isCompact_closedBall (0 : ℂ) (S / ε)).prod (isCompact_closedBall (0 : ℂ) (S / ε))).inter_right
    ((isClosed_le continuous_const continuous_fst.norm).inter
      (isClosed_le continuous_const continuous_snd.norm))

/-- One uniform compact annulus product contains a surviving physical pair
whenever the product is bounded and the actual count exceeds the small-pair bound. -/
theorem exists_bounded_survivors {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ)
    (hsmall : SmallCoordinateBound d L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (S : ℝ) (s : ℂ) (q : OnePoint ℂ), s ≠ 0 → ‖s‖ ≤ S →
      (L : ℕ∞) < (physicalFiber d s q).encard →
      (physicalFiber d s q ∩ survivorCompact ε S).Nonempty := by
  obtain ⟨ε, hε, hbound⟩ := hsmall
  refine ⟨ε, hε, ?_⟩
  intro S s q hs hS hhigh
  by_contra hnone
  have hsubset : physicalFiber d s q ⊆
      {v ∈ physicalFiber d s q | ‖v.1‖ < ε ∨ ‖v.2‖ < ε} := by
    intro v hv
    refine ⟨hv, ?_⟩
    by_contra hsmallv
    have hz : ε ≤ ‖v.1‖ := le_of_not_gt (fun h => hsmallv (Or.inl h))
    have hw : ε ≤ ‖v.2‖ := le_of_not_gt (fun h => hsmallv (Or.inr h))
    have hprod : ‖v.1‖ * ‖v.2‖ = ‖s‖ := by rw [← norm_mul, hv.1]
    have hzupper : ‖v.1‖ ≤ S / ε := (le_div_iff₀ hε).mpr
      ((mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans (hprod.le.trans hS))
    have hwupper : ‖v.2‖ ≤ S / ε := by
      apply (le_div_iff₀ hε).mpr
      calc
        ‖v.2‖ * ε ≤ ‖v.2‖ * ‖v.1‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ = ‖s‖ := (mul_comm _ _).trans hprod
        _ ≤ S := hS
    exact hnone ⟨v, hv, ⟨by simpa using hzupper, by simpa using hwupper⟩, hz, hw⟩
  exact (not_le_of_gt hhigh) ((encard_mono hsubset).trans (hbound s q hs))

/-- A nowhere-zero analytic germ has only finitely many zeros in a compact set. -/
theorem finite_zeros_on_compact_of_not_eventually_zero {g : ℂ → ℂ} (hg : Entire g)
    (hnz : ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, g z = 0)
    (K : Set ℂ) (hK : IsCompact K) : {z ∈ K | g z = 0}.Finite := by
  by_contra hinfinite
  obtain ⟨a, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinfinite hK
    (fun _ hz => hz.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] a, g z = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono (fun _ hz => hz.2)
  exact hnz a ((hg.analyticAt a).frequently_zero_iff_eventually_zero.mp hfreq)

/-- Every nonzero-product fiber restricted to a compact pair set is finite,
including fibers at the value at the origin. -/
theorem finite_physicalFiber_inter_compact {f : ℂ → ℂ} (d : NormalizedFunction f)
    {s : ℂ} (hs : s ≠ 0) (q : OnePoint ℂ) (K : Set (ℂ × ℂ)) (hK : IsCompact K) :
    (physicalFiber d s q ∩ K).Finite := by
  apply Set.Finite.of_finite_image (f := Prod.fst)
    (hi := (injOn_fst_physicalFiber d hs q).mono inter_subset_left)
  have hcompact : IsCompact (Prod.fst '' (physicalFiber d s q ∩ K)) :=
    (hK.inter_left (isClosed_physicalFiber d s q)).image continuous_fst
  cases q using OnePoint.rec with
  | infty =>
    apply (finite_zeros_on_compact d.entire d.at_zero _ hcompact).subset
    rintro z ⟨v, hv, rfl⟩
    refine ⟨mem_image_of_mem Prod.fst hv, ?_⟩
    by_contra hzero
    have hvalue := hv.1.2.1
    simp [logarithmicValue, hzero] at hvalue
  | coe q =>
    apply (finite_zeros_on_compact_of_not_eventually_zero
      (entire_logarithmicEquation d.entire d.multiplicity q)
      (not_eventually_zero_logarithmicEquation d.entire d.at_zero d.nonconstant
        d.multiplicity q) _ hcompact).subset
    rintro z ⟨v, hv, rfl⟩
    refine ⟨mem_image_of_mem Prod.fst hv, ?_⟩
    have hgz : d.g v.1 ≠ 0 := by
      intro hzero
      have hvalue := hv.1.2.1
      simp [logarithmicValue, hzero] at hvalue
    apply (logarithmicEquation_eq_zero_iff d.multiplicity q hgz).mpr
    exact OnePoint.coe_injective
      (by simpa [logarithmicValue, hgz, finiteLogarithmicValue] using hv.1.2.1)

/-- Compact-restricted fibers are captured near every target, without excluding
the value at the origin. -/
theorem exists_neighborhood_capturing_compact_fiber {f : ℂ → ℂ}
    (d : NormalizedFunction f) (K : Set (ℂ × ℂ)) (hK : IsCompact K)
    (s : ℂ) (q : OnePoint ℂ) (O : Set (ℂ × ℂ)) (hO : IsOpen O)
    (hcover : physicalFiber d s q ∩ K ⊆ O) :
    ∃ W : Set (ℂ × OnePoint ℂ), IsOpen W ∧ (s, q) ∈ W ∧
      ∀ y ∈ W, physicalFiber d y.1 y.2 ∩ K ⊆ O := by
  let B : Set (ℂ × ℂ) := (K ∩ equalValuePairs d) ∩ Oᶜ
  have hB : IsCompact B :=
    (hK.inter_right (isClosed_equalValuePairs d)).inter_right hO.isClosed_compl
  have hbad : IsClosed (fiberTarget d '' B) :=
    (hB.image (continuous_fiberTarget d)).isClosed
  have hnotbad : (s, q) ∉ fiberTarget d '' B := by
    rintro ⟨v, hv, htarget⟩
    exact hv.2 (hcover ⟨(mem_physicalFiber_iff_target d v s q).mpr ⟨hv.1.2, htarget⟩, hv.1.1⟩)
  refine ⟨(fiberTarget d '' B)ᶜ, hbad.isOpen_compl, hnotbad, ?_⟩
  intro y hy v hv
  by_contra hvO
  obtain ⟨heq, htarget⟩ := (mem_physicalFiber_iff_target d v y.1 y.2).mp hv.1
  exact hy ⟨v, ⟨⟨hv.2, heq⟩, hvO⟩, htarget⟩

end MaxModulusPoints.FiberContinuation
