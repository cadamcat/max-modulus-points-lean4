module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Maps.Proper.Basic
public import MaxModulusPoints.Blueprint.Data

/-!
# The excluded small-product cylinder

A uniform small-coordinate bound excludes high-count fibers near product zero.
The exclusion persists under closure, and compactness of the spherical value
space makes the product projection closed.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set
open MaxModulusPoints.Blueprint

variable {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ)

/-- If the product is small, every pair has a small coordinate. -/
theorem fiber_subset_small_coordinates (ε : ℝ) (hε : 0 < ε)
    (s : ℂ) (q : OnePoint ℂ) (hs : ‖s‖ < ε ^ 2) :
    physicalFiber d s q ⊆
      {v ∈ physicalFiber d s q | ‖v.1‖ < ε ∨ ‖v.2‖ < ε} := by
  intro v hv
  refine ⟨hv, ?_⟩
  by_contra h
  have hz : ε ≤ ‖v.1‖ := le_of_not_gt (fun hz => h (Or.inl hz))
  have hw : ε ≤ ‖v.2‖ := le_of_not_gt (fun hw => h (Or.inr hw))
  have hprod : ε ^ 2 ≤ ‖s‖ := by
    rw [← hv.1, norm_mul, pow_two]
    exact mul_le_mul hz hw hε.le (norm_nonneg _)
  exact (not_lt_of_ge hprod) hs

/-- Li's small-product bound, uniformly in every spherical common value. -/
theorem exists_small_product_bound (hsmall : SmallCoordinateBound d L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (s : ℂ) (q : OnePoint ℂ), s ≠ 0 → ‖s‖ < ρ →
      (physicalFiber d s q).encard ≤ (L : ℕ∞) := by
  obtain ⟨ε, hε, hbound⟩ := hsmall
  refine ⟨ε ^ 2, sq_pos_of_pos hε, ?_⟩
  intro s q hs hnorm
  exact (encard_mono (fiber_subset_small_coordinates d ε hε s q hnorm)).trans
    (hbound s q hs)

/-- The entire closure of high-count regular targets misses a product cylinder. -/
theorem exists_product_norm_lower_bound (hsmall : SmallCoordinateBound d L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v ∈ closure (highRegularTargets d L), ρ ≤ ‖v.1‖ := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_small_product_bound d L hsmall
  refine ⟨ρ, hρ, ?_⟩
  apply closure_minimal
  · intro v hv
    by_contra h
    exact (not_le_of_gt hv.2.choose_spec.2.2.2)
      (hbound v.1 v.2 hv.1 (lt_of_not_ge h))
  · exact isClosed_le continuous_const (continuous_fst.norm)

/-- Zero cannot be in the product projection, even after spherical closure. -/
theorem zero_not_mem_high_count_projection (hsmall : SmallCoordinateBound d L) :
    (0 : ℂ) ∉ Prod.fst '' closure (highRegularTargets d L) := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_product_norm_lower_bound d L hsmall
  rintro ⟨v, hv, hzero⟩
  have := hbound v hv
  rw [hzero, norm_zero] at this
  exact (not_le_of_gt hρ) this

/-- The spherical value factor is compact, so the product projection is closed. -/
theorem isClosed_high_count_projection :
    IsClosed (Prod.fst '' closure (highRegularTargets d L)) :=
  isClosedMap_fst_of_compactSpace _ isClosed_closure

/-- An open high-count projection would be clopen and omit zero, hence empty. -/
theorem high_count_projection_eq_empty (hsmall : SmallCoordinateBound d L)
    (hopen : IsOpen (Prod.fst '' closure (highRegularTargets d L))) :
    Prod.fst '' closure (highRegularTargets d L) = ∅ := by
  have hclopen : IsClopen (Prod.fst '' closure (highRegularTargets d L)) :=
    ⟨isClosed_high_count_projection d L, hopen⟩
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · exact hempty
  · exact False.elim (zero_not_mem_high_count_projection d L hsmall
      (huniv.symm ▸ mem_univ 0))

/-- The excluded cylinder and an open projection rule out every high target. -/
theorem high_regular_targets_eq_empty (hsmall : SmallCoordinateBound d L)
    (hopen : IsOpen (Prod.fst '' closure (highRegularTargets d L))) :
    highRegularTargets d L = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hmem : v.1 ∈ Prod.fst '' closure (highRegularTargets d L) :=
    ⟨v, subset_closure hv, rfl⟩
  rw [high_count_projection_eq_empty d L hsmall hopen] at hmem
  exact hmem

end MaxModulusPoints.FiberContinuation
