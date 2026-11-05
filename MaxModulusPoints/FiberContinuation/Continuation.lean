module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.Basic
public import MaxModulusPoints.FiberContinuation.CompleteBranches
public import MaxModulusPoints.FiberContinuation.NonconstantBranches
public import MaxModulusPoints.FiberContinuation.OmittedContinuation
public import MaxModulusPoints.FiberContinuation.ValueCoordinates

/-!
# Openness of the high-count product projection

Each spherical point of the high-count closure lies on a complete analytic
physical branch. Nonconstant reflected products force its product coordinate
to be nonconstant as a germ, so the open mapping theorem gives a neighborhood
in the product projection.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint.Packages

open Set Filter Metric
open scoped Topology

/-- Complete physical branches and the open mapping theorem continue the
high-count closure through every spherical value. -/
theorem high_count_continuation_proof {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ)
    (hsmall : SmallCoordinateBound d L) (hnonconstant : NonconstantProducts d) :
    IsOpen (Prod.fst '' closure (highRegularTargets d L)) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro s ⟨y, hy, hys⟩
  obtain ⟨ρ, hρ, hbound⟩ := FiberContinuation.exists_product_norm_lower_bound d L hsmall
  have hs : y.1 ≠ 0 := by
    intro hzero
    have hnorm := hbound y hy
    rw [hzero, norm_zero] at hnorm
    exact (not_le_of_gt hρ) hnorm
  obtain ⟨B⟩ := FiberContinuation.exists_complete_high_branch d L hsmall hy
  have hopen : 𝓝 (B.productFunction 0) ≤ map B.productFunction (𝓝 0) :=
    B.analyticAt_productFunction.eventually_constant_or_nhds_le_map_nhds.resolve_left (by
      simpa only [B.productFunction_zero] using B.not_eventually_constant_product hs hnonconstant)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℂ),
      B.productFunction t ∈ Prod.fst '' closure (highRegularTargets d L) := by
    filter_upwards [ball_mem_nhds 0 B.radius_pos] with t ht
    exact ⟨(B.productFunction t, FiberContinuation.centeredValue y.2 (t ^ B.exponent)), B.high t ht, rfl⟩
  have hmap : ∀ᶠ z in map B.productFunction (𝓝 0),
      z ∈ Prod.fst '' closure (highRegularTargets d L) := by
    simpa only [Filter.eventually_map] using hmem
  have hnhds := hmap.filter_mono hopen
  rwa [B.productFunction_zero, hys] at hnhds

end MaxModulusPoints.Blueprint.Packages
