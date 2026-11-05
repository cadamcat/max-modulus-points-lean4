module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.Stabilization

/-!
# Counts in finite analytic physical families

Stabilized analytic comparisons give constant physical counts on a punctured
parameter disk. Whole-image regularity prevents the central physical fiber
from being larger than the nearby one.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

universe u

/-- Product filters and physical equality kernels stabilize simultaneously. -/
theorem analytic_physical_counts_stabilize {ι : Type u} [Finite ι]
    (P : ι → ℂ → ℂ × ℂ) (hP : ∀ i, AnalyticAt ℂ (P i) 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j t u, t ∈ ball 0 δ → t ≠ 0 →
      u ∈ ball 0 δ → u ≠ 0 →
      ((fun i => P i t) '' {i | (P i t).1 * (P i t).2 =
        (P j t).1 * (P j t).2}).encard =
      ((fun i => P i u) '' {i | (P i u).1 * (P i u).2 =
        (P j u).1 * (P j u).2}).encard := by
  let S : ι → ℂ → ℂ := fun i t => (P i t).1 * (P i t).2
  have hS : ∀ i, AnalyticAt ℂ (S i) 0 := fun i =>
    (analyticAt_fst.comp (hP i)).mul (analyticAt_snd.comp (hP i))
  obtain ⟨δP, hδP, hpair⟩ := analytic_family_stabilizes P hP
  obtain ⟨δS, hδS, hprod⟩ := analytic_family_stabilizes S hS
  refine ⟨min δP δS, lt_min hδP hδS, ?_⟩
  intro j t u ht ht0 hu hu0
  have htP := ball_subset_ball (min_le_left δP δS) ht
  have htS := ball_subset_ball (min_le_right δP δS) ht
  have huP := ball_subset_ball (min_le_left δP δS) hu
  have huS := ball_subset_ball (min_le_right δP δS) hu
  apply physical_counts_eq_of_stabilized_comparisons
  · intro i
    exact (hprod i j t htS ht0).1.trans (hprod i j u huS hu0).1.symm
  · intro i k
    exact (hpair i k t htP ht0).1.trans (hpair i k u huP hu0).1.symm

/-- At a whole-image graph point, distinct central physical pairs remain
distinct in the nearby physical fiber. Exact enumeration is needed only at
the center; forward validity suffices for the nearby lower bound. -/
theorem central_fiber_count_le_nearby {f : ℂ → ℂ} (d : NormalizedFunction f)
    {ι : Type u} [Finite ι] (P : ι → ℂ → ℂ × ℂ)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0) (q : ℂ → ℂ)
    (hq : ContinuousAt q 0) (s₀ : ℂ)
    (hregular : RegularTarget d s₀ (q 0))
    (hcenter : physicalFiber d s₀ ((q 0 : ℂ) : OnePoint ℂ) =
      range (fun i => P i 0))
    (hvalid : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ),
      P i t ∈ physicalFiber d ((P i t).1 * (P i t).2) ((q t : ℂ) : OnePoint ℂ))
    (j : ι) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      (physicalFiber d s₀ ((q 0 : ℂ) : OnePoint ℂ)).encard ≤
        (physicalFiber d ((P j t).1 * (P j t).2) ((q t : ℂ) : OnePoint ℂ)).encard := by
  obtain ⟨U, W, ψ, hU, hW, hsU, hqW, _, _, _, _, hgraph⟩ := hregular
  have hcentral (i : ι) : (P i 0).1 * (P i 0).2 = s₀ := by
    have hmem : P i 0 ∈ physicalFiber d s₀ ((q 0 : ℂ) : OnePoint ℂ) := by
      rw [hcenter]
      exact mem_range_self i
    exact hmem.1
  have hprodU : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ), (P i t).1 * (P i t).2 ∈ U := by
    intro i
    have hc := (hP i).continuousAt.fst.mul (hP i).continuousAt.snd
    apply hc.eventually
    apply hU.mem_nhds
    change (P i 0).1 * (P i 0).2 ∈ U
    rw [hcentral i]
    exact hsU
  have hqevent : ∀ᶠ t in 𝓝 (0 : ℂ), q t ∈ W := hq.eventually (hW.mem_nhds hqW)
  obtain ⟨δ, hδ, hpairs⟩ := analytic_family_stabilizes P hP
  have hball : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball 0 δ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds 0 hδ)
  have hallvalid : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ i,
      P i t ∈ physicalFiber d ((P i t).1 * (P i t).2) ((q t : ℂ) : OnePoint ℂ) :=
    (eventually_all.mpr hvalid).filter_mono nhdsWithin_le_nhds
  have hallU : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ i, (P i t).1 * (P i t).2 ∈ U :=
    (eventually_all.mpr hprodU).filter_mono nhdsWithin_le_nhds
  have hallW : ∀ᶠ t in 𝓝[≠] (0 : ℂ), q t ∈ W :=
    hqevent.filter_mono nhdsWithin_le_nhds
  filter_upwards [hball, eventually_mem_nhdsWithin, hallvalid, hallU, hallW]
    with t ht ht0 hv htU htW
  have hsame (i : ι) : (P i t).1 * (P i t).2 = (P j t).1 * (P j t).2 := by
    exact ((hgraph _ (htU i) _ htW).mp ⟨P i t, hv i⟩).trans
      ((hgraph _ (htU j) _ htW).mp ⟨P j t, hv j⟩).symm
  rw [hcenter, ← image_univ]
  apply (encard_image_le_of_kernel_imp (fun i => P i 0) (fun i => P i t) univ
    (fun i _ k _ heq => (hpairs i k t ht ht0).2 heq)).trans
  apply encard_mono
  rintro v ⟨i, _, rfl⟩
  simpa only [hsame i] using hv i

end MaxModulusPoints.FiberContinuation
