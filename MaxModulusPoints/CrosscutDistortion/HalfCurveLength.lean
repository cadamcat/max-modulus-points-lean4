module

public import MaxModulusPoints.CrosscutDistortion.PotentialSpeed
public import MaxModulusPoints.CrosscutDistortion.SlabPotentials

/-!
# Weighted length of a half-crosscut

A curve starting on the real axis and meeting the core of a vertical slab
has weighted length at least one half if its roof potential tends to zero
at the other endpoint. No endpoint limit of the curve itself is required.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set Filter MeasureTheory
open scoped Topology

/-- A half-curve crossing the slab core and escaping its roof potential
has slab-weighted length at least one half. -/
theorem half_curve_weighted_length (a b H : ℝ) (hH : 0 < H) (γ : ℝ → ℂ)
    (hγ : ∀ d ∈ Ico (0 : ℝ) H, ContDiffOn ℝ 1 γ (uIcc 0 d))
    (hspeed : IntervalIntegrable (slabWeightedSpeed a b γ) volume 0 H)
    (hreal : (γ 0).im = 0)
    (hroof : Tendsto (fun t => slabRoofPotential a b (γ t)) (𝓝[<] H) (𝓝 0))
    (hcore : ∃ c ∈ Ico (0 : ℝ) H,
      (γ c).re ∈ Icc a b ∧ |(γ c).im| ≤ 1 / 2) :
    1 / 2 ≤ ∫ t in 0..H, slabWeightedSpeed a b γ t := by
  obtain ⟨c, hc, hcx, hcy⟩ := hcore
  have hvalues := slab_potentials_core_values_abs a b (γ c) hcx hcy
  have hbase : slabBasePotential a b (γ 0) = 0 := by
    unfold slabBasePotential
    rw [hreal, abs_zero]
    exact max_eq_left (min_le_left _ _)
  have hint (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ H) :
      IntervalIntegrable (slabWeightedSpeed a b γ) volume u v := by
    apply hspeed.mono_set
    rw [uIcc_of_le huv, uIcc_of_le hH.le]
    exact Icc_subset_Icc hu hv
  have hfirst := (slab_potential_increments_le_integral a b 0 c hc.1 γ
    (hγ c hc) (hint 0 c le_rfl hc.1 hc.2.le)).1
  rw [hbase, sub_zero, abs_of_nonneg (slab_potentials_nonneg a b (γ c)).1]
    at hfirst
  have hevent : ∀ᶠ t in 𝓝[<] H,
      1 / 2 ≤ (∫ u in 0..H, slabWeightedSpeed a b γ u) +
        slabRoofPotential a b (γ t) := by
    filter_upwards [Ioo_mem_nhdsLT hc.2] with t ht
    have ht0 : 0 ≤ t := hc.1.trans ht.1.le
    have hct : uIcc c t ⊆ uIcc 0 t := by
      rw [uIcc_of_le ht.1.le, uIcc_of_le ht0]
      exact Icc_subset_Icc hc.1 le_rfl
    have hsecond := (slab_potential_increments_le_integral a b c t ht.1.le γ
      ((hγ t ⟨ht0, ht.2⟩).mono hct) (hint c t hc.1 ht.1.le ht.2.le)).2
    have hsecond' : slabRoofPotential a b (γ c) - slabRoofPotential a b (γ t) ≤
        ∫ u in c..t, slabWeightedSpeed a b γ u := by
      linarith [neg_le_abs (slabRoofPotential a b (γ t) - slabRoofPotential a b (γ c))]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hint 0 c le_rfl hc.1 hc.2.le) (hint c t hc.1 ht.1.le ht.2.le)
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) H)]
        slabWeightedSpeed a b γ := by
      exact Eventually.of_forall fun u => by
        unfold slabWeightedSpeed
        split_ifs <;> positivity
    have hmono := intervalIntegral.integral_mono_interval le_rfl ht0 ht.2.le
      hnonneg hspeed
    linarith [hvalues.1, hvalues.2]
  have hlimit : Tendsto
      (fun t => (∫ u in 0..H, slabWeightedSpeed a b γ u) + slabRoofPotential a b (γ t))
      (𝓝[<] H) (𝓝 ((∫ u in 0..H, slabWeightedSpeed a b γ u) + 0)) :=
    tendsto_const_nhds.add hroof
  simpa only [add_zero] using ge_of_tendsto hlimit hevent

end MaxModulusPoints.CrosscutDistortion
