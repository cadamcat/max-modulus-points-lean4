module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import MaxModulusPoints.StripEstimates.BoundaryMaximum

/-!
# Finite exceptional sets in harmonic comparison

Logarithmic barriers remove finitely many exceptional boundary points from the
maximum principle. This supplies the endpoint argument used in the rectangle
and half-disc comparisons of Pardo-Simón–Sixsmith, Section 4.
-/


@[expose] public section

open Set Filter Metric Topology InnerProductSpace

namespace MaxModulusPoints.StripEstimates

/-- The maximum principle for a harmonic function bounded above on a bounded
connected open domain, allowing finitely many exceptional boundary points. -/
theorem harmonic_le_of_boundary_limsup_except_finite {U : Set ℂ}
    (hopen : IsOpen U) (hconn : IsPreconnected U) (hbounded : Bornology.IsBounded U)
    (E : Finset ℂ) :
    (E : Set ℂ) ⊆ frontier U →
    ∀ {u : ℂ → ℝ} {C : ℝ}, HarmonicOnNhd u U → BddAbove (u '' U) →
      (∀ p ∈ frontier U, p ∉ E → ∀ b : ℝ, C < b →
        ∀ᶠ z in 𝓝[U] p, u z < b) →
      ∀ z ∈ U, u z ≤ C := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    intro _ u C hu _ hboundary
    exact harmonic_le_of_boundary_limsup hopen hconn hbounded hu
      (fun p hp => hboundary p hp (by simp))
  | @insert p E hpE ih =>
    intro hE u C hu hub hboundary
    have hpfront : p ∈ frontier U := hE (by simp)
    have hpnotU : p ∉ U := by
      intro hpU
      exact hpfront.2 (by simpa only [hopen.interior_eq] using hpU)
    have hEfront : (E : Set ℂ) ⊆ frontier U := by
      intro q hq
      exact hE (Finset.mem_insert_of_mem hq)
    obtain ⟨R, hRpos, hR⟩ := hbounded.exists_pos_norm_le
    have hne (z : ℂ) (hz : z ∈ U) : z - p ≠ 0 := by
      intro hzp
      exact hpnotU (sub_eq_zero.mp hzp ▸ hz)
    have hdist (z : ℂ) (hz : z ∈ U) : ‖z - p‖ ≤ R + ‖p‖ := by
      calc
        ‖z - p‖ ≤ ‖z‖ + ‖p‖ := norm_sub_le z p
        _ ≤ R + ‖p‖ := by linarith [hR z hz]
    let l : ℂ → ℝ := fun z => Real.log ‖z - p‖ - Real.log (R + ‖p‖)
    have hlharmonic : HarmonicOnNhd l U := by
      intro z hz
      exact ((analyticAt_id.sub analyticAt_const).harmonicAt_log_norm (hne z hz)).sub
        (harmonicAt_const _)
    have hlle (z : ℂ) (hz : z ∈ U) : l z ≤ 0 :=
      sub_nonpos.mpr (Real.log_le_log (norm_pos_iff.mpr (hne z hz)) (hdist z hz))
    obtain ⟨M, hM⟩ := hub
    have hMbound (z : ℂ) (hz : z ∈ U) : u z ≤ M := hM ⟨z, hz, rfl⟩
    have hperturb (ε : ℝ) (hε : 0 < ε) :
        ∀ z ∈ U, u z + ε * l z ≤ C := by
      have hharmonic : HarmonicOnNhd (fun z => u z + ε * l z) U := by
        simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul] using
          hu.add (hlharmonic.const_smul (c := ε))
      refine ih hEfront hharmonic ⟨M, ?_⟩ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact (add_le_of_nonpos_right
          (mul_nonpos_of_nonneg_of_nonpos hε.le (hlle z hz))).trans (hMbound z hz)
      · intro q hqfront hqE b hCb
        by_cases hqp : q = p
        · subst q
          have hnorm : Tendsto (fun z : ℂ => ‖z - p‖) (𝓝[U] p) (𝓝[>] (0 : ℝ)) := by
            refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
            · have hc : ContinuousAt (fun z : ℂ => ‖z - p‖) p := by fun_prop
              simpa only [sub_self, norm_zero] using
                hc.tendsto.mono_left nhdsWithin_le_nhds
            · filter_upwards [self_mem_nhdsWithin] with z hz
              exact norm_pos_iff.mpr (hne z hz)
          have hlog := Real.tendsto_log_nhdsGT_zero.comp hnorm
          have hnear := hlog.eventually
            (eventually_lt_atBot ((b - M) / ε + Real.log (R + ‖p‖)))
          filter_upwards [hnear, self_mem_nhdsWithin] with z hzlog hz
          change Real.log ‖z - p‖ < (b - M) / ε + Real.log (R + ‖p‖) at hzlog
          have hlb : l z < (b - M) / ε := by dsimp [l]; linarith
          have hmul := (lt_div_iff₀ hε).mp hlb
          nlinarith [hMbound z hz]
        · have hqnot : q ∉ insert p E := by simp only [Finset.mem_insert]; tauto
          filter_upwards [hboundary q hqfront hqnot b hCb, self_mem_nhdsWithin]
            with z hzbound hz
          exact (add_le_of_nonpos_right
            (mul_nonpos_of_nonneg_of_nonpos hε.le (hlle z hz))).trans_lt hzbound
    intro z hz
    have hlim : Tendsto (fun ε : ℝ => u z + ε * l z) (𝓝[>] (0 : ℝ)) (𝓝 (u z)) := by
      have hc : ContinuousAt (fun ε : ℝ => u z + ε * l z) 0 := by fun_prop
      simpa only [zero_mul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hperturb ε hε z hz

end MaxModulusPoints.StripEstimates
