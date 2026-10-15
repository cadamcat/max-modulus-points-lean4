import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
/-!
# Modulus maxima on fixed compact slices

The compact-slice continuity step in Pardo-Simón–Sixsmith, Lemma 4.5.
Local uniform dependence of the functions is an explicit hypothesis.
-/

open Set Filter
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

/-- The largest modulus on a set in logarithmic coordinates. -/
noncomputable def logSliceMaximum (σ : Set ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖f (Complex.exp z)‖) '' σ)

/-- The maximum on a nonempty compact slice is attained. -/
theorem logSliceMaximum_attained {σ : Set ℂ} (hσ : IsCompact σ)
    (hne : σ.Nonempty) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Complex.exp '' σ)) :
    ∃ z ∈ σ, logSliceMaximum σ f = ‖f (Complex.exp z)‖ ∧
      ∀ w ∈ σ, ‖f (Complex.exp w)‖ ≤ ‖f (Complex.exp z)‖ := by
  exact hσ.exists_sSup_image_eq_and_ge hne
    ((hf.comp Complex.continuous_exp.continuousOn (mapsTo_image _ _)).norm)

/-- A uniform modulus error bounds the error between the two slice maxima. -/
theorem logSliceMaximum_stability {σ : Set ℂ} (hσ : IsCompact σ)
    (hne : σ.Nonempty) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (Complex.exp '' σ))
    (hg : ContinuousOn g (Complex.exp '' σ)) {ε : ℝ}
    (hfg : ∀ z ∈ σ, ‖f (Complex.exp z) - g (Complex.exp z)‖ ≤ ε) :
    |logSliceMaximum σ f - logSliceMaximum σ g| ≤ ε := by
  obtain ⟨z, hz, hfz, hmaxf⟩ := logSliceMaximum_attained hσ hne hf
  obtain ⟨w, hw, hgw, hmaxg⟩ := logSliceMaximum_attained hσ hne hg
  rw [hfz, hgw, abs_le]
  constructor
  · have h₁ := hmaxf w hw
    have h₂ := norm_sub_norm_le (g (Complex.exp w)) (f (Complex.exp w))
    have h₃ := hfg w hw
    rw [norm_sub_rev] at h₂
    linarith
  · have h₁ := hmaxg z hz
    have h₂ := norm_sub_norm_le (f (Complex.exp z)) (g (Complex.exp z))
    have h₃ := hfg z hz
    linarith

/-- Local uniform convergence gives convergence of the maximum on a fixed compact slice. -/
theorem tendsto_logSliceMaximum {ι : Type*} {l : Filter ι} {σ : Set ℂ}
    (hσ : IsCompact σ) (hne : σ.Nonempty) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, ContinuousOn (F i) (Complex.exp '' σ))
    (hf : ContinuousOn f (Complex.exp '' σ))
    (hlim : TendstoLocallyUniformly F f l) :
    Tendsto (fun i => logSliceMaximum σ (F i)) l (𝓝 (logSliceMaximum σ f)) := by
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hlim)
    (Complex.exp '' σ) (hσ.image Complex.continuous_exp)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (by positivity)] with i hi
  rw [Real.dist_eq, abs_sub_comm]
  apply (logSliceMaximum_stability hσ hne hf (hF i) ?_).trans_lt (half_lt_self hε)
  intro z hz
  have hdist : ‖f (Complex.exp z) - F i (Complex.exp z)‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hi (Complex.exp z) (mem_image_of_mem _ hz)
  exact hdist.le

/-- The fixed compact-segment maximum depends continuously on a locally uniform family. -/
theorem continuous_logSliceMaximum {P : Type*} [TopologicalSpace P] {σ : Set ℂ}
    (hσ : IsCompact σ) (hne : σ.Nonempty) {F : P → ℂ → ℂ}
    (hF : ∀ p, ContinuousOn (F p) (Complex.exp '' σ))
    (hdep : ∀ p, TendstoLocallyUniformly F (F p) (𝓝 p)) :
    Continuous (fun p => logSliceMaximum σ (F p)) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_logSliceMaximum hσ hne hF (hF p) (hdep p)

/-- The difference of chamber and passage maxima is a continuous shooting function. -/
theorem continuous_chamber_sub_passage_maximum {P : Type*} [TopologicalSpace P]
    {chamber passage : Set ℂ} (hc : IsCompact chamber) (hcne : chamber.Nonempty)
    (hp : IsCompact passage) (hpne : passage.Nonempty) {F : P → ℂ → ℂ}
    (hFc : ∀ p, ContinuousOn (F p) (Complex.exp '' chamber))
    (hFp : ∀ p, ContinuousOn (F p) (Complex.exp '' passage))
    (hdep : ∀ p, TendstoLocallyUniformly F (F p) (𝓝 p)) :
    Continuous (fun p => logSliceMaximum chamber (F p) - logSliceMaximum passage (F p)) :=
  (continuous_logSliceMaximum hc hcne hFc hdep).sub
    (continuous_logSliceMaximum hp hpne hFp hdep)

#print axioms logSliceMaximum_attained
#print axioms logSliceMaximum_stability
#print axioms tendsto_logSliceMaximum
#print axioms continuous_logSliceMaximum
#print axioms continuous_chamber_sub_passage_maximum

end MaxModulusPoints.ConformalKernel
