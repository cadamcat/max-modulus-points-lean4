import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Challenge
import MaxModulusPoints.ParameterApproximation.ExteriorStability
import MaxModulusPoints.ParameterApproximation.Limits
import MaxModulusPoints.ParameterApproximation.Normality
import MaxModulusPoints.ParameterApproximation.Uniqueness
/-!
# Continuous dependence of the unique entire approximant

Exterior stability identifies every entire locally uniform limit with the
approximant for the limiting tract. Normality and the further-subsequence
criterion then give locally uniform convergence of the entire family.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Metric Topology Blueprint

universe u

/-- Coordinatewise convergence of gates and eventual interior membership
identify an entire locally uniform limit with the limiting approximant. -/
theorem tract_limit_eq_approximant {ι : Type u} {l : Filter ι} [NeBot l]
    (p : BlockParameters) (δ : ι → GateIndex → ℝ) (δ₀ : GateIndex → ℝ)
    (hδ : ∀ i j, δ i j ≤ gateUpper j) (hδ₀ : ∀ j, δ₀ j ≤ gateUpper j)
    (G : ∀ i, LogModel (tract p (δ i))) (G₀ : LogModel (tract p δ₀))
    (F : ι → ℂ → ℂ) (F₀ f : ℂ → ℂ) {M M₀ : ℝ}
    (hb : ∀ i, ApproximationBounds (tract p (δ i)) (G i).toFun M (F i))
    (hb₀ : ApproximationBounds (tract p δ₀) G₀.toFun M₀ F₀)
    (hf : Entire f) (hF₀ : Entire F₀)
    (hcoord : ∀ j, Tendsto (fun i => δ i j) l (𝓝 (δ₀ j)))
    (hmem : ∀ z ∈ tract p δ₀, ∀ᶠ i in l, z ∈ tract p (δ i))
    (hG : TendstoLocallyUniformlyOn (fun i => (G i).toFun) G₀.toFun l (tract p δ₀))
    (hF : TendstoLocallyUniformly F f l) : f = F₀ := by
  apply limit_eq_approximant hb hmem (fun z hz => hG.tendsto_at hz)
    (fun z => (tendstoLocallyUniformlyOn_univ.mpr hF).tendsto_at (mem_univ z)) hf hF₀
    (fun z hz hn => exp_tract_exterior_mem_closure p hδ hδ₀ hcoord hz hn) hb₀

/-- For countably generated filters, forward convergence, coordinatewise
gate convergence and eventual membership imply locally uniform convergence
of the entire approximants on the plane. -/
theorem approximants_tendsto {ι : Type u} {l : Filter ι} [l.IsCountablyGenerated]
    (p : BlockParameters) (δ : ι → GateIndex → ℝ) (δ₀ : GateIndex → ℝ)
    (hδ : ∀ i j, δ i j ≤ gateUpper j) (hδ₀ : ∀ j, δ₀ j ≤ gateUpper j)
    (G : ∀ i, LogModel (tract p (δ i))) (G₀ : LogModel (tract p δ₀))
    (F : ι → ℂ → ℂ) (F₀ : ℂ → ℂ) {M M₀ : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i, Entire (F i)) (hF₀ : Entire F₀)
    (hb : ∀ i, ApproximationBounds (tract p (δ i)) (G i).toFun M (F i))
    (hb₀ : ApproximationBounds (tract p δ₀) G₀.toFun M₀ F₀)
    (hcoord : ∀ j, Tendsto (fun i => δ i j) l (𝓝 (δ₀ j)))
    (hmem : ∀ z ∈ tract p δ₀, ∀ᶠ i in l, z ∈ tract p (δ i))
    (hG : TendstoLocallyUniformlyOn (fun i => (G i).toFun) G₀.toFun l (tract p δ₀)) :
    TendstoLocallyUniformly F F₀ l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  have ht : Tendsto (fun i => UniformFun.ofFun (fun z : K => F i z)) l
      (𝓝 (UniformFun.ofFun (fun z : K => F₀ z))) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    have hGs : TendstoLocallyUniformlyOn (fun n => (G (ns n)).toFun)
        G₀.toFun atTop (tract p δ₀) := by
      intro U hU z hz
      obtain ⟨W, hW, he⟩ := hG U hU z hz
      exact ⟨W, hW, hns.eventually he⟩
    obtain ⟨f, hf, φ, hφ, hconv⟩ := approximants_subsequence p
      (fun n => δ (ns n)) δ₀ (fun n => hδ (ns n)) (fun n => G (ns n)) G₀
      (fun n => F (ns n)) hM (fun n => hF (ns n)) (fun n => hb (ns n)) hGs
    have hsub : Tendsto (fun n => ns (φ n)) atTop l :=
      hns.comp hφ.tendsto_atTop
    have hGss : TendstoLocallyUniformlyOn (fun n => (G (ns (φ n))).toFun)
        G₀.toFun atTop (tract p δ₀) := by
      intro U hU z hz
      obtain ⟨W, hW, he⟩ := hG U hU z hz
      exact ⟨W, hW, hsub.eventually he⟩
    have heq : f = F₀ := tract_limit_eq_approximant p
      (fun n => δ (ns (φ n))) δ₀ (fun n => hδ (ns (φ n))) hδ₀
      (fun n => G (ns (φ n))) G₀ (fun n => F (ns (φ n))) F₀ f
      (fun n => hb (ns (φ n))) hb₀ hf hF₀
      (fun j => (hcoord j).comp hsub) (fun z hz => hsub.eventually (hmem z hz))
      hGss hconv
    rw [heq] at hconv
    have hconvK : TendstoUniformlyOn (fun n => F (ns (φ n))) F₀ atTop K :=
      tendstoLocallyUniformly_iff_forall_isCompact.mp hconv K hK
    refine ⟨φ, ?_⟩
    exact UniformFun.tendsto_iff_tendstoUniformly.mpr
      (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hconvK)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp ht)

#print axioms tract_limit_eq_approximant
#print axioms approximants_tendsto

end MaxModulusPoints.ParameterApproximation
