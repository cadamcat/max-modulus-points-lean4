module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.FixedRempeApproximation
public import MaxModulusPoints.Blueprint.Interfaces.RempeApproximation
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.ParameterApproximation.Convergence
public import MaxModulusPoints.ParameterApproximation.Uniqueness

/-!
# A continuous family of entire approximants

Uniqueness, normality and stability of the approximation bounds give the
parameter dependence asserted by Pardo-Simón–Sixsmith, Observation 2.3.
The same universal error constant is retained throughout the family.
-/


@[expose] public section

noncomputable section

open Set Filter Topology
open MaxModulusPoints.ParameterApproximation

namespace MaxModulusPoints.Blueprint.Packages

/-- Fixed approximation with a universal constant yields a symmetric entire
family depending locally uniformly continuously on the gate parameters. -/
theorem parameter_approximation_proof (hfixed : FixedRempeApproximation) :
    RempeApproximation := by
  classical
  obtain ⟨M, hM, hfixed⟩ := hfixed
  refine ⟨M, hM, ?_⟩
  intro p a ha G hopen hG _hinv
  choose F hF hnonmono hsym hinside houtside using
    fun δ : ParameterBox a gateUpper => hfixed p (fun j => (δ j : ℝ))
      (fun j => ⟨(ha j).1.trans_le (δ j).property.1, (δ j).property.2⟩) (G δ)
  have hb (δ : ParameterBox a gateUpper) :
      ApproximationBounds (tract p (fun j => (δ j : ℝ))) (G δ).toFun M (F δ) :=
    ⟨hinside δ, houtside δ⟩
  refine ⟨F, (fun δ => ⟨hF δ, hnonmono δ⟩), ?_, hsym, hinside, houtside⟩
  intro δ
  apply approximants_tendsto p
    (fun e : ParameterBox a gateUpper => fun j => (e j : ℝ))
    (fun j => (δ j : ℝ)) (fun e j => (e j).property.2) (fun j => (δ j).property.2)
    G (G δ) F (F δ) hM.le hF (hF δ) hb (hb δ)
  · intro j
    exact (continuous_subtype_val.comp (continuous_apply j)).tendsto δ
  · intro z hz
    have hpre : IsOpen {e : ParameterBox a gateUpper |
        z ∈ tract p (fun j => (e j : ℝ))} :=
      hopen.preimage (continuous_id.prodMk continuous_const)
    exact hpre.mem_nhds hz
  · exact hG δ

#print axioms parameter_approximation_proof

end MaxModulusPoints.Blueprint.Packages
