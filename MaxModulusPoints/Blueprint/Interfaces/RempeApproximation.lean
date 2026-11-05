module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge

/-!
# `RempeApproximation`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- One normalized approximation bound, and one continuously chosen symmetric
entire family. Merely choosing an approximant independently at each parameter
does not satisfy this interface. -/
def RempeApproximation : Prop :=
  ∃ M : ℝ, 0 < M ∧
    ∀ (p : BlockParameters) (a : GateIndex → ℝ),
      (∀ i, 0 < a i ∧ a i ≤ gateUpper i) →
      ∀ G : ∀ δ : ParameterBox a gateUpper,
        LogModel (tract p (fun i => (δ i : ℝ))),
      IsOpen {v : ParameterBox a gateUpper × ℂ |
        v.2 ∈ tract p (fun i => (v.1 i : ℝ))} →
      (∀ δ, TendstoLocallyUniformlyOn (fun e => (G e).toFun) (G δ).toFun
        (𝓝 δ) (tract p (fun i => (δ i : ℝ)))) →
      (∀ δ, TendstoLocallyUniformlyOn (fun e => (G e).invFun) (G δ).invFun
        (𝓝 δ) target) →
      ∃ F : ParameterBox a gateUpper → ℂ → ℂ,
        (∀ δ, Entire (F δ) ∧ ¬ IsMonomial (F δ)) ∧
        (∀ δ, TendstoLocallyUniformly F (F δ) (𝓝 δ)) ∧
        (∀ δ z, F δ (star z) = star (F δ z)) ∧
        (∀ δ z, z ∈ tract p (fun i => (δ i : ℝ)) → 1 < ‖Complex.exp z‖ →
          ‖F δ (Complex.exp z) - Complex.exp ((G δ).toFun z)‖ ≤
            M / ‖Complex.exp z‖) ∧
        (∀ δ z, z ∉ Complex.exp '' tract p (fun i => (δ i : ℝ)) →
          1 < ‖z‖ → ‖F δ z‖ ≤ M / ‖z‖)
