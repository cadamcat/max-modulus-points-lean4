module

public import MaxModulusPoints.Blueprint.Data

/-!
# `KernelContinuity`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- Kernel continuity, including inverse maps and derivatives, on positive closed
gate boxes. This is specialized to the symmetric tracts actually used. -/
def KernelContinuity : Prop :=
  ∀ (p : BlockParameters) (a : GateIndex → ℝ),
    (∀ i, 0 < a i ∧ a i ≤ gateUpper i) →
    ∀ G : ∀ δ : ParameterBox a gateUpper,
      LogModel (tract p (fun i => (δ i : ℝ))),
    IsOpen {v : ParameterBox a gateUpper × ℂ |
      v.2 ∈ tract p (fun i => (v.1 i : ℝ))} ∧
    ∀ δ : ParameterBox a gateUpper,
      TendstoLocallyUniformlyOn (fun e => (G e).toFun) (G δ).toFun (𝓝 δ)
        (tract p (fun i => (δ i : ℝ))) ∧
      TendstoLocallyUniformlyOn (fun e => (G e).invFun) (G δ).invFun (𝓝 δ) target ∧
      TendstoLocallyUniformlyOn (fun e => deriv (G e).toFun)
        (deriv (G δ).toFun) (𝓝 δ) (tract p (fun i => (δ i : ℝ)))
