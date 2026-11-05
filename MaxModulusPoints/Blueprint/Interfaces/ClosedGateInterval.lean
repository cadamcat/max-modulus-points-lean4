module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates

/-!
# `closedGateInterval`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

def closedGateInterval (y s : ℝ) : Set ℂ :=
  {z | z.re = 1 ∧ |z.im - y| ≤ s / 2}
