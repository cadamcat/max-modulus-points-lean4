module

public import MaxModulusPoints.Blueprint.Data

/-!
# `rectangle`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

def rectangle (h : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < h}
