import MaxModulusPoints.Blueprint.Data

/-!
# `halfDisc`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

def halfDisc : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}
