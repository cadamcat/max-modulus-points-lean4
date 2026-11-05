module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Liminf.Packages

/-!
# `radial_envelope`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- The radial maximum envelope is locally Lipschitz and strictly increasing;
a positive derivative outside a countable set gives a common real logarithmic
value for all tied maximum points. Li, §9: li-v2.txt:395–427. -/
theorem radial_envelope {f : ℂ → ℂ} (d : NormalizedFunction f) (Q : Set ℝ)
    (hQ : Q.Countable) : GoodRadii d Q := by apply @_root_.MaxModulusPoints.Blueprint.Packages.radial_envelope_proof <;> assumption
