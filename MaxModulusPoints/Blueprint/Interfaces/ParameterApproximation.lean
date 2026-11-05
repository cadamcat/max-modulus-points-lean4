module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.FixedRempeApproximation
public import MaxModulusPoints.Blueprint.Interfaces.RempeApproximation
public import MaxModulusPoints.ParameterApproximation.Package

/-!
# `parameter_approximation`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Continuous dependence of the canonical Cauchy construction is included in
the Rempe interface on the positive closed gate boxes of the construction.
Observation 2.3 is the additional parameter argument:
pardo-sixsmith-2607.09462v1.txt:179–189. This package explicitly
separates that obligation from the fixed-model theorem in Rempe's paper. -/
theorem parameter_approximation (hfixed : FixedRempeApproximation) : RempeApproximation := by apply @_root_.MaxModulusPoints.Blueprint.Packages.parameter_approximation_proof <;> assumption
