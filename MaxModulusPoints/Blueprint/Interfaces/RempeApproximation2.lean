module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.FixedRempeApproximation
public import MaxModulusPoints.CauchyApproximation.RempePackage

/-!
# `rempe_approximation`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Rempe approximation, symmetry, and uniform normalization:
rempe-1106.3439.txt:162–184,343–395,773–848;
Pardo-Simón–Sixsmith Theorem 2.2:
pardo-sixsmith-2607.09462v1.txt:140–157. -/
theorem rempe_approximation : FixedRempeApproximation := @_root_.MaxModulusPoints.Blueprint.Packages.rempe_approximation_proof
