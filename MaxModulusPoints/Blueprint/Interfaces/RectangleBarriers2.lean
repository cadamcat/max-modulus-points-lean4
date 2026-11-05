module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.RectangleBarriers
public import MaxModulusPoints.StripEstimates.RectanglePackage

/-!
# `rectangle_barriers`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- The rectangular small-gate harmonic-measure estimate in Proposition 4.3:
pardo-sixsmith-2607.09462v1.txt:1183–1236. -/
theorem rectangle_barriers : RectangleBarriers := @_root_.MaxModulusPoints.Blueprint.Packages.rectangle_barriers_proof
