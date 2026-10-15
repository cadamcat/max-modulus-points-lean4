import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
import MaxModulusPoints.CrosscutDistortion.Bottleneck

/-!
# `bottleneck_estimates`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Ahlfors distortion through the tunnel, with its normalization and orientation:
Pardo-Simón–Sixsmith Theorem 2.5 and proof of Proposition 4.1,
pardo-sixsmith-2607.09462v1.txt:250–266,994–1036. -/
theorem bottleneck_estimates : BottleneckEstimates := @_root_.MaxModulusPoints.Blueprint.Packages.bottleneck_estimates_proof
