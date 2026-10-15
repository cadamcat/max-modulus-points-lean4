import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.HalfDiscBarriers
import MaxModulusPoints.StripEstimates.HalfDiscPackage

/-!
# `half_disc_barriers`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Uniform control of slice endpieces in Proposition 4.4:
pardo-sixsmith-2607.09462v1.txt:1289–1327. -/
theorem half_disc_barriers : HalfDiscBarriers := @_root_.MaxModulusPoints.Blueprint.Packages.half_disc_barriers_proof
