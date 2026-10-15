import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.KernelContinuity
import MaxModulusPoints.ConformalKernel.KernelContinuityPackage

/-!
# `kernel_continuity`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Carathéodory kernel continuity with real positive derivative normalization:
pardo-sixsmith-2607.09462v1.txt:176–198,914–916,1346–1356. -/
theorem kernel_continuity : KernelContinuity := @_root_.MaxModulusPoints.Blueprint.Packages.kernel_continuity_proof
