import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.TractModels
import MaxModulusPoints.TractGeometry.TractModels

/-!
# `tract_models`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Pardo-Simón–Sixsmith, Definition 2.1 and the conformal models in §4:
pardo-sixsmith-2607.09462v1.txt:120–139,790–879,914–916. -/
theorem tract_models : TractModels := @_root_.MaxModulusPoints.Blueprint.Packages.tract_models_proof
