import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.StripMapData
import MaxModulusPoints.StripMap.Package

/-!
# `strip_map_estimates`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Normalized strip map, exponential growth, vertical maximum and kernel limit:
Pardo-Simón–Sixsmith Lemma 2.6 and Corollary 2.7,
pardo-sixsmith-2607.09462v1.txt:270–318. -/
theorem strip_map_estimates : Nonempty StripMapData := @_root_.MaxModulusPoints.Blueprint.Packages.strip_map_estimates_proof
