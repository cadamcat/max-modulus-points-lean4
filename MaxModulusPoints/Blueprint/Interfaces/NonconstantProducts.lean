import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Liminf.Packages

/-!
# `nonconstant_products`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Reflected products on the punctured plane are nonconstant. Li, Lemma 3:
li-v2.txt:76–83. -/
theorem nonconstant_products {f : ℂ → ℂ} (d : NormalizedFunction f) :
    NonconstantProducts d := by apply @_root_.MaxModulusPoints.Blueprint.Packages.nonconstant_products_proof <;> assumption
