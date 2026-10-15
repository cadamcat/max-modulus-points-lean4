import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Liminf.Packages

/-!
# `exceptional_radii`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Exact local finite covers give countably many exceptional positive radii.
Li, §9: li-v2.txt:383–394. -/
theorem exceptional_radii {f : ℂ → ℂ} (d : NormalizedFunction f) :
    ∃ Q : Set ℝ, ExceptionalRadii d Q := _root_.MaxModulusPoints.Blueprint.Packages.exceptional_radii_proof ..
