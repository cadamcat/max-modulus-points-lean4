module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Liminf.Packages

/-!
# `small_coordinate_bound`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Uniform small-coordinate bound, from local inverse power coordinates.
Li, §3, especially equation (3.1): li-v2.txt:103–144. -/
theorem small_coordinate_bound {f : ℂ → ℂ} (d : NormalizedFunction f) :
    ∃ L : ℕ, SmallCoordinateBound d L := _root_.MaxModulusPoints.Blueprint.Packages.small_coordinate_bound_proof ..
