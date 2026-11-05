module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import MaxModulusPoints.Blueprint.Data

/-!
# Geometry of the target of the logarithmic construction

These properties allow the normalized Riemann mapping theorem to be
applied to the target.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

structure TargetGeometry : Prop where
  open_domain : IsOpen target
  connected_domain : IsConnected target
  simply_connected : IsSimplyConnected target
  base_mem : (1 : ℂ) ∈ target
  zero_not_mem : (0 : ℂ) ∉ target
  symmetric_domain : ∀ z ∈ target, star z ∈ target

end MaxModulusPoints.TractGeometry
