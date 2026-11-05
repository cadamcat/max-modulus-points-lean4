module

public import MaxModulusPoints.Blueprint.Interfaces.FixedRempeApproximation
public import MaxModulusPoints.CauchyApproximation.FixedApproximation
public import MaxModulusPoints.WallGrowth.WallDecay

/-!
# The approximation package

The canonical Cauchy-integral approximation for the chamber and gate tracts,
combining the core-relative construction with the uniform decay at the tract walls.
-/


@[expose] public section

namespace MaxModulusPoints.Blueprint.Packages

/-- Approximation of the normalized tract models by entire functions, with one
error constant for all chamber and gate tracts. -/
theorem rempe_approximation_proof : FixedRempeApproximation :=
  MaxModulusPoints.CauchyApproximation.fixedRempeApproximation_of_tractWallDecay
    MaxModulusPoints.WallGrowth.tract_wall_decay

end MaxModulusPoints.Blueprint.Packages
