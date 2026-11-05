module

public import MaxModulusPoints.Blueprint.Interfaces.TractModels
public import MaxModulusPoints.TractGeometry.EndBoundsProof
public import MaxModulusPoints.TractGeometry.Package

/-!
# `MaxModulusPoints.TractGeometry.TractModels`
-/

@[expose] public section

theorem MaxModulusPoints.Blueprint.Packages.tract_models_proof :
    MaxModulusPoints.Blueprint.TractModels :=
  MaxModulusPoints.TractGeometry.tract_models_of_end_bounds
    MaxModulusPoints.TractGeometry.tract_end_bounds
