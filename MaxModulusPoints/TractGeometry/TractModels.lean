import MaxModulusPoints.Blueprint.Interfaces.TractModels
import MaxModulusPoints.TractGeometry.EndBoundsProof
import MaxModulusPoints.TractGeometry.Package
theorem MaxModulusPoints.Blueprint.Packages.tract_models_proof :
    MaxModulusPoints.Blueprint.TractModels :=
  MaxModulusPoints.TractGeometry.tract_models_of_end_bounds
    MaxModulusPoints.TractGeometry.tract_end_bounds
