import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.TractModels
import MaxModulusPoints.TractGeometry.Basepoint
import MaxModulusPoints.TractGeometry.ConformalExistence
import MaxModulusPoints.TractGeometry.EndBounds
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
import MaxModulusPoints.TractGeometry.NormalizedSymmetryProof
import MaxModulusPoints.TractGeometry.Openness
import MaxModulusPoints.TractGeometry.StripContainment
import MaxModulusPoints.TractGeometry.Symmetry
import MaxModulusPoints.TractGeometry.TargetGeometryProof
/-!
# Normalized conformal tracts from finite-end bounds

The geometric and conformal properties combine with the finite-end bounds
to give the normalized logarithmic conformal equivalence and its escape property.
-/

namespace MaxModulusPoints.TractGeometry

open Blueprint

theorem tract_models_of_end_bounds (hbound : TractEndBounds) : TractModels := by
  intro p δ hδ
  have hupper : ∀ i, δ i ≤ gateUpper i := fun i => (hδ i).2
  obtain ⟨e⟩ := tract_normalized_equivalence target_geometry symmetric_riemann_maps
    p δ hupper (fun i => (hδ i).1)
  refine ⟨{
    toConformalEquivalence := e.toConformalEquivalence
    open_domain := tract_isOpen p δ hupper
    base_mem := tract_base_mem p δ
    base_value := by simpa using e.base_value
    positive_derivative := by simpa using e.positive_derivative
    real_derivative := by simpa using e.real_derivative
    exp_injective := tract_exp_injective p δ hupper
    symmetric_domain := fun _ hz => tract_star_mem p δ hz
    symmetric_map := e.symmetric_map
    escape := tract_escape_of_end_bounds hbound p δ hδ e }⟩

end MaxModulusPoints.TractGeometry
