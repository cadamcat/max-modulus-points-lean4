module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.TractModels
public import MaxModulusPoints.TractGeometry.Basepoint
public import MaxModulusPoints.TractGeometry.ConformalExistence
public import MaxModulusPoints.TractGeometry.EndBounds
public import MaxModulusPoints.TractGeometry.NormalizedSymmetry
public import MaxModulusPoints.TractGeometry.NormalizedSymmetryProof
public import MaxModulusPoints.TractGeometry.Openness
public import MaxModulusPoints.TractGeometry.StripContainment
public import MaxModulusPoints.TractGeometry.Symmetry
public import MaxModulusPoints.TractGeometry.TargetGeometryProof

/-!
# Normalized conformal tracts from finite-end bounds

The geometric and conformal properties combine with the finite-end bounds
to give the normalized logarithmic conformal equivalence and its escape property.
-/


@[expose] public section

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
