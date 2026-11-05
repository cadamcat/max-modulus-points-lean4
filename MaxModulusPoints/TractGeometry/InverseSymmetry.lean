module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.NormalizedSymmetry
public import MaxModulusPoints.TractGeometry.Symmetry

/-!
# Conjugation symmetry of the inverse conformal map

The inverse of a symmetric conformal equivalence commutes with conjugation
on the target, since reflection preserves the source tract.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Blueprint

theorem tract_inverse_star (p : BlockParameters) (δ : GateIndex → ℝ)
    (e : NormalizedSymmetricEquivalence (tract p δ) target (-1) 1)
    {w : ℂ} (hw : w ∈ target) :
    e.invFun (star w) = star (e.invFun w) := by
  have hu := e.inverse_mapsTo hw
  have hstaru := tract_star_mem p δ hu
  have hsym := e.symmetric_map (e.invFun w) hu
  rw [e.right_inv w hw] at hsym
  have hleft := e.left_inv (star (e.invFun w)) hstaru
  rw [hsym] at hleft
  exact hleft

end MaxModulusPoints.TractGeometry
