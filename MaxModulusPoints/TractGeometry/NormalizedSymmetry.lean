module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import MaxModulusPoints.Blueprint.Data

/-!
# Normalized conformal equivalences of symmetric plane domains

The real derivative normalization at real base points determines a
conformal equivalence that commutes with complex conjugation.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

structure NormalizedSymmetricEquivalence (U W : Set ℂ) (a b : ℝ)
    extends ConformalEquivalence U W where
  base_value : toFun (a : ℂ) = (b : ℂ)
  positive_derivative : 0 < (deriv toFun (a : ℂ)).re
  real_derivative : (deriv toFun (a : ℂ)).im = 0
  symmetric_map : ∀ z ∈ U, toFun (star z) = star (toFun z)

def SymmetricRiemannMaps : Prop :=
  ∀ (U W : Set ℂ) (a b : ℝ),
    IsOpen U → IsConnected U → IsSimplyConnected U → U ≠ univ →
    IsOpen W → IsConnected W → IsSimplyConnected W → W ≠ univ →
    (a : ℂ) ∈ U → (b : ℂ) ∈ W →
    (∀ z ∈ U, star z ∈ U) → (∀ z ∈ W, star z ∈ W) →
    Nonempty (NormalizedSymmetricEquivalence U W a b)

end MaxModulusPoints.TractGeometry
