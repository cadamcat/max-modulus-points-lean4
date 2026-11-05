module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# Exponential correspondence for normalized conformal data

The logarithmic conformal map induces planar conformal data on its
exponential image. The correspondence below records the domain, forward
and inverse identities, and real symmetry needed to transport entire
approximations between the two descriptions.
-/


@[expose] public section

open Complex Set

namespace MaxModulusPoints.CauchyApproximation

/-- The exponential conjugacy from logarithmic to planar conformal data,
including the normalized inverse and real symmetry. -/
def LogModelAdapterStatement : Prop :=
  ∀ (V : Set ℂ) (G : MaxModulusPoints.Blueprint.LogModel V),
    ∃ m : NormalizedModel,
      m.domain = Complex.exp '' V ∧
      (∀ z ∈ V, m.forward (Complex.exp z) = G.toFun z) ∧
      (∀ w ∈ modelHalfPlane, m.inverse w = Complex.exp (G.invFun w)) ∧
      m.IsRealSymmetric

end MaxModulusPoints.CauchyApproximation
