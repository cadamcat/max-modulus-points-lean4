import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
/-!
# Conformal models and controlled approximation

The fixed image domain and contour are those of Rempe-Gillen's Theorem 1.7
and Corollary 4.5. The normalization is the one in Theorem 2.2 of
Pardo-Simón–Sixsmith, *A finite-order answer to a problem of Erdős on maximum
modulus points*. The approximation assertions below are propositions; in the
family assertion the same selection must depend locally uniformly continuously
on the parameter, as required by Observation 2.3 of that paper.
-/

open Complex ComplexConjugate Filter MeasureTheory Set
open scoped Topology

universe u

namespace MaxModulusPoints.CauchyApproximation

/-- The fixed logarithmically enlarged right half-plane. -/
def modelHalfPlane : Set ℂ := {w | -14 * Real.posLog |w.im| < w.re}

/-- A conformal model in the plane, normalized at `exp (-1)`. -/
structure NormalizedModel where
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  simplyConnected_domain : IsSimplyConnected domain
  unbounded_domain : ¬ Bornology.IsBounded domain
  zero_not_mem : (0 : ℂ) ∉ domain
  forward : ℂ → ℂ
  inverse : ℂ → ℂ
  holomorphic_forward : DifferentiableOn ℂ forward domain
  holomorphic_inverse : DifferentiableOn ℂ inverse modelHalfPlane
  forward_mem : MapsTo forward domain modelHalfPlane
  inverse_mem : MapsTo inverse modelHalfPlane domain
  left_inverse : ∀ z ∈ domain, inverse (forward z) = z
  right_inverse : ∀ w ∈ modelHalfPlane, forward (inverse w) = w
  base_mem : Complex.exp (-1) ∈ domain
  base_value : forward (Complex.exp (-1)) = 1
  inverse_infinity : ∀ w : ℕ → ℂ, (∀ n, w n ∈ modelHalfPlane) →
    Tendsto (fun n ↦ ‖w n‖) atTop atTop →
    Tendsto (fun n ↦ ‖inverse (w n)‖) atTop atTop

/-- The holomorphic function to be approximated on the tract. -/
noncomputable def NormalizedModel.modelFunction (m : NormalizedModel) (z : ℂ) : ℂ :=
  Complex.exp (m.forward z)

/-- The fixed contour in the image domain. -/
noncomputable def imageContour (t : ℝ) : ℂ :=
  ((1 - 13 * Real.posLog |t| : ℝ) : ℂ) + t * I

/-- The inverse image of the fixed contour. -/
noncomputable def NormalizedModel.contour (m : NormalizedModel) : ℝ → ℂ :=
  m.inverse ∘ imageContour

/-- The part of the tract on the right side of the interior contour. -/
def NormalizedModel.core (m : NormalizedModel) : Set ℂ :=
  {z | z ∈ m.domain ∧ 1 - 13 * Real.posLog |(m.forward z).im| < (m.forward z).re}

/-- The density of the canonical improper Cauchy integral. -/
noncomputable def NormalizedModel.density (m : NormalizedModel) (t : ℝ) : ℂ :=
  m.modelFunction (m.contour t) * deriv m.contour t

/-- The entire extension agrees off the contour with the prescribed gluing. -/
def IsCanonicalApproximation (m : NormalizedModel) (f : ℂ → ℂ) : Prop :=
  ∀ z ∉ range m.contour,
    (z ∈ m.core → f z = cauchyIntegral m.contour m.density z + m.modelFunction z) ∧
    (z ∉ m.core → f z = cauchyIntegral m.contour m.density z)

/-- Finite asymptotic values of an entire function, using continuous curves to infinity. -/
def finiteAsymptoticValues (f : ℂ → ℂ) : Set ℂ :=
  {a | ∃ γ : ℝ → ℂ, Continuous γ ∧
    Tendsto (fun t ↦ ‖γ t‖) atTop atTop ∧ Tendsto (f ∘ γ) atTop (𝓝 a)}

/-- The Eremenko–Lyubich condition: the finite singular values form a bounded set. -/
def HasBoundedSingularValues (f : ℂ → ℂ) : Prop :=
  Bornology.IsBounded (closure (f '' {z | deriv f z = 0} ∪ finiteAsymptoticValues f))

/-- Interior approximation and exterior decay with a specified common constant. -/
def IsControlledApproximation (m : NormalizedModel) (C : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ HasBoundedSingularValues f ∧
    (∀ z ∈ m.domain, 1 < ‖z‖ → ‖f z - m.modelFunction z‖ ≤ C / ‖z‖) ∧
    (∀ z ∉ m.domain, 1 < ‖z‖ → ‖f z‖ ≤ C / ‖z‖)

/-- The tract is invariant under conjugation and the conformal map preserves its real points. -/
def NormalizedModel.IsRealSymmetric (m : NormalizedModel) : Prop :=
  (∀ z ∈ m.domain, conj z ∈ m.domain) ∧
    ∀ x : ℝ, (x : ℂ) ∈ m.domain → (m.forward x).im = 0

/-- The normalized approximation assertion, including its canonical construction and symmetry. -/
def RempeApproximationStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : NormalizedModel, ∃ f : ℂ → ℂ,
    IsControlledApproximation m C f ∧ IsCanonicalApproximation m f ∧
      (m.IsRealSymmetric → ∀ z, f (conj z) = conj (f z))

/-- Analytic continuity data for a family of conformal maps on varying domains.
The incidence set is open, and both the forward and inverse maps vary jointly
continuously on their respective domains. -/
def IsContinuousModelFamily {P : Type u} [TopologicalSpace P]
    (m : P → NormalizedModel) : Prop :=
  IsOpen {pz : P × ℂ | pz.2 ∈ (m pz.1).domain} ∧
    ContinuousOn (fun pz : P × ℂ ↦ (m pz.1).forward pz.2)
      {pz | pz.2 ∈ (m pz.1).domain} ∧
    ContinuousOn (fun pz : P × ℂ ↦ (m pz.1).inverse pz.2)
      (univ ×ˢ modelHalfPlane)

/-- A single canonical family with a uniform approximation bound, real symmetry,
and locally uniform continuous dependence on the parameter. -/
def RempeFamilyApproximationStatement (P : Type u) [TopologicalSpace P] : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : P → NormalizedModel, IsContinuousModelFamily m →
    ∃ f : P → ℂ → ℂ,
      (∀ p, IsControlledApproximation (m p) C (f p) ∧
        IsCanonicalApproximation (m p) (f p) ∧
        ((m p).IsRealSymmetric → ∀ z, f p (conj z) = conj (f p z))) ∧
      ∀ p, TendstoLocallyUniformly f (f p) (𝓝 p)

end MaxModulusPoints.CauchyApproximation
