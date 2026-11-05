module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Card

/-!
# Maximum-modulus points of entire functions

The two questions of Erdős concern the count of exact maximum-modulus points
of one fixed non-monomial entire function as the circle radius tends to infinity.
-/


@[expose] public section

namespace MaxModulusPoints

/-- An entire function is complex differentiable at every point. -/
def Entire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- Monomials include all constants, including the zero function. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (n : ℕ), f = fun z => c * z ^ n

/-- The supremum of the moduli on the circle of radius `r`.
For a continuous function and `r ≥ 0`, this is the attained maximum. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' {z : ℂ | ‖z‖ = r})

/-- The exact maximum points, defined directly by comparison of function values. -/
def maximumPoints (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}

/-- The number of exact maximum points, with value `⊤` for an infinite set. -/
noncomputable def ν (f : ℂ → ℂ) (r : ℝ) : ℕ∞ :=
  (maximumPoints f r).encard

/-- Arbitrarily large counts occur at arbitrarily large positive radii. -/
def UnboundedCounts (f : ℂ → ℂ) : Prop :=
  ∀ (N : ℕ) (R : ℝ), ∃ r : ℝ, 0 < r ∧ R < r ∧ (N : ℕ∞) ≤ ν f r

/-- One finite bound holds along a cofinal set of positive radii. -/
def CofinallyBoundedCounts (f : ℂ → ℂ) : Prop :=
  ∃ B : ℕ, ∀ R : ℝ, ∃ r : ℝ, 0 < r ∧ R < r ∧ ν f r ≤ (B : ℕ∞)

/-- The affirmative limsup answer and the negative liminf answer, respectively. -/
def Statement : Prop :=
  (∃ f : ℂ → ℂ, Entire f ∧ ¬ IsMonomial f ∧ UnboundedCounts f) ∧
  (∀ f : ℂ → ℂ, Entire f → ¬ IsMonomial f → CofinallyBoundedCounts f)

end MaxModulusPoints
