module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Order.Compact
public import MaxModulusPoints.Challenge

/-!
# Data for the maximum-modulus construction

Block n represents the block numbered n + 1 in Pardo-Simón–Sixsmith, §4.
Every reciprocal below is real division with a strictly positive denominator.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- The fixed target of the logarithmic conformal models, equation (2.1). -/
def target : Set ℂ := {z | -14 * max 0 (Real.log |z.im|) < z.re}

/-- The horizontal strip of height one, equation (2.7). -/
def strip : Set ℂ := {z | |z.im| < 1 / 2}

/-- A holomorphic isomorphism, with its inverse specified on the target. -/
structure ConformalEquivalence (U W : Set ℂ) where
  toFun : ℂ → ℂ
  invFun : ℂ → ℂ
  holomorphic : DifferentiableOn ℂ toFun U
  inverse_holomorphic : DifferentiableOn ℂ invFun W
  mapsTo : MapsTo toFun U W
  inverse_mapsTo : MapsTo invFun W U
  left_inv : ∀ z ∈ U, invFun (toFun z) = z
  right_inv : ∀ z ∈ W, toFun (invFun z) = z

/-- The symmetric normalized logarithmic model used in §4. -/
structure LogModel (V : Set ℂ) extends ConformalEquivalence V target where
  open_domain : IsOpen V
  base_mem : (-1 : ℂ) ∈ V
  base_value : toFun (-1) = 1
  positive_derivative : 0 < (deriv toFun (-1)).re
  real_derivative : (deriv toFun (-1)).im = 0
  exp_injective : InjOn Complex.exp V
  symmetric_domain : ∀ z ∈ V, star z ∈ V
  symmetric_map : ∀ z ∈ V, toFun (star z) = star (toFun z)
  escape : ∀ z : ℕ → ℂ, (∀ n, z n ∈ target) →
    Tendsto (fun n => ‖z n‖) atTop atTop →
    Tendsto (fun n => (invFun (z n)).re) atTop atTop

/-- A gate in block n is indexed by a member of Fin (n + 1). -/
abbrev GateIndex := Σ n : ℕ, Fin (n + 1)

/-- Gate parameters have the product topology on closed real intervals. -/
abbrev ParameterBox (a b : GateIndex → ℝ) := ∀ i, Icc (a i) (b i)

def gateUpper (i : GateIndex) : ℝ := 1 / ((i.1 : ℝ) + 1)

structure BlockParameters where
  gap : ℕ → ℝ
  tunnelHeight : ℕ → ℝ
  gap_ge_one : ∀ n, 1 ≤ gap n
  tunnel_pos : ∀ n, 0 < tunnelHeight n
  tunnel_le_quarter : ∀ n, tunnelHeight n ≤ 1 / 4

def blockPosition (p : BlockParameters) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), p.gap k) + n

def slicePosition (p : BlockParameters) (n : ℕ) : ℝ := blockPosition p n + 1 / 4

def chamberBase : ℝ := Real.pi / 2 - 1

def passage (p : BlockParameters) (n : ℕ) : Set ℂ :=
  {z | blockPosition p n ≤ z.re ∧ z.re ≤ blockPosition p n + 1 / 2 ∧
    |z.im| ≤ chamberBase}

def tunnel (p : BlockParameters) (n : ℕ) : Set ℂ :=
  {z | blockPosition p n + 1 / 2 ≤ z.re ∧ z.re ≤ blockPosition p n + 1 ∧
    |z.im| ≤ p.tunnelHeight n / 2}

def sideSign (j : Bool) : ℝ := if j then 1 else -1

def chamber (p : BlockParameters) (i : GateIndex) (j : Bool) : Set ℂ :=
  {z | blockPosition p i.1 ≤ z.re ∧ z.re ≤ blockPosition p i.1 + 1 ∧
    chamberBase + (i.2.val : ℝ) / ((i.1 : ℝ) + 1) ≤ sideSign j * z.im ∧
    sideSign j * z.im ≤ chamberBase + ((i.2.val : ℝ) + 1) / ((i.1 : ℝ) + 1)}

def gate (p : BlockParameters) (δ : GateIndex → ℝ) (i : GateIndex)
    (j : Bool) : Set ℂ :=
  {z | z.re = blockPosition p i.1 + 1 ∧
    |z.im - sideSign j * (chamberBase + (2 * (i.2.val : ℝ) + 1) /
      (2 * ((i.1 : ℝ) + 1)))| < δ i / 2}

def walls (p : BlockParameters) : Set ℂ :=
  ⋃ n, frontier (passage p n) ∪ frontier (tunnel p n) ∪
    ⋃ m : Fin (n + 1), ⋃ j : Bool, frontier (chamber p ⟨n, m⟩ j)

def openings (p : BlockParameters) (n : ℕ) : Set ℂ :=
  {z | (z.re = blockPosition p n ∧ |z.im| < chamberBase) ∨
    (z.re = blockPosition p n + 1 / 2 ∧ |z.im| < p.tunnelHeight n / 2) ∨
    (z.re = blockPosition p n + 1 ∧ |z.im| < p.tunnelHeight n / 2)}

/-- Remove the walls, retaining exactly the three passage openings and the gates. -/
def tract (p : BlockParameters) (δ : GateIndex → ℝ) : Set ℂ :=
  ({z : ℂ | -2 < z.re ∧ |z.im| < Real.pi / 2} \ walls p) ∪
    (⋃ n, openings p n) ∪ (⋃ i, ⋃ j : Bool, gate p δ i j)

def passageSlice (p : BlockParameters) (n : ℕ) : Set ℂ :=
  {z | z.re = slicePosition p n ∧ |z.im| < chamberBase}

def cleanSlice (p : BlockParameters) (n : ℕ) : Set ℂ :=
  {z | z.re = blockPosition p n + 3 / 2 ∧ |z.im| < Real.pi / 2}

/-- Maximum over a fixed compact segment in logarithmic coordinates. -/
def sliceMaximum (σ : Set ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖f (Complex.exp z)‖) '' σ)

/-- The passage and the two symmetric chambers for each gate. -/
abbrev SliceIndex (n : ℕ) := Option (Fin (n + 1) × Bool)

/-- The output of the analytic chamber and gate estimates, before shooting. -/
structure ShootingFamily where
  lower : GateIndex → ℝ
  upper : GateIndex → ℝ
  lower_lt_upper : ∀ i, lower i < upper i
  F : ParameterBox lower upper → ℂ → ℂ
  entire : ∀ δ, Entire (F δ)
  not_monomial : ∀ δ, ¬ IsMonomial (F δ)
  locally_uniform : ∀ δ, TendstoLocallyUniformly F (F δ) (𝓝 δ)
  x : ℕ → ℝ
  x_escape : Tendsto x atTop atTop
  segment : ∀ n, SliceIndex n → Set ℂ
  compact_segment : ∀ n i, IsCompact (segment n i)
  nonempty_segment : ∀ n i, (segment n i).Nonempty
  vertical_segment : ∀ n i z, z ∈ segment n i → z.re = x n
  disjoint_images : ∀ n i j, i ≠ j →
    Disjoint (Complex.exp '' segment n i) (Complex.exp '' segment n j)
  reflected_maxima : ∀ δ n m,
    sliceMaximum (segment n (some (m, false))) (F δ) =
      sliceMaximum (segment n (some (m, true))) (F δ)
  floor : ℝ
  ceiling : ℝ
  ceiling_lt_floor : ceiling < floor
  passage_lower : ∀ δ n, floor ≤ sliceMaximum (segment n none) (F δ)
  outside_upper : ∀ δ n z, ‖z‖ = Real.exp (x n) →
    z ∉ ⋃ i, Complex.exp '' segment n i → ‖F δ z‖ ≤ ceiling
  open_gate : ∀ i δ, (δ i : ℝ) = upper i →
    0 < sliceMaximum (segment i.1 (some (i.2, true))) (F δ) -
      sliceMaximum (segment i.1 none) (F δ)
  closed_gate : ∀ i δ, (δ i : ℝ) = lower i →
    sliceMaximum (segment i.1 (some (i.2, true))) (F δ) -
      sliceMaximum (segment i.1 none) (F δ) < 0

/-- Removing the zero at the origin leaves a nonvanishing value at zero
and a nonconstant entire factor. -/
structure NormalizedFunction (f : ℂ → ℂ) where
  multiplicity : ℕ
  g : ℂ → ℂ
  entire : Entire g
  at_zero : g 0 ≠ 0
  nonconstant : ¬ ∃ c : ℂ, ∀ z, g z = c
  factorization : ∀ z, f z = z ^ multiplicity * g z

def reflected (g : ℂ → ℂ) (z : ℂ) : ℂ := star (g (star z))

/-- The actual spherical value of the logarithmic derivative, with genuine
poles at zeros of the normalized entire factor. -/
def logarithmicValue (m : ℕ) (g : ℂ → ℂ) (z : ℂ) : OnePoint ℂ :=
  if g z = 0 then OnePoint.infty else
    ((m : ℂ) + z * deriv g z / g z : ℂ)

/-- Fibers count distinct physical ordered pairs, rather than branch indices. -/
def physicalFiber {f : ℂ → ℂ} (d : NormalizedFunction f)
    (s : ℂ) (q : OnePoint ℂ) : Set (ℂ × ℂ) :=
  {v | v.1 * v.2 = s ∧ logarithmicValue d.multiplicity d.g v.1 = q ∧
    logarithmicValue d.multiplicity (reflected d.g) v.2 = q}

/-- Small-coordinate pairs have a single bound, uniform in product and value. -/
def SmallCoordinateBound {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ (s : ℂ) (q : OnePoint ℂ), s ≠ 0 →
    ({v ∈ physicalFiber d s q | ‖v.1‖ < ε ∨ ‖v.2‖ < ε} : Set (ℂ × ℂ)).encard ≤
      (L : ℕ∞)

/-- A regular finite-valued target has its whole local actual image equal to
one holomorphic graph over the value coordinate. -/
def RegularTarget {f : ℂ → ℂ} (d : NormalizedFunction f) (s q : ℂ) : Prop :=
  ∃ (U W : Set ℂ) (ψ : ℂ → ℂ), IsOpen U ∧ IsOpen W ∧ s ∈ U ∧ q ∈ W ∧
    (∀ v ∈ U, v ≠ 0) ∧ (∀ v ∈ W, v ≠ (d.multiplicity : ℂ)) ∧
    DifferentiableOn ℂ ψ W ∧ MapsTo ψ W U ∧
    ∀ s' ∈ U, ∀ q' ∈ W, (physicalFiber d s' (q' : OnePoint ℂ)).Nonempty ↔ s' = ψ q'

def RegularFiberBound {f : ℂ → ℂ} (d : NormalizedFunction f) (L : ℕ) : Prop :=
  ∀ (s q : ℂ), s ≠ 0 → q ≠ (d.multiplicity : ℂ) → RegularTarget d s q →
    (physicalFiber d s (q : OnePoint ℂ)).encard ≤ (L : ℕ∞)

def highRegularTargets {f : ℂ → ℂ} (d : NormalizedFunction f)
    (L : ℕ) : Set (ℂ × OnePoint ℂ) :=
  {v | v.1 ≠ 0 ∧ ∃ q : ℂ, v.2 = (q : OnePoint ℂ) ∧
    q ≠ (d.multiplicity : ℂ) ∧ RegularTarget d v.1 q ∧
    (L : ℕ∞) < (physicalFiber d v.1 v.2).encard}

/-- Nonconstant reflected products rule out vertical product branches. -/
def NonconstantProducts {f : ℂ → ℂ} (d : NormalizedFunction f) : Prop :=
  ∀ s : ℂ, s ≠ 0 → ¬ ∃ c : ℂ, ∀ z : ℂ, z ≠ 0 →
    d.g z * reflected d.g (s / z) = c

/-- Outside countably many radii, every occupied real target above the
omitted value is regular. -/
def ExceptionalRadii {f : ℂ → ℂ} (d : NormalizedFunction f) (Q : Set ℝ) : Prop :=
  Q.Countable ∧ ∀ r : ℝ, 0 < r → r ∉ Q → ∀ q : ℝ,
    (d.multiplicity : ℝ) < q →
    (physicalFiber d ((r : ℂ) ^ 2) ((q : ℂ) : OnePoint ℂ)).Nonempty →
    RegularTarget d ((r : ℂ) ^ 2) (q : ℂ)

/-- A good radius in every positive interval has one real logarithmic value
at all its exact maximum points. -/
def GoodRadii {f : ℂ → ℂ} (d : NormalizedFunction f) (Q : Set ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∃ (r q : ℝ), a < r ∧ r < b ∧ r ∉ Q ∧
    (d.multiplicity : ℝ) < q ∧
    MapsTo (fun z : ℂ => (z, star z)) (maximumPoints f r)
      (physicalFiber d ((r : ℂ) ^ 2) ((q : ℂ) : OnePoint ℂ))

end MaxModulusPoints.Blueprint

