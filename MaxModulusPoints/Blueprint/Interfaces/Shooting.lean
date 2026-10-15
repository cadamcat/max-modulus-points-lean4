import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Construction.PackageAdapters

/-!
# `shooting`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Simultaneous zeros on a countable product of compact intervals.
Pardo-Simón–Sixsmith Lemma 2.4:
pardo-sixsmith-2607.09462v1.txt:202–238.
The coordinate signs here have already been oriented toward zero. -/
theorem shooting (a b : GateIndex → ℝ) (hab : ∀ i, a i < b i)
    (φ : GateIndex → ParameterBox a b → ℝ)
    (hcontinuous : ∀ i, Continuous (φ i))
    (hlower : ∀ i δ, (δ i : ℝ) = a i → 0 ≤ φ i δ)
    (hupper : ∀ i δ, (δ i : ℝ) = b i → φ i δ ≤ 0) :
    ∃ δ, ∀ i, φ i δ = 0 := by apply (config := {allowSynthFailures := true}) @_root_.MaxModulusPoints.Blueprint.Packages.shooting_proof <;> assumption
