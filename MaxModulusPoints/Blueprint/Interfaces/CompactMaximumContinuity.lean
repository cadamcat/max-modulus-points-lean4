import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Challenge
import MaxModulusPoints.ConformalKernel.CompactMaximumContinuity

/-!
# `compact_maximum_continuity`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Continuity of a compact-segment maximum under locally uniform dependence.
Pardo-Simón–Sixsmith Lemma 4.5:
pardo-sixsmith-2607.09462v1.txt:1331–1356. -/
theorem compact_maximum_continuity {P : Type} [TopologicalSpace P]
    (σ : Set ℂ) (hcompact : IsCompact σ) (hne : σ.Nonempty)
    (F : P → ℂ → ℂ) (hF : ∀ p, Entire (F p))
    (hdep : ∀ p, TendstoLocallyUniformly F (F p) (𝓝 p)) :
    Continuous (fun p => sliceMaximum σ (F p)) := by apply (config := {allowSynthFailures := true}) @_root_.MaxModulusPoints.Blueprint.Packages.compact_maximum_continuity_proof <;> assumption
