module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.Construction.PackageAdapters

/-!
# `global_maxima`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Equal compact-slice maxima give distinct global circle maxima.
Pardo-Simón–Sixsmith Corollary 4.6:
pardo-sixsmith-2607.09462v1.txt:1377–1408. -/
theorem global_maxima (C : ShootingFamily) (δ : ParameterBox C.lower C.upper)
    (hequal : ∀ i : GateIndex,
      sliceMaximum (C.segment i.1 (some (i.2, true))) (C.F δ) =
        sliceMaximum (C.segment i.1 none) (C.F δ)) :
    ∀ n, ((2 * (n + 1) + 1 : ℕ) : ℕ∞) ≤ ν (C.F δ) (Real.exp (C.x n)) := by apply @_root_.MaxModulusPoints.Blueprint.Packages.global_maxima_proof <;> assumption
