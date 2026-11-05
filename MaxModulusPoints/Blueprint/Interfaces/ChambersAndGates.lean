module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.Blueprint.Interfaces.HalfDiscBarriers
public import MaxModulusPoints.Blueprint.Interfaces.KernelContinuity
public import MaxModulusPoints.Blueprint.Interfaces.RectangleBarriers
public import MaxModulusPoints.Blueprint.Interfaces.RempeApproximation
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Blueprint.Interfaces.TractModels
public import MaxModulusPoints.Construction.ChambersAndGates

/-!
# `chambers_and_gates`

One declaration of `MaxModulusPoints.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

namespace Packages

/-- Construct tunnels, gaps, almost-closed gates and fixed starred segments.
The output retains continuity, strict face signs and control of the rest of each
circle. Pardo-Simón–Sixsmith Propositions 4.1–4.4 and Lemma 4.5:
pardo-sixsmith-2607.09462v1.txt:975–1114,1115–1253,1255–1376.
The uniform left bound comes from Lemma 2.8 and Proposition 4.2 at
pardo-sixsmith-2607.09462v1.txt:324–405,1115–1151. -/
theorem chambers_and_gates
    (hmodels : TractModels) (hkernel : KernelContinuity)
    (happrox : RempeApproximation) (hstrip : Nonempty StripMapData)
    (hbottleneck : BottleneckEstimates) (hrectangle : RectangleBarriers)
    (hhalfdisc : HalfDiscBarriers) : Nonempty ShootingFamily := by apply (config := {allowSynthFailures := true}) @_root_.MaxModulusPoints.Blueprint.Packages.chambers_and_gates_proof <;> assumption
