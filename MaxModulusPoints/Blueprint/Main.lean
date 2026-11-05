module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates2
public import MaxModulusPoints.Blueprint.Interfaces.ChambersAndGates
public import MaxModulusPoints.Blueprint.Interfaces.CompactMaximumContinuity
public import MaxModulusPoints.Blueprint.Interfaces.ExceptionalRadii
public import MaxModulusPoints.Blueprint.Interfaces.GlobalMaxima
public import MaxModulusPoints.Blueprint.Interfaces.HalfDiscBarriers2
public import MaxModulusPoints.Blueprint.Interfaces.HighCountContinuation
public import MaxModulusPoints.Blueprint.Interfaces.KernelContinuity2
public import MaxModulusPoints.Blueprint.Interfaces.NonconstantProducts
public import MaxModulusPoints.Blueprint.Interfaces.Normalize
public import MaxModulusPoints.Blueprint.Interfaces.ParameterApproximation
public import MaxModulusPoints.Blueprint.Interfaces.RadialEnvelope
public import MaxModulusPoints.Blueprint.Interfaces.RectangleBarriers2
public import MaxModulusPoints.Blueprint.Interfaces.RegularFiberBound
public import MaxModulusPoints.Blueprint.Interfaces.RempeApproximation2
public import MaxModulusPoints.Blueprint.Interfaces.Shooting
public import MaxModulusPoints.Blueprint.Interfaces.SmallCoordinateBound
public import MaxModulusPoints.Blueprint.Interfaces.StripMapEstimates
public import MaxModulusPoints.Blueprint.Interfaces.TractModels2
public import MaxModulusPoints.Challenge

/-!
# Assembly of the two maximum-modulus counting answers

The analytic construction and the logarithmic-derivative continuation are
the explicit theorem packages in Interfaces.
-/


@[expose] public section

namespace MaxModulusPoints.Blueprint

open Set Filter
open scoped Topology

/-- The shooting equations equalize all compact-slice maxima, and their distinct
exponential images give unbounded counts at escaping radii. -/
theorem positive_of_family (C : ShootingFamily) :
    ∃ f : ℂ → ℂ, Entire f ∧ ¬ IsMonomial f ∧ UnboundedCounts f := by
  let φ : GateIndex → ParameterBox C.lower C.upper → ℝ := fun i δ =>
    sliceMaximum (C.segment i.1 none) (C.F δ) -
      sliceMaximum (C.segment i.1 (some (i.2, true))) (C.F δ)
  have hcontinuous (i : GateIndex) : Continuous (φ i) :=
    (Packages.compact_maximum_continuity _ (C.compact_segment _ _)
      (C.nonempty_segment _ _) C.F C.entire C.locally_uniform).sub
    (Packages.compact_maximum_continuity _ (C.compact_segment _ _)
      (C.nonempty_segment _ _) C.F C.entire C.locally_uniform)
  obtain ⟨δ, hδ⟩ := Packages.shooting C.lower C.upper C.lower_lt_upper φ hcontinuous
    (by
      intro i δ hi
      have h := C.closed_gate i δ hi
      dsimp [φ]
      linarith)
    (by
      intro i δ hi
      have h := C.open_gate i δ hi
      dsimp [φ]
      linarith)
  have hequal (i : GateIndex) :
      sliceMaximum (C.segment i.1 (some (i.2, true))) (C.F δ) =
        sliceMaximum (C.segment i.1 none) (C.F δ) :=
    (sub_eq_zero.mp (hδ i)).symm
  have hcount := Packages.global_maxima C δ hequal
  refine ⟨C.F δ, C.entire δ, C.not_monomial δ, ?_⟩
  intro N R
  have hescape := Real.tendsto_exp_atTop.comp C.x_escape
  have hevent : ∀ᶠ n : ℕ in atTop, N ≤ n ∧ R < Real.exp (C.x n) :=
    (eventually_ge_atTop N).and (hescape.eventually (eventually_gt_atTop R))
  obtain ⟨n, hn, hR⟩ := hevent.exists
  refine ⟨Real.exp (C.x n), Real.exp_pos _, hR, ?_⟩
  have hN : N ≤ 2 * (n + 1) + 1 := by omega
  exact (show (N : ℕ∞) ≤ ((2 * (n + 1) + 1 : ℕ) : ℕ∞) by exact_mod_cast hN).trans
    (hcount n)

/-- The injection into a bounded physical fiber transfers the finite bound to
the exact maximum-point set, uniformly over cofinal thresholds. -/
theorem cofinal_bound_of_fibers {f : ℂ → ℂ} (d : NormalizedFunction f)
    (L : ℕ) (hbound : RegularFiberBound d L) (Q : Set ℝ)
    (hQ : ExceptionalRadii d Q) (hgood : GoodRadii d Q) :
    CofinallyBoundedCounts f := by
  refine ⟨L, fun R => ?_⟩
  have ha : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  obtain ⟨r, q, har, _, hrQ, hq, hmap⟩ :=
    hgood (max R 1) (max R 1 + 1) ha (lt_add_one _)
  have hr : 0 < r := ha.trans har
  refine ⟨r, hr, (le_max_left R 1).trans_lt har, ?_⟩
  have hle : ν f r ≤
      (physicalFiber d ((r : ℂ) ^ 2) ((q : ℂ) : OnePoint ℂ)).encard :=
    Set.encard_le_encard_of_injOn hmap (by
      intro z _ w _ h
      exact congrArg Prod.fst h)
  by_cases hne : (physicalFiber d ((r : ℂ) ^ 2) ((q : ℂ) : OnePoint ℂ)).Nonempty
  · have hregular := hQ.2 r hr hrQ q hq hne
    have hqne : (q : ℂ) ≠ (d.multiplicity : ℂ) := by exact_mod_cast (ne_of_gt hq)
    exact hle.trans (hbound _ _ (pow_ne_zero 2 (by exact_mod_cast hr.ne')) hqne hregular)
  · exact hle.trans (by simp [Set.not_nonempty_iff_eq_empty.mp hne])

/-- The affirmative limsup answer and the negative liminf answer follow from
the conformal construction and the spherical correspondence packages. -/
theorem main : Statement := by
  obtain ⟨C⟩ := Packages.chambers_and_gates Packages.tract_models
    Packages.kernel_continuity
    (Packages.parameter_approximation Packages.rempe_approximation)
    Packages.strip_map_estimates Packages.bottleneck_estimates
    Packages.rectangle_barriers Packages.half_disc_barriers
  refine ⟨positive_of_family C, ?_⟩
  intro f hf hn
  obtain ⟨d⟩ := Packages.normalize f hf hn
  obtain ⟨L, hsmall⟩ := Packages.small_coordinate_bound d
  have hopen := Packages.high_count_continuation d L hsmall (Packages.nonconstant_products d)
  have hbound := Packages.regular_fiber_bound d L hsmall hopen
  obtain ⟨Q, hQ⟩ := Packages.exceptional_radii d
  exact cofinal_bound_of_fibers d L hbound Q hQ (Packages.radial_envelope d Q hQ.1)

#print axioms positive_of_family
#print axioms cofinal_bound_of_fibers
#print axioms main

end MaxModulusPoints.Blueprint

