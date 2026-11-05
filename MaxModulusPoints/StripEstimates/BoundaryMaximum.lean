module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Topology.Order.Compact

/-!
# Harmonic comparison from boundary upper limits

A maximum principle with boundary upper-limit hypotheses, as used in the
rectangle and half-disc comparisons of Pardo-Simón–Sixsmith, Section 4.
-/


@[expose] public section

open Set Filter Metric Topology InnerProductSpace

namespace MaxModulusPoints.StripEstimates

/-- A harmonic function on a bounded connected open subset of the complex plane
is bounded by `C` if its upper limit at every boundary point is at most `C`.
The boundary hypothesis is expressed using every real threshold above `C`.
No continuity on the closure is required. -/
theorem harmonic_le_of_boundary_limsup {U : Set ℂ} {u : ℂ → ℝ} {C : ℝ}
    (hopen : IsOpen U) (hconn : IsPreconnected U) (hbounded : Bornology.IsBounded U)
    (hu : HarmonicOnNhd u U)
    (hboundary : ∀ p ∈ frontier U, ∀ b : ℝ, C < b →
      ∀ᶠ z in 𝓝[U] p, u z < b) :
    ∀ z ∈ U, u z ≤ C := by
  intro z hz
  by_contra hnot
  have hCz : C < u z := lt_of_not_ge hnot
  let b : ℝ := (C + u z) / 2
  have hCb : C < b := by dsimp [b]; linarith
  have hbz : b ≤ u z := by dsimp [b]; linarith
  let K : Set ℂ := {w | w ∈ U ∧ b ≤ u w}
  have hKU : K ⊆ U := fun _ hw => hw.1
  have hKclosed : IsClosed K := by
    apply isClosed_of_closure_subset
    intro w hw
    by_cases hwU : w ∈ U
    · exact ⟨hwU, ContinuousWithinAt.closure_le hw continuousWithinAt_const
        ((hu w hwU).1.continuousAt.continuousWithinAt) (fun _ hy => hy.2)⟩
    · have hwfront : w ∈ frontier U :=
        ⟨closure_mono hKU hw, by simpa only [hopen.interior_eq] using hwU⟩
      have hnear := eventually_nhdsWithin_iff.mp (hboundary w hwfront b hCb)
      obtain ⟨y, hyK, hynear⟩ :=
        ((mem_closure_iff_frequently.mp hw).and_eventually hnear).exists
      exact False.elim ((not_lt_of_ge hyK.2) (hynear hyK.1))
  have hKcompact : IsCompact K :=
    hbounded.isCompact_closure.of_isClosed_subset hKclosed (hKU.trans subset_closure)
  obtain ⟨p, hpK, hpmax⟩ :=
    hKcompact.exists_isMaxOn ⟨z, hz, hbz⟩ (hu.continuousOn.mono hKU)
  have hpmaxU : IsMaxOn u U p := by
    intro y hy
    by_cases hyK : y ∈ K
    · exact hpmax hyK
    · have hyb : u y < b := lt_of_not_ge (fun hby => hyK ⟨hy, hby⟩)
      exact hyb.le.trans hpK.2
  have hplocal : IsLocalMax u p := hpmaxU.isLocalMax (hopen.mem_nhds hpK.1)
  have hconstantNear : u =ᶠ[𝓝 p] (fun _ => u p) := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hu p hpK.1).eventually
    obtain ⟨f, hf, hre⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
      (show HarmonicOnNhd u (ball p r) from hball)
    have hpball : p ∈ ball p r := mem_ball_self hr
    have hexpDiff : ∀ᶠ w in 𝓝 p,
        DifferentiableAt ℂ (fun v => Complex.exp (f v)) w := by
      filter_upwards [ball_mem_nhds p hr] with w hw
      exact Complex.differentiable_exp.differentiableAt.comp w
        (hf w hw).differentiableAt
    have hexpMax : IsLocalMax (norm ∘ (fun w => Complex.exp (f w))) p := by
      filter_upwards [hplocal, ball_mem_nhds p hr] with w hw hwball
      simp only [Function.comp_apply, Complex.norm_exp, hre hwball, hre hpball]
      exact Real.exp_le_exp.mpr hw
    have hexpEq := Complex.norm_eventually_eq_of_isLocalMax hexpDiff hexpMax
    filter_upwards [hexpEq, ball_mem_nhds p hr] with w hw hwball
    simpa only [Complex.norm_exp, hre hwball, hre hpball, Real.exp_eq_exp] using hw
  have hconstant : EqOn u (fun _ => u p) U :=
    (show AnalyticOnNhd ℝ u U from fun w hw => _root_.HarmonicAt.analyticAt (hu w hw))
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hpK.1 hconstantNear
  obtain ⟨q, hq⟩ : (frontier U).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨z, hz⟩, fun hU => NormedSpace.unbounded_univ ℂ ℂ (hU ▸ hbounded)⟩
  have hnear := eventually_nhdsWithin_iff.mp (hboundary q hq b hCb)
  obtain ⟨y, hyU, hynear⟩ :=
    ((mem_closure_iff_frequently.mp (frontier_subset_closure hq)).and_eventually hnear).exists
  have hyp : u p < b := by simpa only [hconstant hyU] using hynear hyU
  exact (not_lt_of_ge hpK.2) hyp

end MaxModulusPoints.StripEstimates
