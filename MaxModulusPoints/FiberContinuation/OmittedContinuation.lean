module

public import Mathlib.Analysis.Complex.Convex
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.Basic
public import MaxModulusPoints.FiberContinuation.BoundedSurvivors
public import MaxModulusPoints.FiberContinuation.CompactCovers
public import MaxModulusPoints.FiberContinuation.CompactFamilies
public import MaxModulusPoints.FiberContinuation.CompactGraphs
public import MaxModulusPoints.FiberContinuation.CompleteBranches
public import MaxModulusPoints.FiberContinuation.ParameterInverses
public import MaxModulusPoints.FiberContinuation.ValueCoordinates
public import MaxModulusPoints.FiberContinuation.ValueWindows

/-!
# Continuation through the value at the origin

A complete branch in the high-count closure fills a local graph over the value
coordinate. Hence membership in that closure is open along each punctured
compact-survivor branch. It is also closed, so connectedness propagates one
noncentral member throughout the punctured disk and closedness includes its
center.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

namespace CompleteHighBranch

/-- A complete branch constrained to a local graph fills a neighborhood of
that graph, since its positive-power value parameter covers a neighborhood. -/
theorem eventually_graph_mem_high {f : ℂ → ℂ} {d : NormalizedFunction f}
    {L : ℕ} {s q : ℂ} (B : CompleteHighBranch d L s (q : OnePoint ℂ))
    (ψ : ℂ → ℂ)
    (hgraph : ∀ᶠ v : ℂ × ℂ in 𝓝 (s, q),
      (v.1, (v.2 : OnePoint ℂ)) ∈ closure (highRegularTargets d L) → v.1 = ψ v.2) :
    ∀ᶠ q' in 𝓝 q, (ψ q', (q' : OnePoint ℂ)) ∈ closure (highRegularTargets d L) := by
  let P : ℂ → ℂ := fun t => (B.pair t).1 * (B.pair t).2
  let F : ℂ → ℂ × ℂ := fun t => (P t, q + t ^ B.exponent)
  have hP0 : P 0 = s := B.central_pair.1
  have hpair : ContinuousAt B.pair 0 :=
    (B.analytic_pair 0 (mem_ball_self B.radius_pos)).continuousAt
  have hP : ContinuousAt P 0 := hpair.fst.mul hpair.snd
  have hF : ContinuousAt F 0 :=
    hP.prodMk ((continuous_const.add (continuous_id.pow B.exponent)).continuousAt)
  have hF0 : F 0 = (s, q) := by simp [F, hP0, B.exponent_pos.ne']
  have hFtendsto : Tendsto F (𝓝 0) (𝓝 (s, q)) := by
    simpa only [hF0] using hF.tendsto
  have hgood : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ ball 0 B.radius ∧ P t = ψ (q + t ^ B.exponent) := by
    filter_upwards [ball_mem_nhds 0 B.radius_pos, hFtendsto.eventually hgraph] with t ht hg
    refine ⟨ht, hg ?_⟩
    simpa [F, P, centeredValue] using B.high t ht
  obtain ⟨δ, hδ, hsmall⟩ := nhds_basis_ball.eventually_iff.mp hgood
  filter_upwards [ball_mem_nhds q (pow_pos hδ B.exponent)] with q' hq'
  have hvalue : (q' : OnePoint ℂ) ∈
      centeredValue (q : OnePoint ℂ) '' ball (0 : ℂ) (δ ^ B.exponent) := by
    refine ⟨q' - q, ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hq'
    · simp [centeredValue]
  obtain ⟨t, ht, htarget⟩ :=
    exists_parameter_in_matched_window (q : OnePoint ℂ) B.exponent_pos hδ hvalue
  have hfinite : q + t ^ B.exponent = q' := by simpa [centeredValue] using htarget
  have hprod : P t = ψ q' := by simpa only [hfinite] using (hsmall ht).2
  have hhigh := B.high t (hsmall ht).1
  change (P t, centeredValue (q : OnePoint ℂ) (t ^ B.exponent)) ∈ _ at hhigh
  rwa [hprod, htarget] at hhigh

end CompleteHighBranch

/-- A punctured complex disk is preconnected: it is the exponential image
of a left half-plane. -/
theorem isPreconnected_punctured_complex_ball {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected (ball (0 : ℂ) δ \ {0}) := by
  have himage : Complex.exp '' {z : ℂ | z.re < Real.log δ} = ball (0 : ℂ) δ \ {0} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero w⟩
      have hnorm : ‖Complex.exp w‖ < δ := by
        rw [Complex.norm_exp]
        exact (Real.exp_lt_exp.mpr hw).trans_eq (Real.exp_log hδ)
      simpa using hnorm
    · rintro ⟨hz, hz0⟩
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      change (Complex.log z).re < Real.log δ
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.mpr hz0) (by simpa using hz)
  rw [← himage]
  exact (convex_halfSpace_re_lt (Real.log δ)).isPreconnected.image Complex.exp
    Complex.continuous_exp.continuousOn

namespace CompactHighCover

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {K : Set (ℂ × ℂ)}
    {s : ℂ} {p : OnePoint ℂ} {L : ℕ} {C : CompactPowerFamily d K s p}
    (D : CompactHighCover C L)

/-- At a noncentral high-closure member away from the omitted value, local
graph filling makes high-closure membership open along the raw branch. -/
theorem eventually_high_closure_of_mem (hsmall : SmallCoordinateBound d L)
    (hstable : C.RotatedProductStability D.radius) (j : C.index) {t : ℂ}
    (ht : t ∈ ball 0 D.radius) (ht0 : t ≠ 0)
    (hhigh : C.rawTarget j t ∈ closure (highRegularTargets d L))
    (hqm : finiteParameterValue p C.exponent t ≠ (d.multiplicity : ℂ)) :
    ∀ᶠ u in 𝓝 t, C.rawTarget j u ∈ closure (highRegularTargets d L) := by
  let q : ℂ := finiteParameterValue p C.exponent t
  let a : ℂ := C.productFunction j t
  have htarget : C.rawTarget j t = (a, (q : OnePoint ℂ)) :=
    Prod.ext rfl (centeredValue_pow_eq_coe p C.exponent ht0)
  have hhigh' : (a, (q : OnePoint ℂ)) ∈ closure (highRegularTargets d L) :=
    htarget ▸ hhigh
  have hq : (q : OnePoint ℂ) ≠ ((d.multiplicity : ℂ) : OnePoint ℂ) := by
    intro heq
    exact hqm (OnePoint.coe_injective heq)
  obtain ⟨B⟩ := exists_complete_high_branch_of_value_ne d L hsmall hhigh' hq
  obtain ⟨ψ, _, _, hgraph⟩ :=
    C.exists_raw_local_graph D.radius_pos D.analytic_pair hstable j ht ht0
  have hcenterW : (a, (q : OnePoint ℂ)) ∈ D.window :=
    htarget ▸ D.rawTarget_mem_window j t ht
  have hmap : Continuous (fun v : ℂ × ℂ => (v.1, (v.2 : OnePoint ℂ))) :=
    continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)
  have hwindow : ∀ᶠ v : ℂ × ℂ in 𝓝 (a, q), (v.1, (v.2 : OnePoint ℂ)) ∈ D.window :=
    (hmap.tendsto (a, q)).eventually (D.open_window.mem_nhds hcenterW)
  have hHgraph : ∀ᶠ v : ℂ × ℂ in 𝓝 (a, q),
      (v.1, (v.2 : OnePoint ℂ)) ∈ closure (highRegularTargets d L) → v.1 = ψ v.2 := by
    filter_upwards [hgraph, hwindow] with v hvgraph hvW hvH
    exact hvgraph (D.closure_cover ⟨hvH, hvW⟩)
  have hfill := B.eventually_graph_mem_high ψ hHgraph
  let F : ℂ → ℂ × ℂ := fun u => (C.productFunction j u, finiteParameterValue p C.exponent u)
  have hpair : ContinuousAt (C.pair j) t := (D.analytic_pair j t ht).continuousAt
  have hvalue := (analyticAt_finiteParameterValue p C.exponent ht0).continuousAt
  have hF : ContinuousAt F t := (hpair.fst.mul hpair.snd).prodMk hvalue
  have hlocal := hF.tendsto.eventually hgraph
  have hfilled := hvalue.tendsto.eventually hfill
  filter_upwards [hlocal, hfilled, isOpen_ball.mem_nhds ht, eventually_ne_nhds ht0]
    with u hugraph huH huball hu0
  have hval := centeredValue_pow_eq_coe p C.exponent hu0
  have huraw : (C.productFunction j u, (finiteParameterValue p C.exponent u : OnePoint ℂ)) ∈
      C.rawBranchUnion univ D.radius := by
    rw [← hval]
    exact mem_iUnion.mpr ⟨⟨j, mem_univ j⟩, u, huball, rfl⟩
  have hprod : C.productFunction j u = ψ (finiteParameterValue p C.exponent u) := hugraph huraw
  change (C.productFunction j u, centeredValue p (u ^ C.exponent)) ∈ _
  rw [hval, hprod]
  exact huH

end CompactHighCover

namespace CompactHighCover

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {K : Set (ℂ × ℂ)}
    {s : ℂ} {L : ℕ}
    {C : CompactPowerFamily d K s ((d.multiplicity : ℂ) : OnePoint ℂ)}
    (D : CompactHighCover C L)

/-- A single noncentral high-closure member propagates throughout its punctured
survivor disk by the clopen property in a preconnected parameter domain. -/
theorem high_on_punctured_disk_of_mem (hsmall : SmallCoordinateBound d L)
    (hstable : C.RotatedProductStability D.radius) (j : C.index) {t : ℂ}
    (ht : t ∈ ball 0 D.radius) (ht0 : t ≠ 0)
    (hhigh : C.rawTarget j t ∈ closure (highRegularTargets d L)) :
    ∀ u ∈ ball 0 D.radius, u ≠ 0 → C.rawTarget j u ∈ closure (highRegularTargets d L) := by
  let X : Set ℂ := ball 0 D.radius \ {0}
  let F : X → ℂ × OnePoint ℂ := fun x => C.rawTarget j x.val
  let A : Set X := F ⁻¹' closure (highRegularTargets d L)
  have hraw : ContinuousOn (C.rawTarget j) (ball 0 D.radius) := by
    have hpair := (D.analytic_pair j).continuousOn
    exact (hpair.fst.mul hpair.snd).prodMk
      (((continuous_centeredValue _).comp (continuous_id.pow C.exponent)).continuousOn)
  have hF : Continuous F := (hraw.mono sdiff_subset).domRestrict
  have hclosed : IsClosed A := isClosed_closure.preimage hF
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hqm : finiteParameterValue ((d.multiplicity : ℂ) : OnePoint ℂ) C.exponent x.val ≠
        (d.multiplicity : ℂ) := by
      intro heq
      have hpow : x.val ^ C.exponent = 0 := by
        simpa [finiteParameterValue, add_eq_left] using heq
      exact pow_ne_zero _ x.property.2 hpow
    have hevent := D.eventually_high_closure_of_mem hsmall hstable j x.property.1
      x.property.2 hx hqm
    exact (continuous_subtype_val.tendsto x).eventually hevent
  letI : PreconnectedSpace X :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_punctured_complex_ball D.radius_pos)
  have hnonempty : A.Nonempty := ⟨⟨t, ht, ht0⟩, hhigh⟩
  have huniv : A = univ := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ hnonempty
  intro u hu hu0
  have hmem : (⟨u, hu, hu0⟩ : X) ∈ A := by rw [huniv]; exact mem_univ _
  exact hmem

end CompactHighCover

/-- Every omitted-value point of the high-count closure lies on a complete
analytic physical branch contained in that closure. -/
theorem exists_complete_high_branch_at_omitted {f : ℂ → ℂ}
    (d : NormalizedFunction f) (L : ℕ) (hsmall : SmallCoordinateBound d L)
    {s : ℂ} (hy : (s, ((d.multiplicity : ℂ) : OnePoint ℂ)) ∈
      closure (highRegularTargets d L)) :
    Nonempty (CompleteHighBranch d L s ((d.multiplicity : ℂ) : OnePoint ℂ)) := by
  have hs : s ≠ 0 := by
    intro hs
    exact zero_not_mem_high_count_projection d L hsmall ⟨(s, _), hy, hs⟩
  obtain ⟨ε, _, C, hcovers⟩ := exists_arbitrarily_small_compact_high_covers d L hsmall hs
    ((d.multiplicity : ℂ) : OnePoint ℂ)
  obtain ⟨r, hr, hstable⟩ := C.exists_rotated_product_stability
  obtain ⟨D, hDr⟩ := hcovers r hr
  have hstableD : C.RotatedProductStability D.radius :=
    CompactPowerFamily.RotatedProductStability.mono C hstable hDr
  obtain ⟨y, hyW, hyE⟩ := _root_.mem_closure_iff.mp hy D.window D.open_window D.center_mem
  have hyH := subset_closure hyE
  obtain ⟨i, hi⟩ := mem_iUnion.mp (D.closure_cover ⟨hyH, hyW⟩)
  obtain ⟨t, ht, htarget⟩ := hi
  have ht0 : t ≠ 0 := by
    intro hzero
    have hvalue : y.2 = ((d.multiplicity : ℂ) : OnePoint ℂ) := by
      rw [← htarget, hzero, C.rawTarget_zero]
    obtain ⟨q, hq, hqm, _⟩ := hyE.2
    exact hqm (OnePoint.coe_injective (hq.symm.trans hvalue))
  have hrawH : C.rawTarget i.val t ∈ closure (highRegularTargets d L) := htarget ▸ hyH
  have hpunc := D.high_on_punctured_disk_of_mem hsmall hstableD i.val ht ht0 hrawH
  refine ⟨{
    exponent := C.exponent
    exponent_pos := C.exponent_pos
    radius := D.radius
    radius_pos := D.radius_pos
    pair := C.pair i.val
    analytic_pair := D.analytic_pair i.val
    central_pair := (C.central_pair i.val).1
    forward := fun u hu => C.forward i.val u (ball_subset_ball D.radius_le hu)
    high := ?_ }⟩
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    change C.rawTarget i.val 0 ∈ _
    rw [C.rawTarget_zero]
    exact hy
  · exact hpunc u hu hu0

/-- Every spherical point of the high-count closure has a complete analytic
physical branch in that closure. -/
theorem exists_complete_high_branch {f : ℂ → ℂ} (d : NormalizedFunction f)
    (L : ℕ) (hsmall : SmallCoordinateBound d L)
    {s : ℂ} {p : OnePoint ℂ} (hy : (s, p) ∈ closure (highRegularTargets d L)) :
    Nonempty (CompleteHighBranch d L s p) := by
  by_cases hp : p = ((d.multiplicity : ℂ) : OnePoint ℂ)
  · subst p
    exact exists_complete_high_branch_at_omitted d L hsmall hy
  · exact exists_complete_high_branch_of_value_ne d L hsmall hy hp

end MaxModulusPoints.FiberContinuation
