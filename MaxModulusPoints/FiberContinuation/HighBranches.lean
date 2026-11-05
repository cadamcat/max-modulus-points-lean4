module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.ClosedBranches
public import MaxModulusPoints.FiberContinuation.ExactCovers
public import MaxModulusPoints.FiberContinuation.LocalCounts
public import MaxModulusPoints.FiberContinuation.LocalFamilies
public import MaxModulusPoints.FiberContinuation.ParameterInverses
public import MaxModulusPoints.FiberContinuation.StabilizedCovers
public import MaxModulusPoints.FiberContinuation.ValueCoordinates

/-!
# Local selection of high-count branches

Stabilized physical counts select the punctured high-count branches. The
central-cardinality comparison prevents an isolated regular high target.
Relative closedness then identifies the local high-count closure exactly with
the selected full raw image union, including at an infinite center.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

namespace StabilizedCover

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    {C : CommonPowerFamily d s p} (D : StabilizedCover C)

def selectedIndices (L : ℕ) : Set C.index :=
  {i | ∃ t ∈ ball 0 D.radius, t ≠ 0 ∧
    (L : ℕ∞) < (physicalFiber d (C.productFunction i t) (centeredValue p (t ^ C.exponent))).encard}

theorem high_count_of_selected {L : ℕ} {i : C.index} (hi : i ∈ D.selectedIndices L)
    {t : ℂ} (ht : t ∈ ball 0 D.radius) (ht0 : t ≠ 0) :
    (L : ℕ∞) < (physicalFiber d (C.productFunction i t) (centeredValue p (t ^ C.exponent))).encard := by
  obtain ⟨u, hu, hu0, hhigh⟩ := hi
  exact hhigh.trans_eq (D.count_stable i u t hu hu0 ht ht0)

theorem rawTarget_mem_high_of_selected {L : ℕ} {i : C.index} (hi : i ∈ D.selectedIndices L)
    {t : ℂ} (ht : t ∈ ball 0 D.radius) (ht0 : t ≠ 0) :
    C.rawTarget i t ∈ highRegularTargets d L := by
  have hadm := D.admissible (C.rawTarget i t) (D.rawTarget_mem_window i ht)
  have hq : finiteParameterValue p C.exponent t ≠ (d.multiplicity : ℂ) := by
    intro heq
    exact hadm.2 ((centeredValue_pow_eq_coe p C.exponent ht0).trans
      (congrArg (fun q : ℂ => (q : OnePoint ℂ)) heq))
  exact ⟨hadm.1, finiteParameterValue p C.exponent t, centeredValue_pow_eq_coe p C.exponent ht0,
    hq, D.regular_rawTarget i ht ht0, D.high_count_of_selected hi ht ht0⟩

/-- A high regular center belongs to a selected full branch, by the actual
central-cardinality comparison. -/
theorem central_high_mem_selected_union (L : ℕ) (hhigh : (s, p) ∈ highRegularTargets d L) :
    (s, p) ∈ C.rawBranchUnion (D.selectedIndices L) D.radius := by
  letI := C.finite_index
  obtain ⟨q, hp, hqm, hregular, hcount⟩ := hhigh.2
  change p = (q : OnePoint ℂ) at hp
  subst p
  have hcenter : physicalFiber d s (q : OnePoint ℂ) = range (fun i => C.pair i 0) := by
    ext v
    constructor
    · intro hv
      exact C.central_capture v hv
    · rintro ⟨i, hi⟩
      rw [← hi]
      exact C.central_pair i
  have hnonempty : (physicalFiber d s (q : OnePoint ℂ)).Nonempty :=
    encard_pos.mp (lt_of_le_of_lt (show 0 ≤ (L : ℕ∞) from zero_le) hcount)
  obtain ⟨v, hv⟩ := hnonempty
  obtain ⟨i, _⟩ := C.central_capture v hv
  let qfun : ℂ → ℂ := fun t => q + t ^ C.exponent
  have hqfun0 : qfun 0 = q := by simp [qfun, C.exponent_pos.ne']
  have hqfun : ContinuousAt qfun 0 := by fun_prop
  have hvalid : ∀ k, ∀ᶠ t in 𝓝 (0 : ℂ), C.pair k t ∈
      physicalFiber d ((C.pair k t).1 * (C.pair k t).2) ((qfun t : ℂ) : OnePoint ℂ) := by
    intro k
    filter_upwards [ball_mem_nhds 0 C.radius_pos] with t ht
    exact C.forward k t ht
  have hbound := central_fiber_count_le_nearby d C.pair C.analytic_pair qfun hqfun s
    (by simpa only [hqfun0] using hregular) (by simpa only [hqfun0] using hcenter) hvalid i
  have hball : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball 0 D.radius :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds 0 D.radius_pos)
  obtain ⟨t, htbound, htball, ht0⟩ := (hbound.and (hball.and self_mem_nhdsWithin)).exists
  have hi : i ∈ D.selectedIndices L := by
    refine ⟨t, htball, ht0, ?_⟩
    exact hcount.trans_le (by
      simpa [qfun, C.exponent_pos.ne', CommonPowerFamily.productFunction, centeredValue] using htbound)
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, 0, mem_ball_self D.radius_pos, C.rawTarget_zero i⟩

theorem high_inter_window_subset_selected_union (L : ℕ) :
    highRegularTargets d L ∩ D.window ⊆ C.rawBranchUnion (D.selectedIndices L) D.radius := by
  rintro y ⟨hyhigh, hyW⟩
  have hcount : (L : ℕ∞) < (physicalFiber d y.1 y.2).encard := hyhigh.2.choose_spec.2.2.2
  have hoccupied : (physicalFiber d y.1 y.2).Nonempty :=
    encard_pos.mp (lt_of_le_of_lt (show 0 ≤ (L : ℕ∞) from zero_le) hcount)
  have hmem : y ∈ actualTargets d ∩ D.window := ⟨hoccupied, hyW⟩
  rw [D.exact_image] at hmem
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
  obtain ⟨t, ht, htarget⟩ := hi
  by_cases ht0 : t = 0
  · have hycenter : y = (s, p) := by
      calc
        y = C.rawTarget i t := htarget.symm
        _ = C.rawTarget i 0 := by rw [ht0]
        _ = (s, p) := C.rawTarget_zero i
    rw [hycenter]
    exact D.central_high_mem_selected_union L (by rw [← hycenter]; exact hyhigh)
  · have hrawcount : (L : ℕ∞) <
        (physicalFiber d (C.productFunction i t) (centeredValue p (t ^ C.exponent))).encard := by
      have h : C.rawTarget i t ∈ highRegularTargets d L := by rw [htarget]; exact hyhigh
      exact h.2.choose_spec.2.2.2
    have hselected : i ∈ D.selectedIndices L := ⟨t, ht, ht0, hrawcount⟩
    exact mem_iUnion.mpr ⟨⟨i, hselected⟩, t, ht, htarget⟩

theorem selected_union_subset_high_closure (L : ℕ) :
    C.rawBranchUnion (D.selectedIndices L) D.radius ⊆ closure (highRegularTargets d L) := by
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  obtain ⟨t, ht, rfl⟩ := hi
  by_cases ht0 : t = 0
  · subst t
    have hcont : ContinuousAt (C.rawTarget i.val) 0 :=
      (C.analyticAt_productFunction i.val).continuousAt.prodMk
        (((continuous_centeredValue p).comp (continuous_id.pow C.exponent)).continuousAt)
    have hball : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ ball 0 D.radius :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds 0 D.radius_pos)
    have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℂ), C.rawTarget i.val t ∈ highRegularTargets d L := by
      filter_upwards [hball, self_mem_nhdsWithin] with t ht ht0
      exact D.rawTarget_mem_high_of_selected i.property ht ht0
    exact mem_closure_of_tendsto hcont.continuousWithinAt.tendsto hevent
  · exact subset_closure (D.rawTarget_mem_high_of_selected i.property ht ht0)

/-- The high-count closure is exactly the selected full branch union on the
matched neighborhood, at both finite and infinite centers. -/
theorem high_closure_inter_window (L : ℕ) :
    closure (highRegularTargets d L) ∩ D.window =
      C.rawBranchUnion (D.selectedIndices L) D.radius := by
  apply Subset.antisymm
  · intro y hy
    have hlocal := mem_closure_inter_of_isOpen hy.1 D.open_window hy.2
    have hselected : y ∈ closure (C.rawBranchUnion (D.selectedIndices L) D.radius) :=
      closure_mono (D.high_inter_window_subset_selected_union L) hlocal
    exact C.closure_rawBranchUnion_inter_valueCylinder_subset D.radius_pos
      (fun i => (D.analytic_pair i).continuousOn) (D.selectedIndices L)
      ⟨hselected, D.value_window hy.2⟩
  · intro y hy
    refine ⟨D.selected_union_subset_high_closure L hy, ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    obtain ⟨t, ht, rfl⟩ := hi
    exact D.rawTarget_mem_window i.val ht

end StabilizedCover

end MaxModulusPoints.FiberContinuation
