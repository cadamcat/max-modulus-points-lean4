module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.BoundedSurvivors
public import MaxModulusPoints.FiberContinuation.ClosedBranches
public import MaxModulusPoints.FiberContinuation.CompactFamilies
public import MaxModulusPoints.FiberContinuation.ValueCoordinates
public import MaxModulusPoints.FiberContinuation.ValueWindows

/-!
# Local covers from compact surviving pairs

Matching the spherical value radius to the parameter power keeps each full
raw image in the target window. One compact surviving pair covers every nearby
high-count target. Relative closedness extends that containment to its closure,
including at the value at the origin.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

namespace CompactPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {K : Set (ℂ × ℂ)}
    {s : ℂ} {p : OnePoint ℂ} (C : CompactPowerFamily d K s p)

def productFunction (i : C.index) (t : ℂ) : ℂ := (C.pair i t).1 * (C.pair i t).2

def rawTarget (i : C.index) (t : ℂ) : ℂ × OnePoint ℂ :=
  (C.productFunction i t, centeredValue p (t ^ C.exponent))

theorem analyticAt_productFunction (i : C.index) : AnalyticAt ℂ (C.productFunction i) 0 :=
  (analyticAt_fst.comp (C.analytic_pair i)).mul (analyticAt_snd.comp (C.analytic_pair i))

@[simp] theorem productFunction_zero (i : C.index) : C.productFunction i 0 = s :=
  (C.central_pair i).1.1

@[simp] theorem rawTarget_zero (i : C.index) : C.rawTarget i 0 = (s, p) := by
  simp [rawTarget, C.exponent_pos.ne']

def rawBranchUnion (J : Set C.index) (δ : ℝ) : Set (ℂ × OnePoint ℂ) :=
  ⋃ i : J, C.rawTarget i.val '' ball 0 δ

/-- A finite raw-image subunion is closed relative to its open value cylinder;
this statement uses only the parameter functions, without any capture claim. -/
theorem closure_rawBranchUnion_inter_valueCylinder_subset {δ : ℝ} (hδ : 0 < δ)
    (hcontinuous : ∀ i, ContinuousOn (C.pair i) (ball 0 δ)) (J : Set C.index) :
    closure (C.rawBranchUnion J δ) ∩
      (Prod.snd ⁻¹' (centeredValue p '' ball (0 : ℂ) (δ ^ C.exponent))) ⊆
        C.rawBranchUnion J δ := by
  letI := C.finite_index
  intro y hy
  obtain ⟨t₀, ht₀, hvalue⟩ := exists_parameter_in_matched_window p C.exponent_pos hδ hy.2
  have ht₀δ : ‖t₀‖ < δ := by simpa using ht₀
  obtain ⟨τ, hτlo, hτδ⟩ := exists_between ht₀δ
  have hτ : 0 < τ := (norm_nonneg _).trans_lt hτlo
  let V : Set (ℂ × OnePoint ℂ) :=
    Prod.snd ⁻¹' (centeredValue p '' ball (0 : ℂ) (τ ^ C.exponent))
  have hV : IsOpen V :=
    (isOpen_centeredValue_image_ball p (pow_pos hτ _)).preimage continuous_snd
  have hyV : y ∈ V := by
    refine ⟨t₀ ^ C.exponent, ?_, hvalue⟩
    have hpower := (pow_lt_pow_iff_left₀ (norm_nonneg t₀) hτ.le C.exponent_pos.ne').mpr hτlo
    simpa only [mem_ball, dist_zero_right, norm_pow] using hpower
  let A : Set (ℂ × OnePoint ℂ) := ⋃ i : J, C.rawTarget i.val '' closedBall 0 τ
  have hrawcont (i : C.index) : ContinuousOn (C.rawTarget i) (closedBall 0 τ) := by
    have hP := (hcontinuous i).mono (closedBall_subset_ball hτδ)
    change ContinuousOn (fun t => ((C.pair i t).1 * (C.pair i t).2,
      centeredValue p (t ^ C.exponent))) (closedBall 0 τ)
    exact (hP.fst.mul hP.snd).prodMk
      (((continuous_centeredValue p).comp (continuous_id.pow C.exponent)).continuousOn)
  have hA : IsCompact A := isCompact_iUnion (fun i : J =>
    (isCompact_closedBall (0 : ℂ) τ).image_of_continuousOn (hrawcont i.val))
  have hsub : C.rawBranchUnion J δ ∩ V ⊆ A := by
    rintro z ⟨hzraw, hzV⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzraw
    obtain ⟨t, ht, rfl⟩ := hi
    have htτ : t ∈ ball (0 : ℂ) τ :=
      parameter_mem_of_matched_window p C.exponent_pos hτ hzV
    exact mem_iUnion.mpr ⟨i, t, ball_subset_closedBall htτ, rfl⟩
  have hyA : y ∈ A := closure_minimal hsub hA.isClosed
    (mem_closure_inter_of_isOpen hy.1 hV hyV)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hyA
  obtain ⟨t, ht, htarget⟩ := hi
  exact mem_iUnion.mpr ⟨i, t, closedBall_subset_ball hτδ ht, htarget⟩

end CompactPowerFamily

/-- A matched compact-survivor cover of the high-count closure. It need not
enumerate any escaping physical pairs or cover the whole actual image. -/
structure CompactHighCover {f : ℂ → ℂ} {d : NormalizedFunction f}
    {K : Set (ℂ × ℂ)} {s : ℂ} {p : OnePoint ℂ}
    (C : CompactPowerFamily d K s p) (L : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ C.radius
  window : Set (ℂ × OnePoint ℂ)
  open_window : IsOpen window
  center_mem : (s, p) ∈ window
  neighborhood_subset : window ⊆ C.neighborhood
  value_window : window ⊆ Prod.snd ⁻¹' (centeredValue p '' ball (0 : ℂ) (radius ^ C.exponent))
  product_nonzero : ∀ y ∈ window, y.1 ≠ 0
  analytic_pair : ∀ i, AnalyticOnNhd ℂ (C.pair i) (ball 0 radius)
  rawTarget_mem_window : ∀ i t, t ∈ ball 0 radius → C.rawTarget i t ∈ window
  closure_cover : closure (highRegularTargets d L) ∩ window ⊆ C.rawBranchUnion univ radius

namespace CompactPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {K : Set (ℂ × ℂ)}
    {s : ℂ} {p : OnePoint ℂ} (C : CompactPowerFamily d K s p)

/-- If every nearby high-count target has a compact survivor, its closure has
a matched finite raw-image cover with arbitrarily small parameter radius. -/
theorem exists_high_closure_cover (L : ℕ) (hs : s ≠ 0)
    (hsurvive : ∀ y ∈ highRegularTargets d L, y.1 ∈ ball s 1 →
      (physicalFiber d y.1 y.2 ∩ K).Nonempty)
    {r : ℝ} (hr : 0 < r) :
    ∃ D : CompactHighCover C L, D.radius ≤ r := by
  letI := C.finite_index
  obtain ⟨U₀, V, hU₀, hV, hsU₀, hpV, hUV⟩ :=
    isOpen_prod_iff.mp C.open_neighborhood s p C.center_mem
  let U : Set ℂ := U₀ ∩ (ball s 1 ∩ {z | z ≠ 0})
  have hU : IsOpen U := hU₀.inter (isOpen_ball.inter isOpen_ne)
  have hsU : s ∈ U := ⟨hsU₀, mem_ball_self zero_lt_one, hs⟩
  have hproduct : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ), C.productFunction i t ∈ U := by
    intro i
    apply (C.analyticAt_productFunction i).continuousAt.eventually
    rw [C.productFunction_zero]
    exact hU.mem_nhds hsU
  have hvalue : ∀ᶠ t in 𝓝 (0 : ℂ), centeredValue p (t ^ C.exponent) ∈ V := by
    apply ((continuous_centeredValue p).comp (continuous_id.pow C.exponent)).continuousAt.eventually
    change V ∈ 𝓝 (centeredValue p ((0 : ℂ) ^ C.exponent))
    rw [zero_pow C.exponent_pos.ne', centeredValue_zero]
    exact hV.mem_nhds hpV
  have hparams : ∀ᶠ t in 𝓝 (0 : ℂ),
      (∀ i, C.productFunction i t ∈ U ∧ AnalyticAt ℂ (C.pair i) t) ∧
      centeredValue p (t ^ C.exponent) ∈ V := by
    apply Filter.Eventually.and _ hvalue
    apply eventually_all.mpr
    intro i
    exact (hproduct i).and (C.analytic_pair i).eventually_analyticAt
  obtain ⟨η, hη, hsmall⟩ := nhds_basis_ball.eventually_iff.mp hparams
  let δ : ℝ := min η (min C.radius r)
  have hδ : 0 < δ := lt_min hη (lt_min C.radius_pos hr)
  have hδη : δ ≤ η := min_le_left _ _
  have hδC : δ ≤ C.radius := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  let W : Set (ℂ × OnePoint ℂ) := U ×ˢ (centeredValue p '' ball (0 : ℂ) (δ ^ C.exponent))
  have hW : IsOpen W := hU.prod (isOpen_centeredValue_image_ball p (pow_pos hδ _))
  have hcenter : (s, p) ∈ W :=
    ⟨hsU, 0, mem_ball_self (pow_pos hδ _), centeredValue_zero p⟩
  have hWsub : W ⊆ C.neighborhood := by
    intro y hy
    obtain ⟨t, ht, htarget⟩ := exists_parameter_in_matched_window p C.exponent_pos hδ hy.2
    exact hUV ⟨hy.1.1, htarget ▸ (hsmall (ball_subset_ball hδη ht)).2⟩
  have hanalytic : ∀ i, AnalyticOnNhd ℂ (C.pair i) (ball 0 δ) :=
    fun i t ht => ((hsmall (ball_subset_ball hδη ht)).1 i).2
  have hrawW (i : C.index) (t : ℂ) (ht : t ∈ ball 0 δ) : C.rawTarget i t ∈ W := by
    have htδ : ‖t‖ < δ := by simpa using ht
    have hpower : t ^ C.exponent ∈ ball (0 : ℂ) (δ ^ C.exponent) := by
      have := (pow_lt_pow_iff_left₀ (norm_nonneg t) hδ.le C.exponent_pos.ne').mpr htδ
      simpa only [mem_ball, dist_zero_right, norm_pow] using this
    exact ⟨(hsmall (ball_subset_ball hδη ht)).1 i |>.1, t ^ C.exponent, hpower, rfl⟩
  have hhigh : highRegularTargets d L ∩ W ⊆ C.rawBranchUnion univ δ := by
    rintro y ⟨hyhigh, hyW⟩
    obtain ⟨v, hv⟩ := hsurvive y hyhigh hyW.1.2.1
    obtain ⟨t, ht, hvalue⟩ := exists_parameter_in_matched_window p C.exponent_pos hδ hyW.2
    obtain ⟨i, hi⟩ := C.capture y (hWsub hyW) t (ball_subset_ball hδC ht) hvalue v hv
    refine mem_iUnion.mpr ⟨⟨i, mem_univ i⟩, t, ht, ?_⟩
    apply Prod.ext
    · change (C.pair i t).1 * (C.pair i t).2 = y.1
      rw [hi]
      exact hv.1.1
    · exact hvalue
  refine ⟨{
    radius := δ
    radius_pos := hδ
    radius_le := hδC
    window := W
    open_window := hW
    center_mem := hcenter
    neighborhood_subset := hWsub
    value_window := fun y hy => hy.2
    product_nonzero := fun y hy => hy.1.2.2
    analytic_pair := hanalytic
    rawTarget_mem_window := hrawW
    closure_cover := ?_ }, hδr⟩
  intro y hy
  have hyraw : y ∈ closure (C.rawBranchUnion univ δ) :=
    closure_mono hhigh (mem_closure_inter_of_isOpen hy.1 hW hy.2)
  exact C.closure_rawBranchUnion_inter_valueCylinder_subset hδ
    (fun i => (hanalytic i).continuousOn) univ ⟨hyraw, hy.2.2⟩

end CompactPowerFamily

/-- A small-coordinate bound supplies one fixed compact survivor family whose
high-closure covers can be chosen with arbitrarily small parameter radii. -/
theorem exists_arbitrarily_small_compact_high_covers {f : ℂ → ℂ}
    (d : NormalizedFunction f) (L : ℕ) (hsmall : SmallCoordinateBound d L)
    {s : ℂ} (hs : s ≠ 0) (p : OnePoint ℂ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ C : CompactPowerFamily d (survivorCompact ε (‖s‖ + 1)) s p,
        ∀ r : ℝ, 0 < r → ∃ D : CompactHighCover C L, D.radius ≤ r := by
  obtain ⟨ε, hε, hsurvivors⟩ := exists_bounded_survivors d L hsmall
  obtain ⟨C⟩ := exists_compact_power_family d (survivorCompact ε (‖s‖ + 1))
    (isCompact_survivorCompact ε (‖s‖ + 1)) hs p
  refine ⟨ε, hε, C, ?_⟩
  intro r hr
  apply C.exists_high_closure_cover L hs _ hr
  intro y hyhigh hyball
  have hnorm : ‖y.1‖ ≤ ‖s‖ + 1 := by
    have hdist : ‖y.1 - s‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hyball
    calc
      ‖y.1‖ = ‖(y.1 - s) + s‖ := by rw [sub_add_cancel]
      _ ≤ ‖y.1 - s‖ + ‖s‖ := norm_add_le _ _
      _ ≤ 1 + ‖s‖ := add_le_add hdist.le le_rfl
      _ = ‖s‖ + 1 := add_comm _ _
  exact hsurvivors (‖s‖ + 1) y.1 y.2 hyhigh.1 hnorm hyhigh.2.choose_spec.2.2.2

end MaxModulusPoints.FiberContinuation
