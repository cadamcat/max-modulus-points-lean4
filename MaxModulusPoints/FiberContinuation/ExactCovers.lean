import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.FiberContinuation.LocalFamilies
import MaxModulusPoints.FiberContinuation.Stabilization
import MaxModulusPoints.FiberContinuation.ValueCoordinates
import MaxModulusPoints.FiberContinuation.ValueWindows
/-!
# Exact covers of the whole local actual image

The product and value windows are shrunk together with the parameter radius.
Every full raw open-disk image stays in the final window, and every actual
target there is captured at each of its common-power parameters.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

/-- The occupied actual targets, without any regularity requirement. -/
def actualTargets {f : ℂ → ℂ} (d : NormalizedFunction f) : Set (ℂ × OnePoint ℂ) :=
  {y | (physicalFiber d y.1 y.2).Nonempty}

namespace CommonPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    (C : CommonPowerFamily d s p)

def productFunction (i : C.index) (t : ℂ) : ℂ := (C.pair i t).1 * (C.pair i t).2

def rawTarget (i : C.index) (t : ℂ) : ℂ × OnePoint ℂ :=
  (C.productFunction i t, centeredValue p (t ^ C.exponent))

theorem analyticAt_productFunction (i : C.index) : AnalyticAt ℂ (C.productFunction i) 0 :=
  (analyticAt_fst.comp (C.analytic_pair i)).mul (analyticAt_snd.comp (C.analytic_pair i))

@[simp] theorem productFunction_zero (i : C.index) : C.productFunction i 0 = s :=
  (C.central_pair i).1

@[simp] theorem rawTarget_zero (i : C.index) : C.rawTarget i 0 = (s, p) := by
  simp [rawTarget, C.exponent_pos.ne']

/-- Exact same-parameter capture counts the image of the product-filtered
physical indices, so repeated indices contribute only once. -/
theorem physicalFiber_eq_image {t : ℂ} (ht : t ∈ ball 0 C.radius)
    {y : ℂ × OnePoint ℂ} (hy : y ∈ C.neighborhood)
    (hvalue : centeredValue p (t ^ C.exponent) = y.2) :
    physicalFiber d y.1 y.2 = (fun i => C.pair i t) '' {i | C.productFunction i t = y.1} := by
  apply FiberContinuation.physicalFiber_eq_image
  · intro i
    simpa only [hvalue] using C.forward i t ht
  · exact C.capture y hy t ht hvalue

/-- The total actual image has an exact finite cover by full raw open-disk
images, with arbitrarily small allowed parameter radius. -/
theorem exists_exact_local_image_cover {r : ℝ} (hr : 0 < r) :
    ∃ (δ : ℝ) (W : Set (ℂ × OnePoint ℂ)), 0 < δ ∧ δ ≤ r ∧ δ ≤ C.radius ∧
      IsOpen W ∧ (s, p) ∈ W ∧ W ⊆ C.neighborhood ∧
      (∀ i, AnalyticOnNhd ℂ (C.pair i) (ball 0 δ)) ∧
      actualTargets d ∩ W = ⋃ i, C.rawTarget i '' ball 0 δ := by
  letI := C.finite_index
  obtain ⟨U, V, hU, hV, hsU, hpV, hUV⟩ := isOpen_prod_iff.mp C.open_neighborhood s p C.center_mem
  have hproduct : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ), C.productFunction i t ∈ U := by
    intro i
    apply (C.analyticAt_productFunction i).continuousAt.eventually
    change U ∈ 𝓝 (C.productFunction i 0)
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
    apply hUV
    exact ⟨hy.1, htarget ▸ (hsmall (ball_subset_ball hδη ht)).2⟩
  have hrawW (i : C.index) (t : ℂ) (ht : t ∈ ball 0 δ) : C.rawTarget i t ∈ W := by
    have htδ : ‖t‖ < δ := by simpa using ht
    have hpower : t ^ C.exponent ∈ ball (0 : ℂ) (δ ^ C.exponent) := by
      have := (pow_lt_pow_iff_left₀ (norm_nonneg t) hδ.le C.exponent_pos.ne').mpr htδ
      simpa only [mem_ball, dist_zero_right, norm_pow] using this
    exact ⟨(hsmall (ball_subset_ball hδη ht)).1 i |>.1, t ^ C.exponent, hpower, rfl⟩
  refine ⟨δ, W, hδ, hδr, hδC, hW, hcenter, hWsub, ?_, ?_⟩
  · intro i t ht
    exact ((hsmall (ball_subset_ball hδη ht)).1 i).2
  · ext y
    constructor
    · rintro ⟨⟨v, hv⟩, hy⟩
      obtain ⟨t, ht, hvalue⟩ := exists_parameter_in_matched_window p C.exponent_pos hδ hy.2
      obtain ⟨i, hi⟩ := C.capture y (hWsub hy) t (ball_subset_ball hδC ht) hvalue v hv
      refine mem_iUnion.mpr ⟨i, t, ht, ?_⟩
      apply Prod.ext
      · change (C.pair i t).1 * (C.pair i t).2 = y.1
        rw [hi]
        exact hv.1
      · exact hvalue
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      obtain ⟨t, ht, rfl⟩ := hi
      exact ⟨⟨C.pair i t, C.forward i t (ball_subset_ball hδC ht)⟩, hrawW i t ht⟩

end CommonPowerFamily

end MaxModulusPoints.FiberContinuation
