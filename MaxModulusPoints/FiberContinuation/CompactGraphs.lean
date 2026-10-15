import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.FiberContinuation.CompactCovers
import MaxModulusPoints.FiberContinuation.CompactFamilies
import MaxModulusPoints.FiberContinuation.InverseRoots
import MaxModulusPoints.FiberContinuation.ParameterInverses
import MaxModulusPoints.FiberContinuation.RotatedComparisons
import MaxModulusPoints.FiberContinuation.Stabilization
import MaxModulusPoints.FiberContinuation.ValueCoordinates
/-!
# Local graphs of compact-survivor images

Stabilize the finitely many rotated product comparisons. At a noncentral
parameter, invert the common value and identify the germs of all graphs through
the target. Continuity removes the other graphs, so the finite raw union is
locally contained in one analytic graph, without any full-fiber capture claim.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

universe u

/-- Persistent central collisions select one graph locally from a finite
continuous graph family. -/
theorem finite_graphs_eventually_single {ι : Type u} [Finite ι]
    (ψ : ι → ℂ → ℂ) (j : ι) (q₀ : ℂ)
    (hcontinuous : ∀ i, ContinuousAt (ψ i) q₀)
    (hcollision : ∀ i, ψ i q₀ = ψ j q₀ → ∀ᶠ q in 𝓝 q₀, ψ i q = ψ j q) :
    ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀),
      (∃ i, v.1 = ψ i v.2) → v.1 = ψ j v.2 := by
  have hselect : ∀ i, ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀),
      v.1 = ψ i v.2 → v.1 = ψ j v.2 := by
    intro i
    by_cases hi : ψ i q₀ = ψ j q₀
    · have hevent : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀), ψ i v.2 = ψ j v.2 :=
        (continuous_snd.tendsto (ψ j q₀, q₀)).eventually (hcollision i hi)
      filter_upwards [hevent] with v hv heq
      exact heq.trans hv
    · have hcont : ContinuousAt (fun v : ℂ × ℂ => v.1 - ψ i v.2) (ψ j q₀, q₀) :=
        continuous_fst.continuousAt.sub ((hcontinuous i).comp continuous_snd.continuousAt)
      have hne : ψ j q₀ - ψ i q₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
      have hevent : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀), v.1 - ψ i v.2 ≠ 0 :=
        hcont.eventually (isOpen_ne.mem_nhds hne)
      filter_upwards [hevent] with v hv heq
      exact False.elim (hv (sub_eq_zero.mpr heq))
  filter_upwards [eventually_all.mpr hselect] with v hv hmem
  obtain ⟨i, hi⟩ := hmem
  exact hv i hi

namespace CompactPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {K : Set (ℂ × ℂ)}
    {s : ℂ} {p : OnePoint ℂ} (C : CompactPowerFamily d K s p)

def RotatedProductStability (δ : ℝ) : Prop :=
  ∀ (i j : C.index) (ω : PowerRootIndex C.exponent) t, t ∈ ball 0 δ → t ≠ 0 →
    (C.productFunction i (ω.val * t) = C.productFunction j t ↔
      ∀ᶠ u in 𝓝 (0 : ℂ), C.productFunction i (ω.val * u) = C.productFunction j u)

theorem exists_rotated_product_stability : ∃ δ : ℝ, 0 < δ ∧ C.RotatedProductStability δ := by
  letI := C.finite_index
  let I := C.index × C.index × PowerRootIndex C.exponent
  let F : I → ℂ → ℂ := fun i t => C.productFunction i.1 (i.2.2.val * t)
  let G : I → ℂ → ℂ := fun i t => C.productFunction i.2.1 t
  have hF : ∀ i, AnalyticAt ℂ (F i) 0 := by
    intro i
    have hprod : AnalyticAt ℂ (C.productFunction i.1) (i.2.2.val * (0 : ℂ)) := by
      simpa only [mul_zero] using C.analyticAt_productFunction i.1
    exact AnalyticAt.comp (f := fun t : ℂ => i.2.2.val * t)
      (g := C.productFunction i.1) hprod (analyticAt_const.mul analyticAt_id)
  have hG : ∀ i, AnalyticAt ℂ (G i) 0 := fun i => C.analyticAt_productFunction i.2.1
  obtain ⟨δ, hδ, hcomp⟩ := analytic_comparisons_stabilize F G hF hG
  exact ⟨δ, hδ, fun i j ω t ht ht0 => hcomp (i, j, ω) t ht ht0⟩

theorem RotatedProductStability.mono {δ η : ℝ} (h : C.RotatedProductStability δ)
    (hη : η ≤ δ) : C.RotatedProductStability η := by
  intro i j ω t ht ht0
  exact h i j ω t (ball_subset_ball hη ht) ht0

theorem product_eqOn_of_rotated_intersection {δ : ℝ} (hδ : 0 < δ)
    (hanalytic : ∀ i, AnalyticOnNhd ℂ (C.pair i) (ball 0 δ))
    (hstable : C.RotatedProductStability δ)
    (i j : C.index) (ω : PowerRootIndex C.exponent) {t : ℂ}
    (ht : t ∈ ball 0 δ) (ht0 : t ≠ 0)
    (heq : C.productFunction i (ω.val * t) = C.productFunction j t) :
    EqOn (fun u => C.productFunction i (ω.val * u)) (C.productFunction j) (ball 0 δ) := by
  have hproducts (k : C.index) : AnalyticOnNhd ℂ (C.productFunction k) (ball 0 δ) :=
    fun u hu => (analyticAt_fst.comp (hanalytic k u hu)).mul
      (analyticAt_snd.comp (hanalytic k u hu))
  have hrot : AnalyticOnNhd ℂ (fun u => C.productFunction i (ω.val * u)) (ball 0 δ) := by
    intro u hu
    exact AnalyticAt.comp (f := fun z : ℂ => ω.val * z) (g := C.productFunction i)
      (hproducts i _ (rotation_mem_ball C.exponent_pos ω hu)) (analyticAt_const.mul analyticAt_id)
  exact hrot.eqOn_of_preconnected_of_eventuallyEq (hproducts j) (convex_ball (0 : ℂ) δ).isPreconnected
    (mem_ball_self hδ) ((hstable i j ω t ht ht0).mp heq)

/-- Near a noncentral raw target, every finite-valued point in the raw union
lies on one analytic graph over its value coordinate. -/
theorem exists_raw_local_graph {δ : ℝ} (hδ : 0 < δ)
    (hanalytic : ∀ i, AnalyticOnNhd ℂ (C.pair i) (ball 0 δ))
    (hstable : C.RotatedProductStability δ)
    (j : C.index) {t : ℂ} (ht : t ∈ ball 0 δ) (ht0 : t ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (finiteParameterValue p C.exponent t) ∧
      ψ (finiteParameterValue p C.exponent t) = C.productFunction j t ∧
      ∀ᶠ v : ℂ × ℂ in 𝓝 (C.productFunction j t, finiteParameterValue p C.exponent t),
        (v.1, (v.2 : OnePoint ℂ)) ∈ C.rawBranchUnion univ δ → v.1 = ψ v.2 := by
  classical
  letI := C.finite_index
  let q₀ : ℂ := finiteParameterValue p C.exponent t
  let s₀ : ℂ := C.productFunction j t
  obtain ⟨R, hR, hRcenter, hRright⟩ := exists_inverse_value_parameter p C.exponent_pos ht0
  have hRcenter' : R q₀ = t := hRcenter
  let I := C.index × PowerRootIndex C.exponent
  let ψ : I → ℂ → ℂ := fun i q => C.productFunction i.1 (i.2.val * R q)
  let ωone : PowerRootIndex C.exponent :=
    ⟨1, Polynomial.one_mem_nthRootsFinset C.exponent_pos⟩
  let base : I := (j, ωone)
  have hbase (q : ℂ) : ψ base q = C.productFunction j (R q) := by simp [ψ, base, ωone]
  have hbase₀ : ψ base q₀ = s₀ := by rw [hbase, hRcenter]
  have hRball : ∀ᶠ q in 𝓝 q₀, R q ∈ ball (0 : ℂ) δ := by
    have hcenterball : R q₀ ∈ ball (0 : ℂ) δ := by rw [hRcenter]; exact ht
    exact hR.continuousAt.eventually (isOpen_ball.mem_nhds hcenterball)
  have hψ : ∀ i, AnalyticAt ℂ (ψ i) q₀ := by
    intro i
    have hparameter : AnalyticAt ℂ (fun q : ℂ => i.2.val * R q) q₀ := analyticAt_const.mul hR
    have hP := hanalytic i.1 (i.2.val * R q₀)
      (rotation_mem_ball C.exponent_pos i.2 (by rw [hRcenter]; exact ht))
    have hS := (analyticAt_fst.comp hP).mul (analyticAt_snd.comp hP)
    exact AnalyticAt.comp (f := fun q : ℂ => i.2.val * R q) (g := C.productFunction i.1) hS hparameter
  have hcollision : ∀ i, ψ i q₀ = ψ base q₀ → ∀ᶠ q in 𝓝 q₀, ψ i q = ψ base q := by
    intro i heq
    have hprod : C.productFunction i.1 (i.2.val * t) = C.productFunction j t := by
      simpa only [ψ, hRcenter', hbase, one_mul] using heq
    have heqOn := C.product_eqOn_of_rotated_intersection hδ hanalytic hstable i.1 j i.2 ht ht0 hprod
    filter_upwards [hRball] with q hqball
    rw [hbase]
    exact heqOn hqball
  have hselect : ∀ᶠ v : ℂ × ℂ in 𝓝 (s₀, q₀),
      (∃ i, v.1 = ψ i v.2) → v.1 = ψ base v.2 := by
    simpa only [hbase₀] using finite_graphs_eventually_single ψ base q₀
      (fun i => (hψ i).continuousAt) hcollision
  have hparamV : ∀ᶠ v : ℂ × ℂ in 𝓝 (s₀, q₀), R v.2 ≠ 0 ∧
      centeredValue p ((R v.2) ^ C.exponent) = (v.2 : OnePoint ℂ) :=
    (continuous_snd.tendsto (s₀, q₀)).eventually hRright
  refine ⟨ψ base, hψ base, hbase₀, ?_⟩
  filter_upwards [hselect, hparamV] with v hvselect hvr hvraw
  obtain ⟨i, hi⟩ := mem_iUnion.mp hvraw
  obtain ⟨u, _, huvalue⟩ := hi
  have hpower : u ^ C.exponent = (R v.2) ^ C.exponent := centeredValue_injective p
    ((congrArg Prod.snd huvalue).trans hvr.2.symm)
  obtain ⟨ω, hω, huω⟩ := exists_root_of_unity_mul C.exponent_pos hpower
  let ωindex : PowerRootIndex C.exponent :=
    ⟨ω, (Polynomial.mem_nthRootsFinset C.exponent_pos 1).mpr hω⟩
  apply hvselect
  refine ⟨(i.val, ωindex), ?_⟩
  have hprod : C.productFunction i.val u = v.1 := congrArg Prod.fst huvalue
  change v.1 = C.productFunction i.val (ω * R v.2)
  rw [← huω]
  exact hprod.symm

end CompactPowerFamily

end MaxModulusPoints.FiberContinuation
