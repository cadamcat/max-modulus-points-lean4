import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.FiberContinuation.ExactCovers
import MaxModulusPoints.FiberContinuation.InverseRoots
import MaxModulusPoints.FiberContinuation.LocalFamilies
import MaxModulusPoints.FiberContinuation.Stabilization
/-!
# Stabilized rotated product comparisons

Two representatives of one common value differ by a root-of-unity rotation
of their parameters. Stabilizing these finitely many rotated comparisons
separates punctured raw image branches.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

theorem norm_powerRootIndex {N : ℕ} (hN : 0 < N) (ω : PowerRootIndex N) : ‖ω.val‖ = 1 := by
  have hω : ω.val ^ N = 1 := (Polynomial.mem_nthRootsFinset hN 1).mp ω.property
  apply (pow_left_inj₀ (norm_nonneg ω.val) zero_le_one hN.ne').mp
  rw [← norm_pow, hω, norm_one, one_pow]

theorem rotation_mem_ball {N : ℕ} (hN : 0 < N) (ω : PowerRootIndex N) {δ : ℝ} {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) δ) : ω.val * t ∈ ball (0 : ℂ) δ := by
  simpa only [mem_ball, dist_zero_right, norm_mul, norm_powerRootIndex hN ω, one_mul] using ht

namespace CommonPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    (C : CommonPowerFamily d s p)

/-- Every rotated product comparison has its punctured equality fixed by its germ. -/
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

/-- A stabilized intersection gives product equality on the entire parameter disk. -/
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

end CommonPowerFamily

end MaxModulusPoints.FiberContinuation
