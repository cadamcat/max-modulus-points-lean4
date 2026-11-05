module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.ExactCovers
public import MaxModulusPoints.FiberContinuation.FiniteGraphs
public import MaxModulusPoints.FiberContinuation.InverseRoots
public import MaxModulusPoints.FiberContinuation.LocalFamilies
public import MaxModulusPoints.FiberContinuation.ParameterInverses
public import MaxModulusPoints.FiberContinuation.RotatedComparisons
public import MaxModulusPoints.FiberContinuation.ValueCoordinates

/-!
# Regularity of noncentral raw targets

Invert the common value parameter near a nonzero parameter. Roots of unity
then give a finite analytic graph description of the whole local image.
Stabilized product comparisons identify every graph through the chosen target.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

namespace CommonPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    (C : CommonPowerFamily d s p)

/-- Every noncentral raw target of a stabilized exact cover is a whole-image
graph point whenever its product is nonzero and its finite value differs from m. -/
theorem regularTarget_of_stabilized_family {δ : ℝ} (hδ : 0 < δ) (hδC : δ ≤ C.radius)
    (hanalytic : ∀ i, AnalyticOnNhd ℂ (C.pair i) (ball 0 δ))
    (hstable : C.RotatedProductStability δ)
    (W : Set (ℂ × OnePoint ℂ)) (hW : IsOpen W)
    (hcover : actualTargets d ∩ W = ⋃ i, C.rawTarget i '' ball 0 δ)
    (j : C.index) {t : ℂ} (ht : t ∈ ball 0 δ) (ht0 : t ≠ 0)
    (hs : C.productFunction j t ≠ 0)
    (hq : finiteParameterValue p C.exponent t ≠ (d.multiplicity : ℂ)) :
    RegularTarget d (C.productFunction j t) (finiteParameterValue p C.exponent t) := by
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
  have hrawW : C.rawTarget j t ∈ W := by
    have hmem : C.rawTarget j t ∈ actualTargets d ∩ W := by
      rw [hcover]
      exact mem_iUnion.mpr ⟨j, t, ht, rfl⟩
    exact hmem.2
  have hcenterW : (s₀, (q₀ : OnePoint ℂ)) ∈ W := by
    change (C.productFunction j t, centeredValue p (t ^ C.exponent)) ∈ W at hrawW
    rwa [centeredValue_pow_eq_coe p C.exponent ht0] at hrawW
  have hmap : Continuous (fun v : ℂ × ℂ => (v.1, (v.2 : OnePoint ℂ))) :=
    continuous_fst.prodMk (OnePoint.continuous_coe.comp continuous_snd)
  have htargetW : ∀ᶠ v : ℂ × ℂ in 𝓝 (s₀, q₀), (v.1, (v.2 : OnePoint ℂ)) ∈ W :=
    (hmap.tendsto (s₀, q₀)).eventually (hW.mem_nhds hcenterW)
  have hqconditions : ∀ᶠ q in 𝓝 q₀, R q ∈ ball (0 : ℂ) δ ∧ R q ≠ 0 ∧
      centeredValue p ((R q) ^ C.exponent) = (q : OnePoint ℂ) := hRball.and hRright
  have hparamV : ∀ᶠ v : ℂ × ℂ in 𝓝 (s₀, q₀), R v.2 ∈ ball (0 : ℂ) δ ∧ R v.2 ≠ 0 ∧
      centeredValue p ((R v.2) ^ C.exponent) = (v.2 : OnePoint ℂ) :=
    (continuous_snd.tendsto (s₀, q₀)).eventually hqconditions
  have himage : ∀ᶠ v : ℂ × ℂ in 𝓝 (s₀, q₀),
      (physicalFiber d v.1 (v.2 : OnePoint ℂ)).Nonempty ↔ ∃ i, v.1 = ψ i v.2 := by
    filter_upwards [htargetW, hparamV] with v hvW hvr
    constructor
    · intro hfiber
      have hmem : (v.1, (v.2 : OnePoint ℂ)) ∈ actualTargets d ∩ W := ⟨hfiber, hvW⟩
      rw [hcover] at hmem
      obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
      obtain ⟨u, hu, huvalue⟩ := hi
      have hpower : u ^ C.exponent = (R v.2) ^ C.exponent := centeredValue_injective p
        ((congrArg Prod.snd huvalue).trans hvr.2.2.symm)
      obtain ⟨ω, hω, huω⟩ := exists_root_of_unity_mul C.exponent_pos hpower
      let ωindex : PowerRootIndex C.exponent :=
        ⟨ω, (Polynomial.mem_nthRootsFinset C.exponent_pos 1).mpr hω⟩
      refine ⟨(i, ωindex), ?_⟩
      have hprod : C.productFunction i u = v.1 := congrArg Prod.fst huvalue
      change v.1 = C.productFunction i (ω * R v.2)
      rw [← huω]
      exact hprod.symm
    · rintro ⟨⟨i, ω⟩, heq⟩
      let u : ℂ := ω.val * R v.2
      have huball : u ∈ ball (0 : ℂ) δ := rotation_mem_ball C.exponent_pos ω hvr.1
      have hforward := C.forward i u (ball_subset_ball hδC huball)
      have hω : ω.val ^ C.exponent = 1 :=
        (Polynomial.mem_nthRootsFinset C.exponent_pos 1).mp ω.property
      have hval : centeredValue p (u ^ C.exponent) = (v.2 : OnePoint ℂ) := by
        change centeredValue p ((ω.val * R v.2) ^ C.exponent) = (v.2 : OnePoint ℂ)
        rw [mul_pow, hω, one_mul]
        exact hvr.2.2
      exact ⟨C.pair i u, heq.symm, hforward.2.1.trans hval, hforward.2.2.trans hval⟩
  have hregular := regularTarget_of_local_finite_graphs d ψ base q₀ hψ
    (by rw [hbase₀]; exact hs) hq hcollision (by simpa only [hbase₀] using himage)
  simpa only [hbase₀] using hregular

end CommonPowerFamily

end MaxModulusPoints.FiberContinuation
