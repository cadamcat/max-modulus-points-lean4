import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.FiberContinuation.ExactCovers
import MaxModulusPoints.FiberContinuation.LocalFamilies
import MaxModulusPoints.FiberContinuation.ValueCoordinates
import MaxModulusPoints.FiberContinuation.ValueWindows
/-!
# Relative closedness of finite raw branch unions

The value coordinate bounds every representing parameter strictly inside its
disk. Compactness of a smaller closed parameter disk then closes any finite
subunion of raw images inside the full open value cylinder.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

universe u

theorem mem_closure_inter_of_isOpen {X : Type u} [TopologicalSpace X]
    {A V : Set X} {x : X} (hx : x ∈ closure A) (hV : IsOpen V) (hxV : x ∈ V) :
    x ∈ closure (A ∩ V) := by
  apply _root_.mem_closure_iff.mpr
  intro U hU hxU
  obtain ⟨z, hzUV, hzA⟩ := _root_.mem_closure_iff.mp hx (U ∩ V) (hU.inter hV) ⟨hxU, hxV⟩
  exact ⟨z, hzUV.1, hzA, hzUV.2⟩

namespace CommonPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    (C : CommonPowerFamily d s p)

/-- A subunion of the full raw parameter-disk images. -/
def rawBranchUnion (J : Set C.index) (δ : ℝ) : Set (ℂ × OnePoint ℂ) :=
  ⋃ i : J, C.rawTarget i.val '' ball 0 δ

/-- Every raw branch subunion is closed relative to the open value cylinder. -/
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
  let K : Set (ℂ × OnePoint ℂ) := ⋃ i : J, C.rawTarget i.val '' closedBall 0 τ
  have hrawcont (i : C.index) : ContinuousOn (C.rawTarget i) (closedBall 0 τ) := by
    have hP := (hcontinuous i).mono (closedBall_subset_ball hτδ)
    change ContinuousOn (fun t => ((C.pair i t).1 * (C.pair i t).2,
      centeredValue p (t ^ C.exponent))) (closedBall 0 τ)
    exact (hP.fst.mul hP.snd).prodMk
      (((continuous_centeredValue p).comp (continuous_id.pow C.exponent)).continuousOn)
  have hK : IsCompact K := isCompact_iUnion (fun i : J =>
    (isCompact_closedBall (0 : ℂ) τ).image_of_continuousOn (hrawcont i.val))
  have hsub : C.rawBranchUnion J δ ∩ V ⊆ K := by
    rintro z ⟨hzraw, hzV⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzraw
    obtain ⟨t, ht, rfl⟩ := hi
    have htτ : t ∈ ball (0 : ℂ) τ :=
      parameter_mem_of_matched_window p C.exponent_pos hτ hzV
    exact mem_iUnion.mpr ⟨i, t, ball_subset_closedBall htτ, rfl⟩
  have hyK : y ∈ K := closure_minimal hsub hK.isClosed
    (mem_closure_inter_of_isOpen hy.1 hV hyV)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hyK
  obtain ⟨t, ht, htarget⟩ := hi
  exact mem_iUnion.mpr ⟨i, t, closedBall_subset_ball hτδ ht, htarget⟩

end CommonPowerFamily

end MaxModulusPoints.FiberContinuation
