import Mathlib.Analysis.SpecificLimits.Basic
import MaxModulusPoints.CauchyApproximation.CoreTopology
import MaxModulusPoints.CauchyApproximation.Model
/-!
# The contour is the frontier of the core

Small positive real shifts of the image contour lie strictly on its core
side. The continuous conformal inverse brings them back to core points
converging to each original contour point. Consequently the contour is
exactly the frontier of the open core, and its complement is dense.
-/

open Complex Filter Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The original contour is exactly the frontier of the core and has a dense
complement in the whole plane. -/
theorem NormalizedModel.contour_frontier_and_dense_complement (m : NormalizedModel) :
    frontier m.core = range m.contour ∧ Dense (range m.contour)ᶜ := by
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hαim (t : ℝ) : (imageContour t).im = t := by simp [imageContour]
  have hαre (t : ℝ) : (imageContour t).re = 1 - 13 * Real.posLog |t| := by
    simp [imageContour]
  have hαmem (t : ℝ) : imageContour t ∈ modelHalfPlane := by
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
    rw [hαim, hαre]
    linarith [Real.posLog_nonneg (x := |t|)]
  have hshift (t u : ℝ) (hu : 0 < u) :
      m.inverse (imageContour t + (u : ℂ)) ∈ m.core := by
    have hwH : imageContour t + (u : ℂ) ∈ modelHalfPlane := by
      change -14 * Real.posLog |(imageContour t + (u : ℂ)).im| <
        (imageContour t + (u : ℂ)).re
      simp only [add_im, ofReal_im, add_zero, hαim, add_re, ofReal_re, hαre]
      linarith [Real.posLog_nonneg (x := |t|)]
    refine ⟨m.inverse_mem hwH, ?_⟩
    rw [m.right_inverse _ hwH]
    simp only [add_im, ofReal_im, add_zero, hαim, add_re, ofReal_re, hαre]
    linarith
  have hcontourClosure : range m.contour ⊆ closure m.core := by
    rintro _ ⟨t, rfl⟩
    have hu : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have huC : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def, ofRealCLM_apply, ofReal_zero] using
        ofRealCLM.continuous.continuousAt.tendsto.comp hu
    have hw : Tendsto (fun n : ℕ ↦ imageContour t + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        atTop (𝓝 (imageContour t)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := imageContour t)).add huC
    have hinverse : ContinuousAt m.inverse (imageContour t) :=
      m.holomorphic_inverse.continuousOn.continuousAt (hH.mem_nhds (hαmem t))
    exact mem_closure_of_tendsto (hinverse.tendsto.comp hw)
      (Eventually.of_forall (fun n ↦ hshift t (1 / ((n : ℝ) + 1)) (by positivity)))
  obtain ⟨hopen, hclosed⟩ := m.core_open_and_closed_contour_union
  have hclosure : closure m.core = m.core ∪ range m.contour :=
    le_antisymm (closure_minimal subset_union_left hclosed)
      (union_subset subset_closure hcontourClosure)
  have hdisjoint : Disjoint m.core (range m.contour) := by
    apply disjoint_left.2
    intro z hzcore hzcontour
    obtain ⟨t, rfl⟩ := hzcontour
    have hforward : m.forward (m.contour t) = imageContour t := m.right_inverse _ (hαmem t)
    have hlt := hzcore.2
    rw [hforward, hαim, hαre] at hlt
    exact (lt_irrefl _) hlt
  have hfrontier : frontier m.core = range m.contour := by
    rw [hopen.frontier_eq, hclosure]
    ext z
    constructor
    · intro hz
      exact hz.1.resolve_left hz.2
    · intro hz
      exact ⟨Or.inr hz, fun hcore ↦ (disjoint_left.1 hdisjoint) hcore hz⟩
  have hnoInterior : interior (frontier m.core) = ∅ := by
    simpa only [frontier_compl] using interior_frontier hopen.isClosed_compl
  rw [hfrontier] at hnoInterior
  exact ⟨hfrontier, interior_eq_empty_iff_dense_compl.1 hnoInterior⟩

#print axioms NormalizedModel.contour_frontier_and_dense_complement

end MaxModulusPoints.CauchyApproximation
