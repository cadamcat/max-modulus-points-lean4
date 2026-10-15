import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import MaxModulusPoints.CauchyApproximation.Model
/-!
# Separation by the interior contour

The core is open, and its union with the interior contour is closed in the
whole plane. The latter assertion includes possible approaches to the tract
boundary: the inverse map is proper on the closed region to the right of the
image graph. Its image is exactly the core together with the contour.
-/

open Complex Filter Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The core has no boundary points away from the interior contour, including
at the boundary of the tract. -/
theorem NormalizedModel.core_open_and_closed_contour_union (m : NormalizedModel) :
    IsOpen m.core ∧ IsClosed (m.core ∪ range m.contour) := by
  classical
  have hstrict : IsOpen {w : ℂ | 1 - 13 * Real.posLog |w.im| < w.re} := by
    apply isOpen_lt <;> fun_prop
  have hopen : IsOpen m.core := by
    apply isOpen_iff_mem_nhds.2
    intro z hz
    have hzT : z ∈ m.domain := hz.1
    have hcont : ContinuousAt m.forward z :=
      m.holomorphic_forward.continuousOn.continuousAt (m.isOpen_domain.mem_nhds hzT)
    have hright := hcont.tendsto.eventually (hstrict.mem_nhds hz.2)
    exact inter_mem (m.isOpen_domain.mem_nhds hzT) hright
  let A : Set ℂ := {w | 1 - 13 * Real.posLog |w.im| ≤ w.re}
  have hA : IsClosed A := by
    apply isClosed_le <;> fun_prop
  have hAH {w : ℂ} (hw : w ∈ A) : w ∈ modelHalfPlane := by
    change 1 - 13 * Real.posLog |w.im| ≤ w.re at hw
    change -14 * Real.posLog |w.im| < w.re
    linarith [Real.posLog_nonneg (x := |w.im|)]
  have hescape : ∀ R : ℝ, ∃ S : ℝ, ∀ w ∈ A,
      S ≤ ‖w‖ → R ≤ ‖m.inverse w‖ := by
    intro R
    by_contra! h
    choose w hwA hwn hwR using fun n : ℕ ↦ h (n : ℝ)
    have hnorm : Tendsto (fun n : ℕ ↦ ‖w n‖) atTop atTop :=
      tendsto_atTop_mono hwn tendsto_natCast_atTop_atTop
    have hinv := m.inverse_infinity w (fun n ↦ hAH (hwA n)) hnorm
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hinv.eventually_ge_atTop R)
    exact (hwR N).not_ge (hN N le_rfl)
  let J : A → ℂ := fun w ↦ m.inverse w
  have hJcont : Continuous J :=
    m.holomorphic_inverse.continuousOn.comp_continuous continuous_subtype_val
      (fun w ↦ hAH w.property)
  have hval : Tendsto (fun w : A ↦ (w : ℂ)) (cocompact A) (cocompact ℂ) :=
    (isProperMap_iff_tendsto_cocompact.1 hA.isProperMap_subtypeVal).2
  have hAnorm : Tendsto (fun w : A ↦ ‖(w : ℂ)‖) (cocompact A) atTop :=
    tendsto_norm_cocompact_atTop.comp hval
  have hJnorm : Tendsto (fun w : A ↦ ‖J w‖) (cocompact A) atTop := by
    refine tendsto_atTop.2 fun R ↦ ?_
    obtain ⟨S, hS⟩ := hescape R
    filter_upwards [hAnorm.eventually_ge_atTop S] with w hw
    exact hS w w.property hw
  have hJproper : IsProperMap J := by
    apply isProperMap_iff_tendsto_cocompact.2
    refine ⟨hJcont, ?_⟩
    simpa only [Metric.cobounded_eq_cocompact] using
      tendsto_norm_atTop_iff_cobounded.1 hJnorm
  have hαim (t : ℝ) : (imageContour t).im = t := by simp [imageContour]
  have hαre (t : ℝ) : (imageContour t).re = 1 - 13 * Real.posLog |t| := by
    simp [imageContour]
  have hαA (t : ℝ) : imageContour t ∈ A := by
    change 1 - 13 * Real.posLog |(imageContour t).im| ≤ (imageContour t).re
    rw [hαim, hαre]
  have himage : range J = m.core ∪ range m.contour := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hwH := hAH w.property
      have hwT : J w ∈ m.domain := m.inverse_mem hwH
      have hforward : m.forward (J w) = (w : ℂ) := m.right_inverse _ hwH
      have hwle : 1 - 13 * Real.posLog |(w : ℂ).im| ≤ (w : ℂ).re := w.property
      rcases eq_or_lt_of_le hwle with heq | hlt
      · right
        refine ⟨(w : ℂ).im, ?_⟩
        have hwgraph : imageContour (w : ℂ).im = (w : ℂ) := by
          apply Complex.ext
          · rw [hαre, heq]
          · exact hαim _
        change m.inverse (imageContour (w : ℂ).im) = m.inverse w
        rw [hwgraph]
      · left
        exact ⟨hwT, by rwa [hforward]⟩
    · intro hz
      rcases hz with hz | ⟨t, rfl⟩
      · have hwA : m.forward z ∈ A := hz.2.le
        exact ⟨⟨m.forward z, hwA⟩, m.left_inverse z hz.1⟩
      · exact ⟨⟨imageContour t, hαA t⟩, rfl⟩
  refine ⟨hopen, ?_⟩
  rw [← himage]
  exact hJproper.isClosed_range

#print axioms NormalizedModel.core_open_and_closed_contour_union

end MaxModulusPoints.CauchyApproximation
