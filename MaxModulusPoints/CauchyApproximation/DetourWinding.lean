module

public import MaxModulusPoints.CauchyApproximation.ConformalWinding
public import MaxModulusPoints.CauchyApproximation.ContourRegularity
public import MaxModulusPoints.CauchyApproximation.GraphWinding
public import MaxModulusPoints.CauchyApproximation.LocalDetour
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.ResidueJump

/-!
# Local winding values of the canonical detour

Near a point of the original contour, the image coordinate lies below the
right-shifted tent graph and strictly between its parameter endpoints. The
graph winding computation and conformal transfer therefore give winding
number −1 on the core side and zero on the other side. The same neighborhood
avoids the entire detour and lies inside the tract.
-/


@[expose] public section

open Complex Filter Set
open TauCeti.Contour
open scoped Topology Classical

namespace MaxModulusPoints.CauchyApproximation

/-- The actual local detour loop has the clockwise jump values on a whole
neighborhood of each original contour point. -/
theorem NormalizedModel.localDetour_windingNumber (m : NormalizedModel) (s : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (m.contour s) ε ⊆ m.domain ∧
      Metric.ball (m.contour s) ε ⊆ (range (m.localDetour s))ᶜ ∧
      ∀ z ∈ Metric.ball (m.contour s) ε, z ∉ range m.contour →
        windingNumber (closedContourDifference m.contour (m.localDetour s) (s + 1))
            (s - 1) (s + 3) z = if z ∈ m.core then (-1 : ℂ) else 0 := by
  have hαim (t : ℝ) : (imageContour t).im = t := by simp [imageContour]
  have hαre (t : ℝ) : (imageContour t).re = 1 - 13 * Real.posLog |t| := by
    simp [imageContour]
  have hδim (t : ℝ) : (imageDetour s t).im = t := by simp [imageDetour, hαim]
  have hαmem (t : ℝ) : imageContour t ∈ modelHalfPlane := by
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re
    rw [hαim, hαre]
    linarith [Real.posLog_nonneg (x := |t|)]
  have hδmem (t : ℝ) : imageDetour s t ∈ modelHalfPlane := by
    have h := hαmem t
    change -14 * Real.posLog |(imageContour t).im| < (imageContour t).re at h
    change -14 * Real.posLog |(imageDetour s t).im| < (imageDetour s t).re
    simp only [imageDetour, add_im, ofReal_im, add_zero, add_re, ofReal_re]
    linarith [le_max_left (0 : ℝ) (1 - |t - s|)]
  have hγmem (t : ℝ) : m.contour t ∈ m.domain := m.inverse_mem (hαmem t)
  have hforwardγ (t : ℝ) : m.forward (m.contour t) = imageContour t :=
    m.right_inverse _ (hαmem t)
  have hforwardη (t : ℝ) : m.forward (m.localDetour s t) = imageDetour s t :=
    m.right_inverse _ (hδmem t)
  have hδcont : Continuous (imageDetour s) := by
    unfold imageDetour imageContour
    fun_prop
  let W : Set ℂ := {w | s - 1 < w.im ∧ w.im < s + 1 ∧
    w.re < (imageDetour s w.im).re}
  have hW : IsOpen W :=
    (isOpen_lt continuous_const continuous_im).inter
      ((isOpen_lt continuous_im continuous_const).inter
        (isOpen_lt continuous_re (continuous_re.comp (hδcont.comp continuous_im))))
  have hcenter : imageContour s ∈ W := by
    change s - 1 < (imageContour s).im ∧ (imageContour s).im < s + 1 ∧
      (imageContour s).re < (imageDetour s (imageContour s).im).re
    rw [hαim]
    refine ⟨by linarith, by linarith, ?_⟩
    simp only [imageDetour, sub_self, abs_zero, sub_zero,
      max_eq_right zero_le_one, ofReal_one, add_re, one_re]
    linarith
  have hcont : ContinuousAt m.forward (m.contour s) :=
    m.holomorphic_forward.continuousOn.continuousAt (m.isOpen_domain.mem_nhds (hγmem s))
  have hnhds : {z : ℂ | z ∈ m.domain ∧ m.forward z ∈ W} ∈ 𝓝 (m.contour s) := by
    have h := hcont.tendsto.eventually
      (hW.mem_nhds (by rw [hforwardγ]; exact hcenter))
    exact inter_mem (m.isOpen_domain.mem_nhds (hγmem s)) h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hηavoid (z : ℂ) (hz : z ∈ Metric.ball (m.contour s) ε) :
      z ∉ range (m.localDetour s) := by
    obtain ⟨-, -, -, hright⟩ := hball hz
    rintro ⟨t, ht⟩
    have heq : imageDetour s t = m.forward z :=
      (hforwardη t).symm.trans (congrArg m.forward ht)
    have hti : t = (m.forward z).im := (hδim t).symm.trans (congrArg Complex.im heq)
    have hre := congrArg Complex.re heq
    rw [hti] at hre
    exact hright.ne hre.symm
  refine ⟨ε, hε, (fun z hz ↦ (hball hz).1), hηavoid, ?_⟩
  intro z hz hzγ
  obtain ⟨hzT, hlo, hhi, hright⟩ := hball hz
  have hne : (imageContour (m.forward z).im).re ≠ (m.forward z).re := by
    intro heq
    have himage : imageContour (m.forward z).im = m.forward z :=
      Complex.ext heq (hαim (m.forward z).im)
    apply hzγ
    refine ⟨(m.forward z).im, ?_⟩
    change m.inverse (imageContour (m.forward z).im) = z
    rw [himage, m.left_inverse z hzT]
  obtain ⟨hαpc, hδpc⟩ := imageContour_and_imageDetour_piecewiseC1 s (s - 1) (s + 1)
  have ha : imageContour (s - 1) = imageDetour s (s - 1) := by
    have hsub : s - 1 - s = -1 := by ring
    simp [imageDetour, hsub]
  have hb : imageContour (s + 1) = imageDetour s (s + 1) := by
    have hsub : s + 1 - s = 1 := by ring
    simp [imageDetour, hsub]
  have hgraph := windingNumber_graph_difference hαpc hδpc
    (fun t _ ↦ hαim t) (fun t _ ↦ hδim t) ha hb ⟨hlo, hhi⟩ hne hright
  have hendpoint : 2 * (s + 1) - (s - 1) = s + 3 := by ring
  rw [← m.localDetour_windingNumber_forward s hzT hzγ (hηavoid z hz)]
  simpa only [hendpoint, hαre, NormalizedModel.core, mem_setOf_eq, hzT, true_and] using hgraph

#print axioms NormalizedModel.localDetour_windingNumber

end MaxModulusPoints.CauchyApproximation
