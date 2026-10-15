import TauCeti.Analysis.Complex.Conformal.LengthArea
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Order.IntermediateValue
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.TargetGeometry
import MaxModulusPoints.TractGeometry.TargetGeometryProof
/-!
# Restricted circular lengths in the logarithmic target

Restricting an injective holomorphic map to the inverse image of a small
disk gives an area bound proportional to the squared radius. A fixed-ratio
annulus therefore contains a short restricted circular image. Such a circle
cannot carry an arc whose image norm decreases from the radius to half of it.
-/

namespace MaxModulusPoints.WallGrowth

open Set Filter Metric Complex MeasureTheory Blueprint TractGeometry
open scoped Topology ENNReal Real

private theorem logPlus_mono_abs {u v : ℝ} (h : |u| ≤ |v|) :
    max 0 (Real.log |u|) ≤ max 0 (Real.log |v|) := by
  by_cases hu : |u| ≤ 1
  · rw [max_eq_left (Real.log_nonpos (abs_nonneg u) hu)]
    exact le_max_left _ _
  · exact max_le_max le_rfl (Real.log_le_log (by linarith [abs_nonneg u]) h)

private theorem target_positive_circle_arc {ρ a : ℝ} (hρ : 1 < ρ)
    (ha : a ∈ Icc 0 Real.pi) (hw : circleMap 0 ρ a ∈ target)
    {t : ℝ} (ht : t ∈ Icc 0 a) : circleMap 0 ρ t ∈ target := by
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  change -14 * max 0 (Real.log |(circleMap 0 ρ a).im|) <
    (circleMap 0 ρ a).re at hw
  change -14 * max 0 (Real.log |(circleMap 0 ρ t).im|) <
    (circleMap 0 ρ t).re
  simp only [circleMap_zero_re, circleMap_zero_im] at hw ⊢
  rcases lt_trichotomy t (Real.pi / 2) with hlt | heq | hgt
  · have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], hlt⟩
    have hm := le_max_left (0 : ℝ) (Real.log |ρ * Real.sin t|)
    have hp := mul_pos hρpos hc
    linarith
  · rw [heq, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one,
      abs_of_pos hρpos]
    have hl : 0 < Real.log ρ := Real.log_pos hρ
    rw [max_eq_right hl.le]
    linarith
  · have hcos : Real.cos a ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht.1 ha.2 ht.2
    have hsin : Real.sin a ≤ Real.sin t := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ t - Real.pi / 2 by linarith)
        (show a - Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos, ha.2])
        (sub_le_sub_right ht.2 (Real.pi / 2))
      simpa only [Real.cos_sub_pi_div_two] using h
    have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_mem_Icc ha
    have hst : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ⟨ht.1, ht.2.trans ha.2⟩
    have habs : |ρ * Real.sin a| ≤ |ρ * Real.sin t| := by
      rw [abs_of_nonneg (mul_nonneg hρpos.le hsa),
        abs_of_nonneg (mul_nonneg hρpos.le hst)]
      exact mul_le_mul_of_nonneg_left hsin hρpos.le
    have hlog := logPlus_mono_abs habs
    have hre := mul_le_mul_of_nonneg_left hcos hρpos.le
    linarith

/-- A continuous arc descending through a level has a last crossing of that
level, after which it stays below it. -/
theorem exists_last_crossing {g : ℝ → ℝ} {a b r : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (ha : r ≤ g a) (hb : g b < r) :
    ∃ c ∈ Icc a b, g c = r ∧ ∀ t ∈ Icc c b, g t ≤ r := by
  obtain ⟨d, hd, hdr⟩ := isPreconnected_Icc.intermediate_value
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hg ⟨hb.le, ha⟩
  let K := Icc a b ∩ g ⁻¹' {r}
  have hKclosed : IsClosed K :=
    hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
  obtain ⟨c, hc, hmax⟩ := hKcompact.exists_isGreatest ⟨d, hd, hdr⟩
  refine ⟨c, hc.1, hc.2, ?_⟩
  intro t ht
  by_contra h
  have hgt : r < g t := lt_of_not_ge h
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc (hc.1.1.trans ht.1) le_rfl
  obtain ⟨d', hd', hd'r⟩ := isPreconnected_Icc.intermediate_value
    (show b ∈ Icc t b from ⟨ht.2, le_rfl⟩)
    (show t ∈ Icc t b from ⟨le_rfl, ht.2⟩) (hg.mono hsub) ⟨hb.le, hgt.le⟩
  have hdc : d' ≤ c := hmax ⟨hsub hd', hd'r⟩
  have heq : t = c := le_antisymm (hd'.1.trans hdc) ht.1
  have hcr : g c = r := hc.2
  rw [heq, hcr] at hgt
  exact lt_irrefl _ hgt

/-- A target-circle arc dropping from radius r to below r/2 contributes
at least r/2 to the length restricted to the inverse image of the closed disk. -/
theorem cutoff_circle_length_lower {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f target) {ρ r : ℝ} (hρ : 1 < ρ) (hr : 0 < r)
    {w : ℂ} (hw : w ∈ target) (hnorm : ‖w‖ = ρ) (harg : 0 ≤ w.arg)
    (hstart : r ≤ ‖f (ρ : ℂ)‖) (hend : ‖f w‖ < r / 2) :
    ENNReal.ofReal (r / 2) ≤
      TauCeti.circleImageLength f {q ∈ target | ‖f q‖ ≤ r} 0 ρ := by
  have hrepr : circleMap 0 ρ w.arg = w := by
    rw [circleMap_zero, ← hnorm]
    exact Complex.norm_mul_exp_arg_mul_I w
  have hzero : circleMap 0 ρ 0 = (ρ : ℂ) := by simp [circleMap_zero]
  have hargmem : circleMap 0 ρ w.arg ∈ target := by rwa [hrepr]
  have hmem {t : ℝ} (ht : t ∈ Icc 0 w.arg) : circleMap 0 ρ t ∈ target :=
    target_positive_circle_arc hρ ⟨harg, Complex.arg_le_pi w⟩ hargmem ht
  have hg : ContinuousOn (fun t => ‖f (circleMap 0 ρ t)‖) (Icc 0 w.arg) :=
    (hf.continuousOn.comp (continuous_circleMap 0 ρ).continuousOn
      (fun _ ht => hmem ht)).norm
  obtain ⟨c, hc, hcr, htail⟩ := exists_last_crossing harg hg
    (show r ≤ ‖f (circleMap 0 ρ 0)‖ by rwa [hzero])
    (show ‖f (circleMap 0 ρ w.arg)‖ < r by rw [hrepr]; linarith)
  have hlength := TauCeti.ofReal_dist_le_circleImageLength
    (s := {q ∈ target | ‖f q‖ ≤ r})
    target_geometry.open_domain hf 0 (zero_lt_one.trans hρ) hc.2
    (show w.arg ≤ c + 2 * Real.pi by linarith [Complex.arg_le_pi w, Real.pi_pos, hc.1])
    (fun t ht => ⟨hmem ⟨hc.1.trans ht.1, ht.2⟩, htail t ht⟩)
    (fun t ht => hmem ⟨hc.1.trans ht.1, ht.2⟩)
  rw [hrepr] at hlength
  have hdist : r / 2 ≤ dist (f (circleMap 0 ρ c)) (f w) := by
    have htri := norm_le_norm_add_norm_sub' (f (circleMap 0 ρ c)) (f w)
    rw [hcr] at htri
    rw [dist_eq_norm]
    linarith
  exact (ENNReal.ofReal_le_ofReal hdist).trans hlength

private theorem cutoff_image_volume_le {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    volume (f '' {q ∈ target | ‖f q‖ ≤ r}) ≤ ENNReal.ofReal (4 * r ^ 2) := by
  let K := Complex.measurableEquivRealProd ⁻¹' (Icc (-r) r ×ˢ Icc (-r) r)
  have hvol : volume K = ENNReal.ofReal (4 * r ^ 2) := by
    rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ r - -r)]
    congr 1
    ring
  rw [← hvol]
  apply measure_mono
  rintro _ ⟨q, hq, rfl⟩
  have hre : |(f q).re| ≤ r := (Complex.abs_re_le_norm _).trans hq.2
  have him : |(f q).im| ≤ r := (Complex.abs_im_le_norm _).trans hq.2
  exact ⟨abs_le.mp hre, abs_le.mp him⟩

/-- A fixed multiplicative annulus contains a circle whose restricted image
length is less than half the cutoff radius. -/
theorem exists_short_cutoff_circle {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f target) (hinj : InjOn f target)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ∃ ρ ∈ Ioo R (R * Real.exp (64 * Real.pi)),
      TauCeti.circleImageLength f {q ∈ target | ‖f q‖ ≤ r} 0 ρ <
        ENNReal.ofReal (r / 2) := by
  let S := {q ∈ target | ‖f q‖ ≤ r}
  have hS : MeasurableSet S := by
    have hopen : IsOpen {q ∈ target | r < ‖f q‖} :=
      hf.continuousOn.norm.isOpen_inter_preimage target_geometry.open_domain isOpen_Ioi
    have heq : S = target \ {q ∈ target | r < ‖f q‖} := by
      ext q
      simp only [S, mem_ofPred_eq, Set.mem_sdiff, not_and, not_lt]
      tauto
    rw [heq]
    exact target_geometry.open_domain.measurableSet.diff hopen.measurableSet
  have hSQ : S ⊆ target := fun _ h => h.1
  have hratio : R < R * Real.exp (64 * Real.pi) := by
    have he : 1 < Real.exp (64 * Real.pi) := Real.one_lt_exp_iff.mpr (by positivity)
    nlinarith
  have hlog : Real.log (R * Real.exp (64 * Real.pi) / R) = 64 * Real.pi := by
    rw [mul_div_cancel_left₀ _ hR.ne', Real.log_exp]
  have harea : ENNReal.ofReal (2 * Real.pi) * volume (f '' S) <
      ENNReal.ofReal ((r / 2) ^ 2) *
        ENNReal.ofReal (Real.log (R * Real.exp (64 * Real.pi) / R)) := by
    have hupper : ENNReal.ofReal (2 * Real.pi) * volume (f '' S) ≤
        ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (4 * r ^ 2) := by
      exact mul_le_mul' le_rfl (cutoff_image_volume_le hr.le)
    apply lt_of_le_of_lt hupper
    rw [hlog, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi),
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    nlinarith [Real.pi_pos, sq_pos_of_pos hr]
  obtain ⟨ρ, hρ, hshort⟩ := TauCeti.exists_circleImageLength_sq_lt_of_volume_image
    target_geometry.open_domain hf hS hSQ (hinj.mono hSQ) 0 hR hratio harea
  refine ⟨ρ, hρ, ?_⟩
  rw [ENNReal.ofReal_pow (by positivity : 0 ≤ r / 2)] at hshort
  by_contra h
  have hle : ENNReal.ofReal (r / 2) ≤ TauCeti.circleImageLength f S 0 ρ := le_of_not_gt h
  have hsquare : ENNReal.ofReal (r / 2) ^ 2 ≤ TauCeti.circleImageLength f S 0 ρ ^ 2 := by
    gcongr
  exact (not_lt_of_ge hsquare) hshort

end MaxModulusPoints.WallGrowth
