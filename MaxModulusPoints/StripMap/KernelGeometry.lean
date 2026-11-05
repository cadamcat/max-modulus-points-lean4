module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.Growth

/-!
# Geometry of the rescaled logarithmic targets

Positive dilations of the logarithmic target contain the right half-plane.
On every bounded set their leftward overhang tends uniformly to zero as
the dilation scale tends to infinity.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

universe u

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

def scaledTarget (t : ℝ) : Set ℂ := {z | (t : ℂ) * z ∈ target}

theorem halfPlane_subset_scaledTarget {t : ℝ} (ht : 0 < t) :
    {z : ℂ | 0 < z.re} ⊆ scaledTarget t := by
  intro z hz
  have hre : 0 < ((t : ℂ) * z).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using mul_pos ht hz
  change -14 * max 0 (Real.log |((t : ℂ) * z).im|) < ((t : ℂ) * z).re
  have hlog : 0 ≤ max 0 (Real.log |((t : ℂ) * z).im|) := le_max_left _ _
  exact lt_of_le_of_lt (by nlinarith) hre

theorem scaledTarget_real_lower_bound {t R : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ scaledTarget t) (hR : ‖z‖ ≤ R) :
    -(14 * Real.posLog (t * R) / t) < z.re := by
  have him : |((t : ℂ) * z).im| ≤ t * R := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm z).trans hR) ht.le
  have hlog := Real.posLog_le_posLog
    (by linarith [abs_nonneg ((t : ℂ) * z).im] : -1 ≤ |((t : ℂ) * z).im|) him
  have htarget : -14 * Real.posLog |((t : ℂ) * z).im| < t * z.re := by
    simpa only [scaledTarget, target, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Real.posLog] using hz
  rw [← neg_div]
  apply (div_lt_iff₀ ht).mpr
  nlinarith

theorem posLog_mul_div_tendsto_zero (R : ℝ) :
    Tendsto (fun t : ℝ => Real.posLog (t * R) / t) atTop (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ => Real.posLog t / t) atTop (𝓝 0) := by
    apply Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.posLog_eq_log (ht.trans (le_abs_self t))]
    rfl
  have hc : Tendsto (fun t : ℝ => Real.posLog R / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsum : Tendsto (fun t : ℝ => (Real.posLog t + Real.posLog R) / t) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using hlog.add hc
  apply squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact div_nonneg Real.posLog_nonneg ht.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact div_le_div_of_nonneg_right Real.posLog_mul ht.le

/-- The rescaled targets lie eventually within any prescribed small distance
to the left of the right half-plane, on each fixed bounded set. -/
theorem scaledTarget_eventually_real_lower_bound (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ z ∈ scaledTarget t, ‖z‖ ≤ R → -ε < z.re := by
  have hlim : Tendsto (fun t : ℝ => 14 * Real.posLog (t * R) / t) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using (posLog_mul_div_tendsto_zero R).const_mul 14
  have he := (tendsto_order.mp hlim).2 ε hε
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with t ht hpos z hz hR
  exact (neg_lt_neg ht).trans (scaledTarget_real_lower_bound hpos hz hR)

/-- A finite limit of points in targets whose scale escapes has nonnegative real part. -/
theorem scaledTarget_limit_re_nonneg {ι : Type u} {l : Filter ι} [NeBot l]
    {t : ι → ℝ} {w : ι → ℂ} {w₀ : ℂ} (ht : Tendsto t l atTop)
    (hw : Tendsto w l (𝓝 w₀)) (hmem : ∀ᶠ i in l, w i ∈ scaledTarget (t i)) :
    0 ≤ w₀.re := by
  by_contra hn
  have hn' : w₀.re < 0 := lt_of_not_ge hn
  have hε : 0 < -w₀.re / 2 := by linarith
  have hb : ∀ᶠ i in l, ‖w i‖ ≤ ‖w₀‖ + 1 :=
    ((tendsto_order.mp hw.norm).2 (‖w₀‖ + 1) (by linarith)).mono fun _ hi => hi.le
  have hs := ht.eventually
    (scaledTarget_eventually_real_lower_bound (‖w₀‖ + 1) (-w₀.re / 2) hε)
  have hlow : ∀ᶠ i in l, -(-w₀.re / 2) ≤ (w i).re := by
    filter_upwards [hb, hs, hmem] with i hi hsi hmi
    exact (hsi (w i) hmi hi).le
  have hlim := ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hw) hlow
  linarith

theorem scaledTarget_subset_slitPlane {t : ℝ} (ht : 0 < t) :
    scaledTarget t ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    have hpos : 0 < t * z.re := by
      simpa only [scaledTarget, target, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, hi, mul_zero, add_zero,
        abs_zero, Real.log_zero, max_self] using hz
    exact (mul_pos_iff_of_pos_left ht).mp hpos
  · exact Or.inr hi

end MaxModulusPoints.StripMap
