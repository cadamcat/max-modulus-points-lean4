import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MaxModulusPoints.Blueprint.Data
/-!
# A positive real majorant on the logarithmic target

The holomorphic function w + 14 log(w + 1) has positive real part on the
logarithmically enlarged half-plane, and its real part majorizes Re w.
Borel–Carathéodory therefore bounds conformal maps into that target from
their value at the center of any source disk.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Metric Blueprint

/-- A holomorphic majorant adapted to the logarithmic target. -/
def targetMajorant (w : ℂ) : ℂ := w + 14 * Complex.log (w + 1)

/-- Translation by one keeps the target in the principal logarithm's domain. -/
theorem target_add_one_mem_slitPlane {w : ℂ} (hw : w ∈ target) :
    w + 1 ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hy : w.im = 0
  · have hre : 0 < w.re := by simpa [target, hy] using hw
    left
    simp only [Complex.add_re, Complex.one_re]
    linarith
  · right
    simpa only [Complex.add_im, Complex.one_im, add_zero] using hy

/-- The translated target stays outside the open unit disk. -/
theorem one_le_norm_target_add_one {w : ℂ} (hw : w ∈ target) :
    1 ≤ ‖w + 1‖ := by
  have him : |w.im| ≤ ‖w + 1‖ := by
    simpa only [Complex.add_im, Complex.one_im, add_zero] using
      Complex.abs_im_le_norm (w + 1)
  by_cases hy : |w.im| ≤ 1
  · have hl : Real.log |w.im| ≤ 0 := Real.log_nonpos (abs_nonneg _) hy
    have hre : 0 < w.re := by
      have ht := hw
      change -14 * max 0 (Real.log |w.im|) < w.re at ht
      rwa [max_eq_left hl, mul_zero] at ht
    have hr : w.re + 1 ≤ ‖w + 1‖ := by
      simpa only [Complex.add_re, Complex.one_re] using Complex.re_le_norm (w + 1)
    linarith
  · exact (lt_of_not_ge hy).le.trans him

/-- The majorant is holomorphic on the entire fixed target. -/
theorem differentiableOn_targetMajorant : DifferentiableOn ℂ targetMajorant target := by
  have hl : DifferentiableOn ℂ (fun w : ℂ => Complex.log (w + 1)) target :=
    (differentiable_id.add_const 1).differentiableOn.clog
      (fun _ hw => target_add_one_mem_slitPlane hw)
  exact differentiable_id.differentiableOn.add (hl.const_mul 14)

/-- The real part of the majorant is positive and dominates the original
real coordinate. -/
theorem targetMajorant_re_bounds {w : ℂ} (hw : w ∈ target) :
    w.re ≤ (targetMajorant w).re ∧ 0 < (targetMajorant w).re := by
  have heq : (targetMajorant w).re = w.re + 14 * Real.log ‖w + 1‖ := by
    simp [targetMajorant, Complex.mul_re, Complex.log_re]
  have hlog : 0 ≤ Real.log ‖w + 1‖ :=
    Real.log_nonneg (one_le_norm_target_add_one hw)
  rw [heq]
  constructor
  · linarith
  · by_cases hy : |w.im| ≤ 1
    · have hl : Real.log |w.im| ≤ 0 := Real.log_nonpos (abs_nonneg _) hy
      have hre : 0 < w.re := by
        have ht := hw
        change -14 * max 0 (Real.log |w.im|) < w.re at ht
        rwa [max_eq_left hl, mul_zero] at ht
      linarith
    · have hy' : 1 < |w.im| := lt_of_not_ge hy
      have hylog : 0 ≤ Real.log |w.im| := Real.log_nonneg hy'.le
      have hre : -14 * Real.log |w.im| < w.re := by
        have ht := hw
        change -14 * max 0 (Real.log |w.im|) < w.re at ht
        rwa [max_eq_right hylog] at ht
      have him : |w.im| ≤ ‖w + 1‖ := by
        simpa only [Complex.add_im, Complex.one_im, add_zero] using
          Complex.abs_im_le_norm (w + 1)
      have hcomp := Real.log_le_log (lt_trans zero_lt_one hy') him
      linarith

/-- A map into the target has a reciprocal-distance real upper bound on any
source disk, controlled by one interior value of the majorant. -/
theorem target_map_re_le_on_ball {G : ℂ → ℂ} {a z : ℂ} {R : ℝ}
    (hR : 0 < R) (hG : DifferentiableOn ℂ G (ball a R))
    (hmaps : MapsTo G (ball a R) target) (hz : z ∈ ball a R) :
    (G z).re ≤ (2 + 2 * ‖targetMajorant (G a)‖) * R / (R - dist z a) := by
  let H : ℂ → ℂ := fun w => targetMajorant (G (a + w))
  have ht : MapsTo (fun w : ℂ => a + w) (ball 0 R) (ball a R) := by
    intro w hw
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have hH : DifferentiableOn ℂ H (ball 0 R) :=
    (differentiableOn_targetMajorant.comp hG hmaps).comp
      ((differentiable_const a).add differentiable_id).differentiableOn ht
  have hHre : MapsTo (fun w => -H w) (ball 0 R) {v : ℂ | v.re ≤ 1} := by
    intro w hw
    have hpos := (targetMajorant_re_bounds (hmaps (ht hw))).2
    change (-H w).re ≤ 1
    simp only [Complex.neg_re]
    change -(targetMajorant (G (a + w))).re ≤ 1
    linarith
  have hza : z - a ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
  have hb := Complex.borelCaratheodory (by norm_num : (0 : ℝ) < 1)
    hH.neg hHre hR hza
  have haz : a + (z - a) = z := by ring
  simp only [Pi.neg_apply, H, norm_neg, haz, add_zero, mul_one] at hb
  have hd : 0 ≤ ‖z - a‖ := norm_nonneg _
  have hdr : ‖z - a‖ < R := mem_ball_zero_iff.mp hza
  have hden : 0 < R - ‖z - a‖ := sub_pos.mpr hdr
  have hn : 0 ≤ ‖targetMajorant (G a)‖ := norm_nonneg _
  have h₁ : 2 * ‖z - a‖ / (R - ‖z - a‖) ≤ 2 * R / (R - ‖z - a‖) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have h₂ : ‖targetMajorant (G a)‖ * (R + ‖z - a‖) / (R - ‖z - a‖) ≤
      ‖targetMajorant (G a)‖ * (2 * R) / (R - ‖z - a‖) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hn) hden.le
  calc
    (G z).re ≤ (targetMajorant (G z)).re := (targetMajorant_re_bounds (hmaps hz)).1
    _ ≤ ‖targetMajorant (G z)‖ := Complex.re_le_norm _
    _ ≤ 2 * ‖z - a‖ / (R - ‖z - a‖) +
        ‖targetMajorant (G a)‖ * (R + ‖z - a‖) / (R - ‖z - a‖) := hb
    _ ≤ 2 * R / (R - ‖z - a‖) +
        ‖targetMajorant (G a)‖ * (2 * R) / (R - ‖z - a‖) := add_le_add h₁ h₂
    _ = (2 + 2 * ‖targetMajorant (G a)‖) * R / (R - dist z a) := by
      rw [dist_eq_norm]
      ring

#print axioms targetMajorant_re_bounds
#print axioms differentiableOn_targetMajorant
#print axioms target_map_re_le_on_ball

end MaxModulusPoints.ParameterApproximation
