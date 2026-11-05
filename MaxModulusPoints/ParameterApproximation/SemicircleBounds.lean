module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.ParameterApproximation.TargetMajorant
public import MaxModulusPoints.StripEstimates.HalfDisc

/-!
# Bounds on an upper semicircle from three interior values

Three unit disks tangent to the real axis cover the unit upper semicircle.
Their boundary-distance estimates, combined with the positive target
majorant, give the reciprocal-height bound used in harmonic comparison.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Metric Blueprint StripEstimates

private theorem side_distance_bound {x y d : ℝ}
    (hunit : x ^ 2 + y ^ 2 = 1) (hx : 1 / 2 ≤ x) (hy : 0 < y)
    (hd : 0 ≤ d) (hd2 : d ^ 2 = 3 - 2 * x - 2 * y) :
    y / 4 ≤ 1 - d := by
  have hx1 : x ≤ 1 := by nlinarith [sq_nonneg y]
  have hy1 : y ≤ 1 := by nlinarith [sq_nonneg x]
  have hp : 0 ≤ (1 - x) * (x - 1 / 2) := mul_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ y * (1 - y) := mul_nonneg hy.le (by linarith)
  have hsq : d ^ 2 ≤ (1 - y / 4) ^ 2 := by nlinarith
  have hr : 0 ≤ 1 - y / 4 := by linarith
  nlinarith

/-- One of three tangent disks contains an upper semicircle point with
boundary distance at least one quarter of its height. -/
theorem semicircle_tangent_disk_cover {z : ℂ} (hz : ‖z‖ = 1) (hy : 0 < z.im) :
    ∃ s : ℝ, (s = -1 ∨ s = 0 ∨ s = 1) ∧
      z.im / 4 ≤ 1 - dist z ((s : ℂ) + Complex.I) := by
  have hunit : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.sq_norm_sub_sq_re z
    rw [hz] at h
    nlinarith
  have hdist (s : ℝ) :
      dist z ((s : ℂ) + Complex.I) ^ 2 = (z.re - s) ^ 2 + (z.im - 1) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_re,
      add_zero, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
    ring
  by_cases hx : 1 / 2 ≤ z.re
  · refine ⟨1, Or.inr (Or.inr rfl), ?_⟩
    apply side_distance_bound hunit hx hy (dist_nonneg)
    nlinarith [hdist 1]
  · by_cases hx' : z.re ≤ -(1 / 2)
    · refine ⟨-1, Or.inl rfl, ?_⟩
      apply side_distance_bound (x := -z.re) (by nlinarith) (by linarith) hy dist_nonneg
      nlinarith [hdist (-1)]
    · refine ⟨0, Or.inr (Or.inl rfl), ?_⟩
      have hp : 0 ≤ (z.re + 1 / 2) * (1 / 2 - z.re) :=
        mul_nonneg (by linarith) (by linarith)
      have hy1 : z.im ≤ 1 := by nlinarith [sq_nonneg z.re]
      have hylo : 3 / 4 ≤ z.im := by nlinarith
      have hd := dist_nonneg (x := z) (y := ((0 : ℝ) : ℂ) + Complex.I)
      have hdle : dist z (((0 : ℝ) : ℂ) + Complex.I) ≤ 3 / 4 := by
        nlinarith [hdist 0]
      linarith

/-- Each tangent disk lies in a common upper half-disk of radius three. -/
theorem tangent_disk_subset_upperHalfDisc {s : ℝ} (hs : s = -1 ∨ s = 0 ∨ s = 1) :
    ball ((s : ℂ) + Complex.I) 1 ⊆ upperHalfDisc 3 := by
  intro z hz
  have hsabs : |s| ≤ 1 := by rcases hs with rfl | rfl | rfl <;> norm_num
  have hcenter : ‖(s : ℂ) + Complex.I‖ ≤ 2 := by
    calc
      _ ≤ ‖(s : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ ≤ 2 := by simpa only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I] using
        (show |s| + 1 ≤ 2 by linarith)
  have hdist : dist z ((s : ℂ) + Complex.I) < 1 := hz
  have hnorm : ‖z‖ < 3 := by
    calc
      _ ≤ ‖z - ((s : ℂ) + Complex.I)‖ + ‖(s : ℂ) + Complex.I‖ :=
        norm_le_norm_sub_add _ _
      _ < 3 := by rw [← dist_eq_norm]; linarith
  have him : |z.im - 1| < 1 := by
    have hi := Complex.abs_im_le_norm (z - ((s : ℂ) + Complex.I))
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
      Complex.I_im, zero_add] at hi
    exact hi.trans_lt (by simpa only [dist_eq_norm] using hdist)
  exact ⟨hnorm, by linarith [(abs_lt.mp him).1]⟩

/-- Three interior majorant values control the real part of a target map on
the whole upper unit semicircle. -/
theorem target_map_re_le_on_semicircle {G : ℂ → ℂ} {A : ℝ}
    (hG : DifferentiableOn ℂ G (upperHalfDisc 3))
    (hmaps : MapsTo G (upperHalfDisc 3) target)
    (hA : ∀ s : ℝ, s = -1 ∨ s = 0 ∨ s = 1 →
      ‖targetMajorant (G ((s : ℂ) + Complex.I))‖ ≤ A)
    {z : ℂ} (hz : ‖z‖ = 1) (hy : 0 < z.im) :
    (G z).re ≤ 8 * (1 + A) / z.im := by
  obtain ⟨s, hs, hd⟩ := semicircle_tangent_disk_cover hz hy
  have hsub := tangent_disk_subset_upperHalfDisc hs
  have hzball : z ∈ ball ((s : ℂ) + Complex.I) 1 := by
    change dist z ((s : ℂ) + Complex.I) < 1
    linarith
  have hbound := target_map_re_le_on_ball (by norm_num : (0 : ℝ) < 1)
    (hG.mono hsub) (hmaps.mono_left hsub) hzball
  have hnum : 0 ≤ 2 + 2 * ‖targetMajorant (G ((s : ℂ) + Complex.I))‖ := by positivity
  have hden : 0 < 1 - dist z ((s : ℂ) + Complex.I) := by linarith
  calc
    (G z).re ≤ (2 + 2 * ‖targetMajorant (G ((s : ℂ) + Complex.I))‖) /
        (1 - dist z ((s : ℂ) + Complex.I)) := by simpa only [mul_one] using hbound
    _ ≤ (2 + 2 * ‖targetMajorant (G ((s : ℂ) + Complex.I))‖) / (z.im / 4) :=
      div_le_div_of_nonneg_left hnum (by linarith) hd
    _ ≤ (2 + 2 * A) / (z.im / 4) :=
      div_le_div_of_nonneg_right (by linarith [hA s hs]) (by linarith)
    _ = 8 * (1 + A) / z.im := by ring

#print axioms semicircle_tangent_disk_cover
#print axioms target_map_re_le_on_semicircle

end MaxModulusPoints.ParameterApproximation
