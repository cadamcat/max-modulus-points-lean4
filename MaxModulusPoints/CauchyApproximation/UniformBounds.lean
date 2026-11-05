module

public import Mathlib.Topology.Connected.Clopen
public import MaxModulusPoints.CauchyApproximation.CanonicalDensity
public import MaxModulusPoints.CauchyApproximation.ContourDerivative
public import MaxModulusPoints.CauchyApproximation.ContourDistortion
public import MaxModulusPoints.CauchyApproximation.InverseDistortion
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.RealSymmetry

/-!
# Uniform bounds for normalized inverse conformal maps

The quarter theorem bounds the derivative of a univalent map omitting zero
by its value at the center of a disk. Disk distortion then compares nearby
values by a fixed factor. Connectedness propagates this comparison from the
normalization point, and a finite covering gives uniform value and derivative
bounds on compact subsets of the fixed image domain.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology BigOperators

namespace MaxModulusPoints.CauchyApproximation

/-- Omitting zero controls the derivative at the center of a univalence disk. -/
theorem norm_deriv_le_of_univalent_ball_omit_zero {f : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : UnivalentOn f (Metric.ball a R))
    (hzero : ∀ w ∈ Metric.ball a R, f w ≠ 0) :
    ‖deriv f a‖ ≤ 4 * ‖f a‖ / R := by
  have hquarter := univalent_ball_quarter hR hf
  have hb : R * ‖deriv f a‖ / 4 ≤ ‖f a‖ := by
    by_contra! h
    have hz : (0 : ℂ) ∈ Metric.ball (f a) (R * ‖deriv f a‖ / 4) := by
      simpa only [Metric.mem_ball, dist_zero_left] using h
    obtain ⟨w, hw, he⟩ := hquarter hz
    exact hzero w hw he
  apply (le_div_iff₀ hR).2
  nlinarith

/-- On the middle half of a univalence disk, omission of zero bounds values
by a universal multiple of the value at the center. -/
theorem norm_value_le_of_univalent_ball_omit_zero {f : ℂ → ℂ} {a z : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : UnivalentOn f (Metric.ball a R))
    (hzero : ∀ w ∈ Metric.ball a R, f w ≠ 0) (hz : ‖z - a‖ ≤ R / 2) :
    ‖f z‖ ≤ 33 * ‖f a‖ := by
  let u : ℂ := (z - a) / (R : ℂ)
  have hu : ‖u‖ ≤ (1 / 2 : ℝ) := by
    dsimp only [u]
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (div_le_iff₀ hR).2 (by linarith)
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf (Metric.mem_ball_self hR)
  have hb := schlicht_local_bound (ballNormalize_schlicht hR hf hn)
    (by norm_num : (1 / 2 : ℝ) < 1) hu
  norm_num at hb
  have heq : a + (R : ℂ) * u = z := by
    dsimp only [u]
    field_simp [ofReal_ne_zero.2 hR.ne']
    ring
  change ‖(f (a + (R : ℂ) * u) - f a) / ((R : ℂ) * deriv f a)‖ ≤ 8 at hb
  rw [heq, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hR] at hb
  have hdist := (div_le_iff₀ (mul_pos hR (norm_pos_iff.2 hn))).1 hb
  have hd := (le_div_iff₀ hR).1 (norm_deriv_le_of_univalent_ball_omit_zero hR hf hzero)
  have ht := norm_add_le (f z - f a) (f a)
  rw [sub_add_cancel] at ht
  nlinarith

private theorem inverse_norm_comparison (m₀ : NormalizedModel)
    {a b : ℂ} (ha : a ∈ modelHalfPlane) (hb : b ∈ modelHalfPlane) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : NormalizedModel, ‖m.inverse b‖ ≤ C * ‖m.inverse a‖ := by
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have himage : m₀.forward '' m₀.domain = modelHalfPlane := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact m₀.forward_mem hz
    · intro w hw
      exact ⟨m₀.inverse w, m₀.inverse_mem hw, m₀.right_inverse w hw⟩
  have hconn : IsPreconnected modelHalfPlane := by
    rw [← himage]
    exact m₀.simplyConnected_domain.isPathConnected.isConnected.isPreconnected.image
      m₀.forward m₀.holomorphic_forward.continuousOn
  let P : ℂ → ℂ → Prop := fun x y ↦
    ∃ C : ℝ, 0 < C ∧ ∀ m : NormalizedModel, ‖m.inverse y‖ ≤ C * ‖m.inverse x‖
  have hlocal (x : ℂ) (hx : x ∈ modelHalfPlane) :
      ∀ᶠ y in 𝓝[modelHalfPlane] x, P x y ∧ P y x := by
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hH x hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds x (by positivity : 0 < R / 4))] with y hy
    have hxy : ‖y - x‖ < R / 4 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hballY : Metric.ball y (R / 2) ⊆ modelHalfPlane := by
      intro v hv
      apply hball
      have hv' : ‖v - y‖ < R / 2 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hv
      have ht := norm_add_le (v - y) (y - x)
      rw [sub_add_sub_cancel] at ht
      simpa only [Metric.mem_ball, dist_eq_norm] using (show ‖v - x‖ < R by linarith)
    constructor
    · refine ⟨33, by norm_num, ?_⟩
      intro m
      exact norm_value_le_of_univalent_ball_omit_zero hR
        ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
        (fun w hw he ↦ m.zero_not_mem (he ▸ m.inverse_mem (hball hw))) (by linarith)
    · refine ⟨33, by norm_num, ?_⟩
      intro m
      apply norm_value_le_of_univalent_ball_omit_zero (by positivity : 0 < R / 2)
        ⟨m.holomorphic_inverse.mono hballY, m.univalentOn_inverse.2.mono hballY⟩
        (fun w hw he ↦ m.zero_not_mem (he ▸ m.inverse_mem (hballY hw)))
      rw [norm_sub_rev]
      linarith
  apply hconn.induction₂' P hlocal ?_ ha hb
  intro x y z _ _ _ hxy hyz
  obtain ⟨C, hC, hCb⟩ := hxy
  obtain ⟨D, hD, hDb⟩ := hyz
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro m
  calc
    _ ≤ D * ‖m.inverse y‖ := hDb m
    _ ≤ D * (C * ‖m.inverse x‖) := mul_le_mul_of_nonneg_left (hCb m) hD.le
    _ = _ := by ring

/-- The actual inverse maps and their derivatives are uniformly bounded on
each compact subset of the fixed image domain. -/
theorem exists_uniform_inverse_bounds_on_compact {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ modelHalfPlane) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (w : ℂ), w ∈ K →
      ‖m.inverse w‖ ≤ C ∧ ‖deriv m.inverse w‖ ≤ C := by
  classical
  by_cases hnonempty : Nonempty NormalizedModel
  · obtain ⟨m₀⟩ := hnonempty
    have hH : IsOpen modelHalfPlane := by
      apply isOpen_lt <;> fun_prop
    have hone : (1 : ℂ) ∈ modelHalfPlane := by
      simp [modelHalfPlane, Real.posLog_zero]
    have honeval (m : NormalizedModel) : ‖m.inverse 1‖ = Real.exp (-1) := by
      have hi : m.inverse 1 = Complex.exp (-1) := by
        simpa only [m.base_value] using m.left_inverse _ m.base_mem
      rw [hi, Complex.norm_exp]
      norm_num
    have hlocal (x : K) : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (m : NormalizedModel) (y : ℂ), y ∈ Metric.ball (x : ℂ) r →
          ‖m.inverse y‖ ≤ C ∧ ‖deriv m.inverse y‖ ≤ C := by
      obtain ⟨A, hA, hAb⟩ := inverse_norm_comparison m₀ hone (hKH x.2)
      obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hH (x : ℂ) (hKH x.2)
      let B : ℝ := A * Real.exp (-1)
      have hB : 0 < B := mul_pos hA (Real.exp_pos _)
      have hxval (m : NormalizedModel) : ‖m.inverse x‖ ≤ B := by
        simpa only [honeval, B] using hAb m
      refine ⟨R / 4, by positivity, 33 * B + 264 * B / R + 1, by positivity, ?_⟩
      intro m y hy
      have hxy : ‖y - (x : ℂ)‖ < R / 4 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have hval : ‖m.inverse y‖ ≤ 33 * B :=
        (norm_value_le_of_univalent_ball_omit_zero hR
          ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
          (fun w hw he ↦ m.zero_not_mem (he ▸ m.inverse_mem (hball hw)))
          (by linarith)).trans (mul_le_mul_of_nonneg_left (hxval m) (by norm_num))
      have hballY : Metric.ball y (R / 2) ⊆ modelHalfPlane := by
        intro v hv
        apply hball
        have hv' : ‖v - y‖ < R / 2 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hv
        have ht := norm_add_le (v - y) (y - (x : ℂ))
        rw [sub_add_sub_cancel] at ht
        simpa only [Metric.mem_ball, dist_eq_norm] using
          (show ‖v - (x : ℂ)‖ < R by linarith)
      have hd := norm_deriv_le_of_univalent_ball_omit_zero (by positivity : 0 < R / 2)
        ⟨m.holomorphic_inverse.mono hballY, m.univalentOn_inverse.2.mono hballY⟩
        (fun w hw he ↦ m.zero_not_mem (he ▸ m.inverse_mem (hballY hw)))
      have hderiv : ‖deriv m.inverse y‖ ≤ 264 * B / R := by
        calc
          _ ≤ 4 * ‖m.inverse y‖ / (R / 2) := hd
          _ ≤ 4 * (33 * B) / (R / 2) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hval (by norm_num))
              (by positivity)
          _ = _ := by ring
      constructor <;> linarith [show 0 ≤ 33 * B by positivity,
        show 0 ≤ 264 * B / R by positivity]
    choose r hr C hC hb using hlocal
    obtain ⟨s, hs⟩ := hK.elim_nhds_subcover'
      (fun x hx ↦ Metric.ball x (r ⟨x, hx⟩))
      (fun x hx ↦ Metric.ball_mem_nhds x (hr ⟨x, hx⟩))
    let B : ℝ := 1 + ∑ x ∈ s, C x
    have hsum : 0 ≤ ∑ x ∈ s, C x := Finset.sum_nonneg (fun x _ ↦ (hC x).le)
    refine ⟨B, by dsimp only [B]; linarith, ?_⟩
    intro m w hw
    obtain ⟨x, hxs, hxw⟩ := mem_iUnion₂.1 (hs hw)
    have hxB : C x ≤ B := by
      have hle : C x ≤ ∑ y ∈ s, C y :=
        Finset.single_le_sum (fun y _ ↦ (hC y).le) hxs
      dsimp only [B]
      linarith
    exact ⟨((hb x m w hxw).1).trans hxB, ((hb x m w hxw).2).trans hxB⟩
  · exact ⟨1, zero_lt_one, fun m ↦ False.elim (hnonempty ⟨m⟩)⟩

/-- One constant bounds the inverse derivative on the entire canonical
contour, uniformly over every normalized conformal map. -/
theorem exists_uniform_inverse_deriv_contour_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (t : ℝ),
      ‖deriv m.inverse (imageContour t)‖ ≤ C * (max |t| 1) ^ 4 := by
  obtain ⟨T, hT, htail⟩ := exists_uniform_inverse_deriv_contour_tail_bound
  have hK : IsCompact (imageContour '' Icc (-T) T) :=
    isCompact_Icc.image lipschitzWith_imageContour.continuous
  obtain ⟨B, hB, hb⟩ := exists_uniform_inverse_bounds_on_compact hK
    (by rintro _ ⟨t, _, rfl⟩; exact imageContour_mem_modelHalfPlane t)
  let C : ℝ := max (3936600 * Real.exp (-1)) B
  have hC : 0 < C := lt_of_lt_of_le hB (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro m t
  by_cases ht : T ≤ |t|
  · exact (htail m t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hmid : t ∈ Icc (-T) T := abs_le.1 (le_of_lt (lt_of_not_ge ht))
    have hp : 1 ≤ (max |t| 1) ^ 4 := one_le_pow₀ (le_max_right _ _)
    calc
      _ ≤ B := (hb m (imageContour t) ⟨t, hmid, rfl⟩).2
      _ ≤ C := le_max_right _ _
      _ ≤ C * (max |t| 1) ^ 4 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hC.le

#print axioms norm_deriv_le_of_univalent_ball_omit_zero
#print axioms norm_value_le_of_univalent_ball_omit_zero
#print axioms exists_uniform_inverse_bounds_on_compact
#print axioms exists_uniform_inverse_deriv_contour_bound

end MaxModulusPoints.CauchyApproximation
