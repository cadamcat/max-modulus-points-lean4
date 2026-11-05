module

public import MaxModulusPoints.CauchyApproximation.CanonicalDensity
public import MaxModulusPoints.CauchyApproximation.ContourDerivative
public import MaxModulusPoints.CauchyApproximation.ContourDistortion
public import MaxModulusPoints.CauchyApproximation.InverseDistortion
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.UniformBounds

/-!
# Distortion relative to the normalization derivative

The derivative scale at the normalization point is retained in both
directions. Comparisons on the right-hand line transfer to the contour
tails by disk distortion. Compact derivative comparisons cover the middle
interval without imposing a positive absolute lower bound on the scale.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology BigOperators

namespace MaxModulusPoints.CauchyApproximation

/-- Lower disk distortion compares the derivative with that at the center
of the same univalence disk. -/
theorem norm_deriv_ge_of_univalent_ball {f : ℂ → ℂ} {a z : ℂ} {R q : ℝ}
    (hR : 0 < R) (hf : UnivalentOn f (Metric.ball a R)) (hq : q < 1)
    (hz : ‖z - a‖ ≤ q * R) :
    ((1 - q) / 8) * ‖deriv f a‖ ≤ ‖deriv f z‖ := by
  let u : ℂ := (z - a) / (R : ℂ)
  have hu : ‖u‖ ≤ q := by
    dsimp only [u]
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (div_le_iff₀ hR).2 hz
  have hudisk : u ∈ disk := by
    simpa only [disk, Metric.mem_ball, dist_zero_right] using hu.trans_lt hq
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf (Metric.mem_ball_self hR)
  have hb := (schlicht_deriv_bounds (ballNormalize_schlicht hR hf hn) hudisk).1
  rw [(ballNormalize_deriv hR hf.1 hudisk).deriv] at hb
  have heq : a + (R : ℂ) * u = z := by
    dsimp only [u]
    field_simp [ofReal_ne_zero.2 hR.ne']
    ring
  rw [heq, norm_div (deriv f z) (deriv f a)] at hb
  have hden : (1 + ‖u‖) ^ 3 ≤ (8 : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖u‖)
      (by linarith : 1 + ‖u‖ ≤ 2) 3
    norm_num at h
    exact h
  have hlow : (1 - q) / 8 ≤ (1 - ‖u‖) / (1 + ‖u‖) ^ 3 :=
    div_le_div₀ (by linarith) (by linarith) (by positivity) hden
  exact (le_div_iff₀ (norm_pos_iff.2 hn)).1 (hlow.trans hb)

/-- Imaginary translation of the right half-plane gives a derivative
comparison between any two points on the line of real part one. -/
theorem NormalizedModel.norm_inverse_deriv_vertical_comparison (m : NormalizedModel)
    (s t : ℝ) : ‖deriv m.inverse (1 + (t : ℂ) * I)‖ ≤
      (25 * (max |t - s| 1) ^ 4) * ‖deriv m.inverse (1 + (s : ℂ) * I)‖ := by
  let f : ℂ → ℂ := fun w ↦ m.inverse (-I * w + (s : ℂ) * I)
  have hmem {w : ℂ} (hw : w ∈ halfPlane) :
      -I * w + (s : ℂ) * I ∈ modelHalfPlane := by
    have hre : (-I * w + (s : ℂ) * I).re = w.im := by
      simp [mul_re]
    change -14 * Real.posLog |(-I * w + (s : ℂ) * I).im| <
      (-I * w + (s : ℂ) * I).re
    rw [hre]
    have hw' : 0 < w.im := hw
    linarith [Real.posLog_nonneg (x := |(-I * w + (s : ℂ) * I).im|)]
  have hH : IsOpen modelHalfPlane := by
    apply isOpen_lt <;> fun_prop
  have hd {w : ℂ} (hw : w ∈ halfPlane) :
      HasDerivAt f (deriv m.inverse (-I * w + (s : ℂ) * I) * (-I)) w := by
    have hlin : HasDerivAt (fun w : ℂ ↦ -I * w + (s : ℂ) * I) (-I) w := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id w).const_mul (-I)).add_const ((s : ℂ) * I)
    exact (m.holomorphic_inverse.differentiableAt (hH.mem_nhds (hmem hw))).hasDerivAt.comp w
      hlin
  have hu : UnivalentOn f halfPlane := by
    refine ⟨fun w hw ↦ (hd hw).differentiableAt.differentiableWithinAt, ?_⟩
    intro w hw v hv he
    exact mul_left_cancel₀ (by simp : (-I : ℂ) ≠ 0)
      (add_right_cancel (m.univalentOn_inverse.2 (hmem hw) (hmem hv) he))
  let z : ℂ := -((t - s : ℝ) : ℂ) + I
  have hz : z ∈ halfPlane := by simp [z, halfPlane]
  have hI : I ∈ halfPlane := by simp [halfPlane]
  have hzval : -I * z + (s : ℂ) * I = 1 + (t : ℂ) * I := by
    simp only [z, ofReal_sub]
    ring_nf
    simp only [I_sq]
    ring
  have hIval : -I * I + (s : ℂ) * I = 1 + (s : ℂ) * I := by
    simp only [neg_mul, I_mul_I, neg_neg]
  have hnorm (w : ℂ) (hw : w ∈ halfPlane) :
      ‖deriv f w‖ = ‖deriv m.inverse (-I * w + (s : ℂ) * I)‖ := by
    rw [(hd hw).deriv, norm_mul]
    simp only [norm_neg, norm_I, mul_one]
  have hb := univalent_halfPlane_norm_deriv_le hu hz
  rw [hnorm z hz, hnorm I hI, hzval, hIval] at hb
  have hsq : ‖z + I‖ ^ 2 = (t - s) ^ 2 + 4 := by
    rw [Complex.sq_norm]
    simp only [z, Complex.normSq_apply, add_re, add_im, neg_re, neg_im,
      ofReal_re, ofReal_im, I_re, I_im, add_zero, zero_add, neg_zero]
    ring
  have hfour : ‖z + I‖ ^ 4 = ((t - s) ^ 2 + 4) ^ 2 := by
    calc
      _ = (‖z + I‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have hzIm : z.im = 1 := by simp [z]
  rw [hfour, hzIm, one_pow, div_one] at hb
  have hr : 1 ≤ max |t - s| 1 := le_max_right _ _
  have htsq : (t - s) ^ 2 ≤ (max |t - s| 1) ^ 2 := by
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (t - s)) (le_max_left |t - s| 1) 2
  have hr2 : 1 ≤ (max |t - s| 1) ^ 2 := one_le_pow₀ hr
  have hp : ((t - s) ^ 2 + 4) ^ 2 ≤ 25 * (max |t - s| 1) ^ 4 := by
    calc
      _ ≤ (5 * (max |t - s| 1) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = _ := by ring
  exact hb.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp
      (norm_nonneg (deriv m.inverse (1 + (s : ℂ) * I))))

/-- Both derivative comparisons with the normalization point have degree four. -/
theorem NormalizedModel.inverse_deriv_vertical_bounds (m : NormalizedModel) (t : ℝ) :
    ‖deriv m.inverse 1‖ ≤ (25 * (max |t| 1) ^ 4) *
        ‖deriv m.inverse (1 + (t : ℂ) * I)‖ ∧
      ‖deriv m.inverse (1 + (t : ℂ) * I)‖ ≤
        (25 * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖ := by
  constructor
  · simpa only [zero_sub, abs_neg, ofReal_zero, zero_mul, add_zero] using
      m.norm_inverse_deriv_vertical_comparison t 0
  · simpa only [sub_zero, ofReal_zero, zero_mul, add_zero] using
      m.norm_inverse_deriv_vertical_comparison 0 t

/-- Tail distortion preserves the normalization derivative in both directions. -/
theorem exists_scaled_inverse_deriv_contour_tail_bounds :
    ∃ T : ℝ, 0 < T ∧ ∀ (m : NormalizedModel) (t : ℝ), T ≤ |t| →
      ‖deriv m.inverse 1‖ ≤ (5400 * (max |t| 1) ^ 4) *
          ‖deriv m.inverse (imageContour t)‖ ∧
        ‖deriv m.inverse (imageContour t)‖ ≤
          (984150 * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖ := by
  obtain ⟨T, hT, hdisks⟩ := imageContour_tail_disks
  refine ⟨T, by linarith, ?_⟩
  intro m t ht
  obtain ⟨hR, hball, hrelative⟩ := hdisks t ht
  have hf : UnivalentOn m.inverse
      (Metric.ball (1 + (t : ℂ) * I) ((27 / 2) * Real.posLog |t|)) :=
    ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
  have hl := norm_deriv_ge_of_univalent_ball hR hf
    (by norm_num : (26 / 27 : ℝ) < 1) hrelative
  have hu := norm_deriv_le_of_univalent_ball hR hf
    (by norm_num : (26 / 27 : ℝ) < 1) hrelative
  norm_num at hl hu
  obtain ⟨hvl, hvu⟩ := m.inverse_deriv_vertical_bounds t
  constructor
  · calc
      _ ≤ (25 * (max |t| 1) ^ 4) * ‖deriv m.inverse (1 + (t : ℂ) * I)‖ := hvl
      _ ≤ (25 * (max |t| 1) ^ 4) * (216 * ‖deriv m.inverse (imageContour t)‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ 39366 * ‖deriv m.inverse (1 + (t : ℂ) * I)‖ := hu
      _ ≤ 39366 * ((25 * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖) :=
        mul_le_mul_of_nonneg_left hvu (by norm_num)
      _ = _ := by ring

private theorem inverse_deriv_comparison (m₀ : NormalizedModel)
    {a b : ℂ} (ha : a ∈ modelHalfPlane) (hb : b ∈ modelHalfPlane) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : NormalizedModel,
      ‖deriv m.inverse b‖ ≤ C * ‖deriv m.inverse a‖ := by
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
    ∃ C : ℝ, 0 < C ∧ ∀ m : NormalizedModel,
      ‖deriv m.inverse y‖ ≤ C * ‖deriv m.inverse x‖
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
    · refine ⟨16, by norm_num, ?_⟩
      intro m
      have h := norm_deriv_le_of_univalent_ball hR
        ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
        (by norm_num : (1 / 2 : ℝ) < 1) (by linarith : ‖y - x‖ ≤ (1 / 2) * R)
      norm_num at h
      exact h
    · refine ⟨16, by norm_num, ?_⟩
      intro m
      have hd : ‖x - y‖ ≤ (1 / 2) * (R / 2) := by rw [norm_sub_rev]; linarith
      have h := norm_deriv_le_of_univalent_ball (by positivity : 0 < R / 2)
        ⟨m.holomorphic_inverse.mono hballY, m.univalentOn_inverse.2.mono hballY⟩
        (by norm_num : (1 / 2 : ℝ) < 1) hd
      norm_num at h
      exact h
  apply hconn.induction₂' P hlocal ?_ ha hb
  intro x y z _ _ _ hxy hyz
  obtain ⟨C, hC, hCb⟩ := hxy
  obtain ⟨D, hD, hDb⟩ := hyz
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro m
  calc
    _ ≤ D * ‖deriv m.inverse y‖ := hDb m
    _ ≤ D * (C * ‖deriv m.inverse x‖) := mul_le_mul_of_nonneg_left (hCb m) hD.le
    _ = _ := by ring

/-- On a fixed compact set, inverse derivatives are uniformly comparable
with their actual derivative at the normalization point. -/
theorem exists_scaled_inverse_deriv_bounds_on_compact {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ modelHalfPlane) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (w : ℂ), w ∈ K →
      ‖deriv m.inverse 1‖ ≤ C * ‖deriv m.inverse w‖ ∧
        ‖deriv m.inverse w‖ ≤ C * ‖deriv m.inverse 1‖ := by
  classical
  by_cases hnonempty : Nonempty NormalizedModel
  · obtain ⟨m₀⟩ := hnonempty
    have hH : IsOpen modelHalfPlane := by
      apply isOpen_lt <;> fun_prop
    have hone : (1 : ℂ) ∈ modelHalfPlane := by
      simp [modelHalfPlane, Real.posLog_zero]
    have hlocal (x : K) : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (m : NormalizedModel) (y : ℂ), y ∈ Metric.ball (x : ℂ) r →
          ‖deriv m.inverse 1‖ ≤ C * ‖deriv m.inverse y‖ ∧
            ‖deriv m.inverse y‖ ≤ C * ‖deriv m.inverse 1‖ := by
      obtain ⟨A, hA, hAb⟩ := inverse_deriv_comparison m₀ hone (hKH x.2)
      obtain ⟨B, hB, hBb⟩ := inverse_deriv_comparison m₀ (hKH x.2) hone
      obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hH (x : ℂ) (hKH x.2)
      refine ⟨R / 4, by positivity, 16 * (A + B), by positivity, ?_⟩
      intro m y hy
      have hxy : ‖y - (x : ℂ)‖ < R / 4 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have hu := norm_deriv_le_of_univalent_ball hR
        ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
        (by norm_num : (1 / 2 : ℝ) < 1) (by linarith : ‖y - (x : ℂ)‖ ≤ (1 / 2) * R)
      have hl := norm_deriv_ge_of_univalent_ball hR
        ⟨m.holomorphic_inverse.mono hball, m.univalentOn_inverse.2.mono hball⟩
        (by norm_num : (1 / 2 : ℝ) < 1) (by linarith : ‖y - (x : ℂ)‖ ≤ (1 / 2) * R)
      norm_num at hu hl
      constructor
      · calc
          _ ≤ B * ‖deriv m.inverse x‖ := hBb m
          _ ≤ B * (16 * ‖deriv m.inverse y‖) :=
            mul_le_mul_of_nonneg_left (by linarith) hB.le
          _ ≤ (16 * (A + B)) * ‖deriv m.inverse y‖ := by
            nlinarith [mul_nonneg hA.le (norm_nonneg (deriv m.inverse y))]
      · calc
          _ ≤ 16 * ‖deriv m.inverse x‖ := hu
          _ ≤ 16 * (A * ‖deriv m.inverse 1‖) :=
            mul_le_mul_of_nonneg_left (hAb m) (by norm_num)
          _ ≤ (16 * (A + B)) * ‖deriv m.inverse 1‖ := by
            nlinarith [mul_nonneg hB.le (norm_nonneg (deriv m.inverse 1))]
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
    exact ⟨((hb x m w hxw).1).trans
        (mul_le_mul_of_nonneg_right hxB (norm_nonneg _)),
      ((hb x m w hxw).2).trans (mul_le_mul_of_nonneg_right hxB (norm_nonneg _))⟩
  · exact ⟨1, zero_lt_one, fun m ↦ False.elim (hnonempty ⟨m⟩)⟩

/-- Both global contour-derivative bounds retain the positive normalization
scale, with one constant uniform over all conformal maps. -/
theorem exists_scaled_inverse_deriv_contour_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (t : ℝ),
      ‖deriv m.inverse 1‖ ≤ (C * (max |t| 1) ^ 4) *
          ‖deriv m.inverse (imageContour t)‖ ∧
        ‖deriv m.inverse (imageContour t)‖ ≤
          (C * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖ := by
  obtain ⟨T, hT, htail⟩ := exists_scaled_inverse_deriv_contour_tail_bounds
  have hK : IsCompact (imageContour '' Icc (-T) T) :=
    isCompact_Icc.image lipschitzWith_imageContour.continuous
  obtain ⟨B, hB, hb⟩ := exists_scaled_inverse_deriv_bounds_on_compact hK
    (by rintro _ ⟨t, _, rfl⟩; exact imageContour_mem_modelHalfPlane t)
  let C : ℝ := max 984150 B
  have hC : 0 < C := lt_of_lt_of_le hB (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro m t
  have hp : 1 ≤ (max |t| 1) ^ 4 := one_le_pow₀ (le_max_right _ _)
  by_cases ht : T ≤ |t|
  · obtain ⟨hl, hu⟩ := htail m t ht
    constructor
    · apply hl.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (by norm_num : (5400 : ℝ) ≤ 984150).trans (le_max_left _ _)
    · exact hu.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (norm_nonneg _))
  · have hmid : t ∈ Icc (-T) T := abs_le.1 (le_of_lt (lt_of_not_ge ht))
    obtain ⟨hl, hu⟩ := hb m (imageContour t) ⟨t, hmid, rfl⟩
    have hcoeff : B ≤ C * (max |t| 1) ^ 4 := by
      calc
        _ ≤ C := le_max_right _ _
        _ ≤ C * (max |t| 1) ^ 4 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hC.le
    exact ⟨hl.trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)),
      hu.trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))⟩

#print axioms norm_deriv_ge_of_univalent_ball
#print axioms NormalizedModel.norm_inverse_deriv_vertical_comparison
#print axioms NormalizedModel.inverse_deriv_vertical_bounds
#print axioms exists_scaled_inverse_deriv_contour_tail_bounds
#print axioms exists_scaled_inverse_deriv_bounds_on_compact
#print axioms exists_scaled_inverse_deriv_contour_bounds

end MaxModulusPoints.CauchyApproximation
