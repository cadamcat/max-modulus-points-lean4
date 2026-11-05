module

public import MaxModulusPoints.CauchyApproximation.ContourDerivative
public import MaxModulusPoints.CauchyApproximation.ContourDistortion
public import MaxModulusPoints.CauchyApproximation.ContourGrowth
public import MaxModulusPoints.CauchyApproximation.ContourTube
public import MaxModulusPoints.CauchyApproximation.InverseDistortion
public import MaxModulusPoints.CauchyApproximation.LocalDetour
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.QuantitativeDetour
public import MaxModulusPoints.CauchyApproximation.ScaledDistortion
public import MaxModulusPoints.CauchyApproximation.UniformBounds

/-!
# Uniform growth and density estimates for the tent detours

Nonnegative horizontal shifts preserve the interior disks of the fixed
image domain. A finite chain of overlapping disks compares inverse values
and derivatives along every height-one tent. Thus the modified contours
retain quartic position growth and order-nine density decay, with constants
independent of the position of the tent and with the normalization derivative
scale retained in the density.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open OAI.Brennan
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Horizontal translation to the right preserves the enlarged half-plane. -/
theorem modelHalfPlane_add_nonneg {w : ℂ} (hw : w ∈ modelHalfPlane)
    {u : ℝ} (hu : 0 ≤ u) : w + (u : ℂ) ∈ modelHalfPlane := by
  change -14 * Real.posLog |w.im| < w.re at hw
  change -14 * Real.posLog |(w + (u : ℂ)).im| < (w + (u : ℂ)).re
  simp only [add_im, ofReal_im, add_zero, add_re, ofReal_re]
  linarith

/-- The fixed interior disk persists along every nonnegative horizontal shift. -/
theorem imageContour_add_ball_subset_modelHalfPlane (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Metric.ball (imageContour t + (u : ℂ)) (1 / 30) ⊆ modelHalfPlane := by
  intro w hw
  have he : (w - (u : ℂ)) - imageContour t = w - (imageContour t + (u : ℂ)) := by ring
  have hnear : w - (u : ℂ) ∈ Metric.ball (imageContour t) (1 / 30) := by
    simpa only [Metric.mem_ball, dist_eq_norm, he] using hw
  have h := modelHalfPlane_add_nonneg (imageContour_ball_subset_modelHalfPlane t hnear) hu
  simpa only [sub_add_cancel] using h

/-- Sixty half-radius steps compare inverse values and derivatives on the
whole horizontal unit segment with their values on the original contour. -/
theorem NormalizedModel.inverse_bounds_horizontal_shift (m : NormalizedModel)
    (t : ℝ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖m.inverse (imageContour t + (u : ℂ))‖ ≤
        (33 : ℝ) ^ 60 * ‖m.inverse (imageContour t)‖ ∧
      ‖deriv m.inverse (imageContour t + (u : ℂ))‖ ≤
        (16 : ℝ) ^ 60 * ‖deriv m.inverse (imageContour t)‖ := by
  let w : ℕ → ℂ := fun n ↦ imageContour t + (((n : ℝ) * u / 60 : ℝ) : ℂ)
  have hstep (n : ℕ) : ‖w (n + 1) - w n‖ ≤ (1 / 60 : ℝ) := by
    have he : w (n + 1) - w n = ((u / 60 : ℝ) : ℂ) := by
      dsimp only [w]
      push_cast
      ring
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ u / 60)]
    linarith
  have hind (n : ℕ) :
      ‖m.inverse (w n)‖ ≤ (33 : ℝ) ^ n * ‖m.inverse (imageContour t)‖ ∧
        ‖deriv m.inverse (w n)‖ ≤ (16 : ℝ) ^ n * ‖deriv m.inverse (imageContour t)‖ := by
    induction n with
    | zero => simp [w]
    | succ n ih =>
      have hb : Metric.ball (w n) (1 / 30) ⊆ modelHalfPlane :=
        imageContour_add_ball_subset_modelHalfPlane t (by positivity : 0 ≤ (n : ℝ) * u / 60)
      have hf : UnivalentOn m.inverse (Metric.ball (w n) (1 / 30)) :=
        ⟨m.holomorphic_inverse.mono hb, m.univalentOn_inverse.2.mono hb⟩
      have hv := norm_value_le_of_univalent_ball_omit_zero (by norm_num : (0 : ℝ) < 1 / 30)
        hf (fun z hz he ↦ m.zero_not_mem (he ▸ m.inverse_mem (hb hz)))
        (by linarith [hstep n] : ‖w (n + 1) - w n‖ ≤ (1 / 30 : ℝ) / 2)
      have hd := norm_deriv_le_of_univalent_ball (by norm_num : (0 : ℝ) < 1 / 30) hf
        (by norm_num : (1 / 2 : ℝ) < 1)
        (by linarith [hstep n] : ‖w (n + 1) - w n‖ ≤ (1 / 2 : ℝ) * (1 / 30))
      norm_num only at hd
      constructor
      · calc
          _ ≤ 33 * ‖m.inverse (w n)‖ := hv
          _ ≤ 33 * ((33 : ℝ) ^ n * ‖m.inverse (imageContour t)‖) :=
            mul_le_mul_of_nonneg_left ih.1 (by norm_num)
          _ = _ := by rw [pow_succ]; ring
      · calc
          _ ≤ 16 * ‖deriv m.inverse (w n)‖ := hd
          _ ≤ 16 * ((16 : ℝ) ^ n * ‖deriv m.inverse (imageContour t)‖) :=
            mul_le_mul_of_nonneg_left ih.2 (by norm_num)
          _ = _ := by rw [pow_succ]; ring
  have he : w 60 = imageContour t + (u : ℂ) := by norm_num [w]
  simpa only [he] using hind 60

/-- The height-one image tents have one Lipschitz constant for every centre. -/
theorem lipschitzWith_imageDetour (s : ℝ) : LipschitzWith 15 (imageDetour s) := by
  have htent : LipschitzWith 1 (fun t : ℝ ↦ 1 - |t - s|) := by
    apply LipschitzWith.mk_one
    intro x y
    simp only [Real.dist_eq]
    have h := abs_abs_sub_abs_le_abs_sub (y - s) (x - s)
    have he : (y - s) - (x - s) = y - x := by ring
    have he' : (1 - |x - s|) - (1 - |y - s|) = |y - s| - |x - s| := by ring
    rw [he']
    rw [he] at h
    exact h.trans_eq (abs_sub_comm y x)
  have hc : LipschitzWith 1 (fun t : ℝ ↦ ((max 0 (1 - |t - s|) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, one_mul] using
      Complex.isometry_ofReal.lipschitzWith.comp (htent.const_max 0)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  have he : imageDetour s x - imageDetour s y =
      (imageContour x - imageContour y) +
        (((max 0 (1 - |x - s|) : ℝ) : ℂ) - ((max 0 (1 - |y - s|) : ℝ) : ℂ)) := by
    simp only [imageDetour]
    ring
  rw [he]
  have hα := lipschitzWith_imageContour.dist_le_mul x y
  have hδ := hc.dist_le_mul x y
  simp only [dist_eq_norm, NNReal.coe_ofNat, NNReal.coe_one, one_mul] at hα hδ
  exact (norm_add_le _ _).trans (by linarith)

/-- The actual modified contour satisfies the inverse chain rule at corners
as well as at smooth parameters. -/
theorem NormalizedModel.deriv_localDetour (m : NormalizedModel) (s t : ℝ) :
    deriv (m.localDetour s) t =
      deriv m.inverse (imageDetour s t) * deriv (imageDetour s) t := by
  have hH : IsOpen modelHalfPlane := by apply isOpen_lt <;> fun_prop
  have hi : DifferentiableAt ℂ m.inverse (imageDetour s t) :=
    m.holomorphic_inverse.differentiableAt
      (hH.mem_nhds (imageDetour_mem_modelHalfPlane s t))
  by_cases hα : DifferentiableAt ℝ (imageDetour s) t
  · exact deriv_comp t hi hα
  · have hη : ¬ DifferentiableAt ℝ (m.localDetour s) t := by
      intro hη
      have hf : DifferentiableAt ℂ m.forward (m.localDetour s t) :=
        m.holomorphic_forward.differentiableAt (m.isOpen_domain.mem_nhds
          (m.inverse_mem (imageDetour_mem_modelHalfPlane s t)))
      have he : m.forward ∘ m.localDetour s = imageDetour s := by
        funext v
        exact m.right_inverse _ (imageDetour_mem_modelHalfPlane s v)
      apply hα
      rw [← he]
      exact (hf.restrictScalars ℝ).comp t hη
    rw [deriv_zero_of_not_differentiableAt hη, deriv_zero_of_not_differentiableAt hα,
      mul_zero]

/-- Every modified contour has the same quartic position-growth coefficient. -/
theorem exists_uniform_localDetour_position_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m : NormalizedModel) (s t : ℝ),
      ‖m.localDetour s t‖ ≤ A * (max |t| 1) ^ 4 := by
  obtain ⟨A, hA, hpos⟩ := exists_uniform_contour_position_bound
  refine ⟨(33 : ℝ) ^ 60 * A, ?_, ?_⟩
  · have hp : (1 : ℝ) ≤ 33 ^ 60 := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 33)
    nlinarith
  · intro m s t
    have hu : 0 ≤ max 0 (1 - |t - s|) := le_max_left _ _
    have hu1 : max 0 (1 - |t - s|) ≤ 1 :=
      max_le zero_le_one (by linarith [abs_nonneg (t - s)])
    have hb := (m.inverse_bounds_horizontal_shift t hu hu1).1
    calc
      _ ≤ (33 : ℝ) ^ 60 * ‖m.contour t‖ := hb
      _ ≤ (33 : ℝ) ^ 60 * (A * (max |t| 1) ^ 4) :=
        mul_le_mul_of_nonneg_left (hpos m t) (by positivity)
      _ = _ := by ring

/-- The exponential model retains order-thirteen decay on every image tent. -/
theorem NormalizedModel.norm_modelFunction_localDetour_le (m : NormalizedModel) (s t : ℝ) :
    ‖m.modelFunction (m.localDetour s t)‖ ≤
      Real.exp 2 * (max |t| 1) ^ (-13 : ℝ) := by
  have he : m.forward (m.localDetour s t) = imageDetour s t :=
    m.right_inverse _ (imageDetour_mem_modelHalfPlane s t)
  change ‖Complex.exp (m.forward (m.localDetour s t))‖ ≤ _
  rw [he]
  have hnear : ‖imageDetour s t - imageContour t‖ ≤ (1 : ℝ) := by
    simp only [imageDetour, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_max_left 0 (1 - |t - s|))]
    exact max_le zero_le_one (by linarith [abs_nonneg (t - s)])
  simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using
    norm_exp_le_of_dist_imageContour_le hnear

/-- One order-nine density coefficient works for every tent detour, retaining
the actual normalization derivative so it can cancel against separation. -/
theorem exists_scaled_localDetour_density_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : NormalizedModel) (s t : ℝ),
      ‖m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t‖ ≤
        D * ‖deriv m.inverse 1‖ * (max |t| 1) ^ (-9 : ℝ) := by
  obtain ⟨C, hC, hbounds⟩ := exists_scaled_inverse_deriv_contour_bounds
  refine ⟨15 * (16 : ℝ) ^ 60 * C * Real.exp 2, by positivity, ?_⟩
  intro m s t
  have hu : 0 ≤ max 0 (1 - |t - s|) := le_max_left _ _
  have hu1 : max 0 (1 - |t - s|) ≤ 1 :=
    max_le zero_le_one (by linarith [abs_nonneg (t - s)])
  have hderiv : ‖deriv (m.localDetour s) t‖ ≤
      15 * ((16 : ℝ) ^ 60 * ((C * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖)) := by
    rw [m.deriv_localDetour, norm_mul]
    calc
      _ ≤ ‖deriv m.inverse (imageDetour s t)‖ * 15 :=
        mul_le_mul_of_nonneg_left (norm_deriv_le_of_lipschitz (lipschitzWith_imageDetour s))
          (norm_nonneg _)
      _ ≤ ((16 : ℝ) ^ 60 * ‖deriv m.inverse (imageContour t)‖) * 15 :=
        mul_le_mul_of_nonneg_right (m.inverse_bounds_horizontal_shift t hu hu1).2
          (by norm_num)
      _ ≤ ((16 : ℝ) ^ 60 * ((C * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖)) * 15 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbounds m t).2
          (by positivity)) (by norm_num)
      _ = _ := by ring
  have hs : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hp : (max |t| 1) ^ (-13 : ℝ) * (max |t| 1) ^ (4 : ℕ) =
      (max |t| 1) ^ (-9 : ℝ) := by
    rw [← Real.rpow_natCast (max |t| 1) 4, ← Real.rpow_add hs]
    norm_num
  calc
    _ = ‖m.modelFunction (m.localDetour s t)‖ * ‖deriv (m.localDetour s) t‖ := norm_mul _ _
    _ ≤ (Real.exp 2 * (max |t| 1) ^ (-13 : ℝ)) *
        (15 * ((16 : ℝ) ^ 60 * ((C * (max |t| 1) ^ 4) * ‖deriv m.inverse 1‖))) :=
      mul_le_mul (m.norm_modelFunction_localDetour_le s t) hderiv (norm_nonneg _)
        (by positivity)
    _ = (15 * (16 : ℝ) ^ 60 * C * Real.exp 2) * ‖deriv m.inverse 1‖ *
        ((max |t| 1) ^ (-13 : ℝ) * (max |t| 1) ^ (4 : ℕ)) := by ring
    _ = _ := by rw [hp]

#print axioms modelHalfPlane_add_nonneg
#print axioms imageContour_add_ball_subset_modelHalfPlane
#print axioms NormalizedModel.inverse_bounds_horizontal_shift
#print axioms lipschitzWith_imageDetour
#print axioms NormalizedModel.deriv_localDetour
#print axioms exists_uniform_localDetour_position_bound
#print axioms NormalizedModel.norm_modelFunction_localDetour_le
#print axioms exists_scaled_localDetour_density_bound

end MaxModulusPoints.CauchyApproximation
