import MaxModulusPoints.CauchyApproximation.ContourTube
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
/-!
# Quantitative bounds for separated Cauchy kernels

Polynomial density decay and separation from a shrinking contour tube
cancel the normalization scale. The resulting clamped-power envelope has
an explicit two-sided tail integral. Splitting at a middle interval gives
the integral estimate used in the decay argument for Cauchy approximation.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Powers of the clamped absolute parameter with exponent at most minus two
placeholder an integrable inverse-quadratic majorant. -/
theorem clamped_rpow_le_inv_one_add_sq {p : ℝ} (hp : p ≤ -2) (t : ℝ) :
    (max |t| 1) ^ p ≤ 2 * (1 + t ^ 2)⁻¹ := by
  have hr : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hexp : (max |t| 1) ^ p ≤ (max |t| 1) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) hp
  have hsq : t ^ 2 ≤ (max |t| 1) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) (le_max_left |t| 1) 2
  apply hexp.trans
  rw [Real.rpow_neg hr.le, Real.rpow_two]
  have hpos : 0 < (max |t| 1) ^ 2 := sq_pos_of_pos hr
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hpos (by positivity)]
  nlinarith [le_max_right |t| 1]

/-- The clamped powers used for the density and separated kernel are integrable. -/
theorem integrable_clamped_rpow {p : ℝ} (hp : p ≤ -2) :
    Integrable (fun t : ℝ ↦ (max |t| 1) ^ p) := by
  have hc : Continuous (fun t : ℝ ↦ (max |t| 1) ^ p) :=
    (continuous_abs.max continuous_const).rpow_const
      (fun t ↦ Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right |t| 1))))
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact clamped_rpow_le_inv_one_add_sq hp t

/-- The inverse-quadratic majorant also bounds the total density norm. -/
theorem integral_norm_le_of_clamped_bound {ρ : ℝ → ℂ} (hρ : Integrable ρ)
    {B p : ℝ} (hB : 0 ≤ B) (hp : p ≤ -2)
    (hb : ∀ t, ‖ρ t‖ ≤ B * (max |t| 1) ^ p) :
    (∫ t : ℝ, ‖ρ t‖) ≤ 2 * Real.pi * B := by
  have h := integral_mono hρ.norm
    ((integrable_inv_one_add_sq.const_mul 2).const_mul B)
    (fun t ↦ (hb t).trans (mul_le_mul_of_nonneg_left
      (clamped_rpow_le_inv_one_add_sq hp t) hB))
  rw [integral_const_mul, integral_const_mul, integral_univ_inv_one_add_sq] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The two tails of a clamped power have an explicit improper-integral value. -/
theorem integral_clamped_rpow_tail {p T : ℝ} (hp : p < -1) (hT : 1 ≤ T) :
    (∫ t : ℝ in {t | T < |t|}, (max |t| 1) ^ p) =
      2 * (-(T ^ (p + 1)) / (p + 1)) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hset : MeasurableSet {t : ℝ | T < |t|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have heq : {t : ℝ | T < |t|}.indicator (fun t ↦ (max |t| 1) ^ p) =
      fun t : ℝ ↦ (Ioi T).indicator (fun x : ℝ ↦ x ^ p) |t| := by
    funext t
    by_cases ht : T < |t|
    · simp only [indicator_apply, mem_ofPred_eq, mem_Ioi, ht, ite_true,
        max_eq_left (hT.trans ht.le)]
    · simp only [indicator_apply, mem_ofPred_eq, mem_Ioi, ht, ite_false]
  rw [← integral_indicator hset, heq, integral_comp_abs,
    setIntegral_indicator measurableSet_Ioi]
  have hinter : Ioi (0 : ℝ) ∩ Ioi T = Ioi T := by
    exact inter_eq_right.2 (fun _ hx ↦ hTpos.trans hx)
  rw [hinter, integral_Ioi_rpow_of_lt hp hTpos]

/-- The separated kernel envelope has tails of order minus four. -/
theorem integral_clamped_neg_five_tail {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ in {t | T < |t|}, (max |t| 1) ^ (-5 : ℝ)) = 1 / (2 * T ^ 4) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  calc
    _ = 2 * (-(T ^ (-4 : ℝ)) / (-4 : ℝ)) := by
      simpa only [show (-5 : ℝ) + 1 = -4 by norm_num] using
        integral_clamped_rpow_tail (by norm_num : (-5 : ℝ) < -1) hT
    _ = _ := by
      rw [Real.rpow_neg hTpos.le, Real.rpow_ofNat]
      ring

/-- Separation from the scaled tube cancels the scale in the kernel bound. -/
theorem norm_kernel_le_of_scaled_separation {γ ρ : ℝ → ℂ}
    {D σ ε : ℝ} (hD : 0 ≤ D) (hσ : 0 < σ) (hε : 0 < ε) {z : ℂ}
    (hρ : ∀ t, ‖ρ t‖ ≤ D * σ * (max |t| 1) ^ (-9 : ℝ))
    (hsep : ∀ t, ε * σ / (max |t| 1) ^ 4 ≤ ‖γ t - z‖) (t : ℝ) :
    ‖ρ t / (γ t - z)‖ ≤ (D / ε) * (max |t| 1) ^ (-5 : ℝ) := by
  have hs : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hden : 0 < ε * σ / (max |t| 1) ^ 4 := by positivity
  have hp : (max |t| 1) ^ (-9 : ℝ) * (max |t| 1) ^ (4 : ℕ) =
      (max |t| 1) ^ (-5 : ℝ) := by
    rw [← Real.rpow_natCast (max |t| 1) 4, ← Real.rpow_add hs]
    norm_num
  rw [norm_div]
  calc
    _ ≤ (D * σ * (max |t| 1) ^ (-9 : ℝ)) /
        (ε * σ / (max |t| 1) ^ 4) :=
      div_le_div₀ (by positivity) (hρ t) hden (hsep t)
    _ = (D / ε) * ((max |t| 1) ^ (-9 : ℝ) * (max |t| 1) ^ (4 : ℕ)) := by
      field_simp
    _ = _ := by rw [hp]

/-- A middle interval separated by half the evaluation norm and two scaled
tails give an explicit norm bound on the full, absolutely convergent kernel. -/
theorem integral_norm_kernel_le_of_middle_and_tails {γ ρ : ℝ → ℂ}
    (hγ : IsProperMap γ) (hρ : Integrable ρ) {D σ ε T : ℝ}
    (hD : 0 ≤ D) (hσ : 0 < σ) (hε : 0 < ε) (hT : 1 ≤ T)
    {z : ℂ} (hz : 0 < ‖z‖)
    (hb : ∀ t, ‖ρ t‖ ≤ D * σ * (max |t| 1) ^ (-9 : ℝ))
    (hsep : ∀ t, ε * σ / (max |t| 1) ^ 4 ≤ ‖γ t - z‖)
    (hmid : ∀ t, |t| ≤ T → ‖z‖ / 2 ≤ ‖γ t - z‖) :
    (∫ t : ℝ, ‖ρ t / (γ t - z)‖) ≤
      (2 / ‖z‖) * (∫ t : ℝ, ‖ρ t‖) + (D / ε) / (2 * T ^ 4) := by
  have havoid : z ∉ range γ := by
    rintro ⟨t, rfl⟩
    have h := hsep t
    have hp : 0 < ε * σ / (max |t| 1) ^ 4 := by positivity
    simp only [sub_self, norm_zero] at h
    linarith
  have hk := (cauchyIntegral_converges_of_integrable hγ hρ havoid).1
  let M : Set ℝ := {t | |t| ≤ T}
  have hM : MeasurableSet M := (isClosed_le continuous_abs continuous_const).measurableSet
  have hmiddle : (∫ t in M, ‖ρ t / (γ t - z)‖) ≤
      (2 / ‖z‖) * (∫ t : ℝ, ‖ρ t‖) := by
    have h := setIntegral_mono_on hk.norm.integrableOn
      ((hρ.norm.const_mul (2 / ‖z‖)).integrableOn) hM (fun t ht ↦ ?_)
    · apply h.trans
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hρ.norm (ae_of_all _ (fun _ ↦ norm_nonneg _)))
        (by positivity)
    · rw [norm_div]
      have h := div_le_div_of_nonneg_left (norm_nonneg (ρ t)) (by positivity : 0 < ‖z‖ / 2)
        (hmid t ht)
      exact h.trans_eq (by ring)
  have htailset : Mᶜ = {t : ℝ | T < |t|} := by
    ext t
    simp only [M, mem_compl_iff, mem_ofPred_eq, not_le]
  have htail : (∫ t in Mᶜ, ‖ρ t / (γ t - z)‖) ≤ (D / ε) / (2 * T ^ 4) := by
    have h := setIntegral_mono_on hk.norm.integrableOn
      (((integrable_clamped_rpow (by norm_num : (-5 : ℝ) ≤ -2)).const_mul (D / ε)).integrableOn)
      hM.compl (fun t _ ↦ norm_kernel_le_of_scaled_separation hD hσ hε hb hsep t)
    rw [integral_const_mul, htailset, integral_clamped_neg_five_tail hT] at h
    simpa only [htailset, mul_one_div] using h
  have hsplit := integral_add_compl hM hk.norm
  linarith

/-- The same middle/tail bound applies to the actual Cauchy transform. -/
theorem norm_cauchyIntegral_le_of_middle_and_tails {γ ρ : ℝ → ℂ}
    (hγ : IsProperMap γ) (hρ : Integrable ρ) {D σ ε T : ℝ}
    (hD : 0 ≤ D) (hσ : 0 < σ) (hε : 0 < ε) (hT : 1 ≤ T)
    {z : ℂ} (hz : 0 < ‖z‖)
    (hb : ∀ t, ‖ρ t‖ ≤ D * σ * (max |t| 1) ^ (-9 : ℝ))
    (hsep : ∀ t, ε * σ / (max |t| 1) ^ 4 ≤ ‖γ t - z‖)
    (hmid : ∀ t, |t| ≤ T → ‖z‖ / 2 ≤ ‖γ t - z‖) :
    ‖cauchyIntegral γ ρ z‖ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
      ((2 / ‖z‖) * (∫ t : ℝ, ‖ρ t‖) + (D / ε) / (2 * T ^ 4)) := by
  unfold cauchyIntegral
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans
      (integral_norm_kernel_le_of_middle_and_tails hγ hρ hD hσ hε hT hz hb hsep hmid))
    (norm_nonneg _)

#print axioms integrable_clamped_rpow
#print axioms integral_norm_le_of_clamped_bound
#print axioms integral_clamped_rpow_tail
#print axioms norm_kernel_le_of_scaled_separation
#print axioms integral_norm_kernel_le_of_middle_and_tails
#print axioms norm_cauchyIntegral_le_of_middle_and_tails

end MaxModulusPoints.CauchyApproximation
