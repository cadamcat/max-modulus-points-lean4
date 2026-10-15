import MaxModulusPoints.CauchyApproximation.ImproperIntegral
import MaxModulusPoints.CauchyApproximation.KernelEstimates
/-!
# Decay of a Cauchy integral away from a scaled contour tube

A quartic position bound determines a middle interval on which the denominator
is comparable to the evaluation norm. The remaining tails have an explicit
integral bound. Together with the global separated-kernel envelope for small
evaluation norms, this gives inverse-norm decay with a uniform constant.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Quartic contour growth and separation from the scaled tube give a uniform
inverse-norm bound on the absolutely convergent kernel integral. -/
theorem integral_norm_kernel_le_of_quartic_growth {γ ρ : ℝ → ℂ}
    (hγ : IsProperMap γ) (hρ : Integrable ρ) {A D σ S ε : ℝ}
    (hA : 1 ≤ A) (hD : 0 ≤ D) (hσ : 0 < σ) (hσS : σ ≤ S) (hε : 0 < ε)
    (hpos : ∀ t, ‖γ t‖ ≤ A * (max |t| 1) ^ 4)
    (hb : ∀ t, ‖ρ t‖ ≤ D * σ * (max |t| 1) ^ (-9 : ℝ))
    {z : ℂ} (hz : 0 < ‖z‖)
    (hsep : ∀ t, ε * σ / (max |t| 1) ^ 4 ≤ ‖γ t - z‖) :
    (∫ t : ℝ, ‖ρ t / (γ t - z)‖) ≤
      (4 * Real.pi * D * S + (4 * Real.pi + 1) * (A * D / ε)) / ‖z‖ := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hS : 0 < S := hσ.trans_le hσS
  have hx : 0 ≤ A * D / ε := by positivity
  have hmass : (∫ t : ℝ, ‖ρ t‖) ≤ 2 * Real.pi * D * S := by
    have h := integral_norm_le_of_clamped_bound hρ (by positivity : 0 ≤ D * σ)
      (by norm_num : (-9 : ℝ) ≤ -2) hb
    apply h.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hσS
      (by positivity : 0 ≤ 2 * Real.pi * D)
  by_cases hlarge : 2 * A ≤ ‖z‖
  · let q : ℝ := ‖z‖ / (2 * A)
    let T : ℝ := q ^ (1 / 4 : ℝ)
    have hq : 1 ≤ q := by
      dsimp [q]
      exact (le_div_iff₀ (by positivity)).2 (by simpa using hlarge)
    have hT : 1 ≤ T := Real.one_le_rpow hq (by norm_num)
    have hTfour : T ^ 4 = q := by
      dsimp [T]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ q)]
      norm_num
    have hmid : ∀ t, |t| ≤ T → ‖z‖ / 2 ≤ ‖γ t - z‖ := by
      intro t ht
      have hbound : ‖γ t‖ ≤ ‖z‖ / 2 := by
        calc
          _ ≤ A * (max |t| 1) ^ 4 := hpos t
          _ ≤ A * T ^ 4 := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (max_le ht hT) 4) hApos.le
          _ = ‖z‖ / 2 := by
            rw [hTfour]
            dsimp [q]
            field_simp
            <;> ring
      have htriangle : ‖z‖ - ‖γ t‖ ≤ ‖γ t - z‖ := by
        simpa only [norm_sub_rev] using norm_sub_norm_le z (γ t)
      linarith
    calc
      _ ≤ (2 / ‖z‖) * (∫ t : ℝ, ‖ρ t‖) + (D / ε) / (2 * T ^ 4) :=
        integral_norm_kernel_le_of_middle_and_tails hγ hρ hD hσ hε hT hz hb hsep hmid
      _ ≤ (2 / ‖z‖) * (2 * Real.pi * D * S) + (D / ε) / (2 * T ^ 4) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 2 / ‖z‖)) le_rfl
      _ = (4 * Real.pi * D * S + A * D / ε) / ‖z‖ := by
        rw [hTfour]
        dsimp [q]
        field_simp
        <;> ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hz.le
        nlinarith [mul_nonneg Real.pi_pos.le hx]
  · have hsmall : ‖z‖ ≤ 2 * A := (lt_of_not_ge hlarge).le
    have havoid : z ∉ range γ := by
      rintro ⟨t, rfl⟩
      have h := hsep t
      have hp : 0 < ε * σ / (max |t| 1) ^ 4 := by positivity
      simp only [sub_self, norm_zero] at h
      linarith
    have hk := (cauchyIntegral_converges_of_integrable hγ hρ havoid).1
    calc
      _ ≤ 2 * Real.pi * (D / ε) :=
        integral_norm_le_of_clamped_bound hk (by positivity)
          (by norm_num : (-5 : ℝ) ≤ -2)
          (norm_kernel_le_of_scaled_separation hD hσ hε hb hsep)
      _ ≤ _ := by
        apply (le_div_iff₀ hz).2
        calc
          2 * Real.pi * (D / ε) * ‖z‖ ≤
              2 * Real.pi * (D / ε) * (2 * A) :=
            mul_le_mul_of_nonneg_left hsmall (by positivity)
          _ = 4 * Real.pi * (A * D / ε) := by ring
          _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * Real.pi * D) hS.le]

/-- The normalized improper Cauchy transform has the same inverse-norm decay
under quartic growth and separation from the scaled tube. -/
theorem norm_cauchyIntegral_le_of_quartic_growth {γ ρ : ℝ → ℂ}
    (hγ : IsProperMap γ) (hρ : Integrable ρ) {A D σ S ε : ℝ}
    (hA : 1 ≤ A) (hD : 0 ≤ D) (hσ : 0 < σ) (hσS : σ ≤ S) (hε : 0 < ε)
    (hpos : ∀ t, ‖γ t‖ ≤ A * (max |t| 1) ^ 4)
    (hb : ∀ t, ‖ρ t‖ ≤ D * σ * (max |t| 1) ^ (-9 : ℝ))
    {z : ℂ} (hz : 0 < ‖z‖)
    (hsep : ∀ t, ε * σ / (max |t| 1) ^ 4 ≤ ‖γ t - z‖) :
    ‖cauchyIntegral γ ρ z‖ ≤ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
      ((4 * Real.pi * D * S + (4 * Real.pi + 1) * (A * D / ε)) / ‖z‖) := by
  unfold cauchyIntegral
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_integral_le_integral_norm _).trans
      (integral_norm_kernel_le_of_quartic_growth hγ hρ hA hD hσ hσS hε hpos hb hz hsep))
    (norm_nonneg _)

#print axioms integral_norm_kernel_le_of_quartic_growth
#print axioms norm_cauchyIntegral_le_of_quartic_growth

end MaxModulusPoints.CauchyApproximation
