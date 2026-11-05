module

public import MaxModulusPoints.CauchyApproximation.ArcDecay
public import MaxModulusPoints.CauchyApproximation.CanonicalApproximation
public import MaxModulusPoints.CauchyApproximation.CanonicalDecay
public import MaxModulusPoints.CauchyApproximation.ContourGrowth
public import MaxModulusPoints.CauchyApproximation.DetourSeparation
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# Global decay for the canonical core approximation

The model function has inverse-norm decay throughout a scaled neighborhood
of the interior contour. Combining this with the canonical near-contour
bound and the separated Cauchy estimate gives uniform approximation on the
core and uniform decay outside the core. In particular, the original
improper Cauchy integral has inverse-norm decay off its contour, and the
canonical entire function has that decay outside the original tract.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The same scaled neighborhood lies in the tract and controls the model
function by the inverse evaluation norm. -/
theorem exists_uniform_near_model_bound :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (m : NormalizedModel) (t : ℝ) (z : ℂ),
      0 < ‖z‖ →
      ‖m.contour t - z‖ ≤ (ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2 →
        z ∈ m.domain ∧ ‖m.modelFunction z‖ ≤ C / ‖z‖ := by
  obtain ⟨ε, hε, htube⟩ := exists_bounded_scaled_contour_tube
  obtain ⟨A, hA, hposition⟩ := exists_uniform_contour_position_bound
  let C : ℝ := Real.exp (31 / 30) * (A + 1)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨ε, C, hε, hC, ?_⟩
  intro m t z hz hnear
  let s : ℝ := max |t| 1
  let r : ℝ := ε * ‖deriv m.inverse 1‖ / s ^ 4
  obtain ⟨hr, hrone, hmodel⟩ := htube m t
  have hs : 1 ≤ s := le_max_right _ _
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs
  have hnear' : ‖z - m.contour t‖ ≤ r / 2 := by
    simpa only [norm_sub_rev] using hnear
  obtain ⟨hzT, hgbound⟩ := hmodel z (by linarith : ‖z - m.contour t‖ ≤ r)
  refine ⟨hzT, ?_⟩
  have hnormz : ‖z‖ ≤ (A + 1) * s ^ 4 := by
    have ht := norm_add_le (z - m.contour t) (m.contour t)
    rw [sub_add_cancel] at ht
    have hp := hposition m t
    change ‖m.contour t‖ ≤ A * s ^ 4 at hp
    change r ≤ 1 at hrone
    nlinarith
  have hweight : s ^ (-13 : ℝ) * s ^ (4 : ℕ) = s ^ (-9 : ℝ) := by
    rw [← Real.rpow_natCast s 4, ← Real.rpow_add hspos]
    norm_num
  have htail : s ^ (-9 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs (by norm_num)
  apply (le_div_iff₀ hz).2
  calc
    _ ≤ (Real.exp (31 / 30) * s ^ (-13 : ℝ)) * ((A + 1) * s ^ 4) :=
      mul_le_mul hgbound hnormz (norm_nonneg _) (by positivity)
    _ = C * (s ^ (-13 : ℝ) * s ^ (4 : ℕ)) := by dsimp only [C]; ring
    _ = C * s ^ (-9 : ℝ) := by rw [hweight]
    _ ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left htail hC.le

/-- One constant controls the error on the whole interior core and the
canonical entire function outside the core, without a separation hypothesis. -/
theorem exists_uniform_core_approximation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (z : ℂ), 0 < ‖z‖ →
      (z ∈ m.core → ‖m.canonicalEntire z - m.modelFunction z‖ ≤ C / ‖z‖) ∧
      (z ∉ m.core → ‖m.canonicalEntire z‖ ≤ C / ‖z‖) := by
  obtain ⟨εn, Cn, hεn, hCn, hnear⟩ := exists_uniform_near_canonical_bound
  obtain ⟨εg, Cg, hεg, hCg, hmodel⟩ := exists_uniform_near_model_bound
  let η : ℝ := min εn εg
  have hη : 0 < η := lt_min hεn hεg
  obtain ⟨Cf, hCf, hfar⟩ :=
    exists_uniform_separated_canonical_bound (by positivity : 0 < η / 2)
  let C : ℝ := max Cf (Cn + Cg)
  have hC : 0 < C := hCf.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro m z hz
  have hscale (ξ : ℝ) (hξ : η ≤ ξ) (t : ℝ) :
      (η * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2 ≤
        (ξ * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2 :=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hξ (norm_nonneg _)) (by positivity)) (by norm_num)
  by_cases hnear' : ∃ t, ‖m.contour t - z‖ ≤
      (η * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2
  · obtain ⟨t, ht⟩ := hnear'
    have hf := hnear m z hz ⟨t, ht.trans (hscale εn (min_le_left _ _) t)⟩
    have hg := (hmodel m t z hz (ht.trans (hscale εg (min_le_right _ _) t))).2
    constructor
    · intro _
      calc
        _ ≤ ‖m.canonicalEntire z‖ + ‖m.modelFunction z‖ := norm_sub_le _ _
        _ ≤ Cn / ‖z‖ + Cg / ‖z‖ := add_le_add hf hg
        _ = (Cn + Cg) / ‖z‖ := by ring
        _ ≤ C / ‖z‖ := div_le_div_of_nonneg_right (le_max_right _ _) hz.le
    · intro _
      exact hf.trans (div_le_div_of_nonneg_right
        ((by linarith : Cn ≤ Cn + Cg).trans (le_max_right _ _)) hz.le)
  · have hsep (t : ℝ) : (η / 2) * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4 ≤
        ‖m.contour t - z‖ := by
      have ht : (η * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2 <
          ‖m.contour t - z‖ := lt_of_not_ge (fun ht ↦ hnear' ⟨t, ht⟩)
      convert ht.le using 1
      ring
    obtain ⟨hi, he⟩ := hfar m z hz hsep
    have hbound : Cf / ‖z‖ ≤ C / ‖z‖ :=
      div_le_div_of_nonneg_right (le_max_left _ _) hz.le
    exact ⟨fun hc ↦ (hi hc).trans hbound, fun hc ↦ (he hc).trans hbound⟩

/-- The original improper Cauchy integral has a universal inverse-norm bound
at every point off its contour. -/
theorem exists_uniform_cauchy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (z : ℂ),
      0 < ‖z‖ → z ∉ range m.contour →
        ‖cauchyIntegral m.contour m.density z‖ ≤ C / ‖z‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_core_approximation_bound
  refine ⟨C, hC, ?_⟩
  intro m z hz hzγ
  by_cases hc : z ∈ m.core
  · have h := (hbound m z hz).1 hc
    rw [(m.canonicalEntire_spec.2 z hzγ).1 hc, add_sub_cancel_right] at h
    exact h
  · have h := (hbound m z hz).2 hc
    rw [(m.canonicalEntire_spec.2 z hzγ).2 hc] at h
    exact h

/-- The canonical entire function is uniformly small outside the original
tract, as a consequence of its stronger decay outside the core. -/
theorem exists_uniform_exterior_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : NormalizedModel) (z : ℂ),
      z ∉ m.domain → 0 < ‖z‖ → ‖m.canonicalEntire z‖ ≤ C / ‖z‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_core_approximation_bound
  exact ⟨C, hC, fun m z hzT hz ↦ (hbound m z hz).2 (fun hc ↦ hzT hc.1)⟩

#print axioms exists_uniform_near_model_bound
#print axioms exists_uniform_core_approximation_bound
#print axioms exists_uniform_cauchy_bound
#print axioms exists_uniform_exterior_bound

end MaxModulusPoints.CauchyApproximation
