import MaxModulusPoints.CauchyApproximation.ArcDecay
import MaxModulusPoints.CauchyApproximation.ContourTube
import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
import MaxModulusPoints.CauchyApproximation.LocalDetour
import MaxModulusPoints.CauchyApproximation.Model
/-!
# Minimal near parameters and separation outside the selected disk

A nonempty closed set of near parameters has a point of minimal absolute
parameter. If the tube radii decrease with the absolute parameter, all
points of the contour outside the selected disk remain at least half
their own tube radius from the evaluation point. This provides the
separation estimate for the surviving part of a contour replacement.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Continuous contour and radius data have a near point of minimal absolute
parameter whenever their closed near set is nonempty. -/
theorem exists_minimal_abs_near_parameter {γ : ℝ → ℂ} {δ : ℝ → ℝ}
    (hγ : Continuous γ) (hδ : Continuous δ) {z : ℂ}
    (hnear : ∃ t, ‖γ t - z‖ ≤ δ t / 2) :
    ∃ t₀ : ℝ, ‖γ t₀ - z‖ ≤ δ t₀ / 2 ∧
      ∀ t, ‖γ t - z‖ ≤ δ t / 2 → |t₀| ≤ |t| := by
  let S : Set ℝ := {t | ‖γ t - z‖ ≤ δ t / 2}
  have hS : IsClosed S := isClosed_le ((hγ.sub continuous_const).norm) (hδ.div_const 2)
  obtain ⟨t₁, ht₁⟩ := hnear
  have hK : IsCompact (S ∩ Icc (-|t₁|) |t₁|) := isCompact_Icc.inter_left hS
  have hne : (S ∩ Icc (-|t₁|) |t₁|).Nonempty := ⟨t₁, ht₁, abs_le.1 le_rfl⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hK.exists_isMinOn hne continuous_abs.continuousOn
  refine ⟨t₀, ht₀.1, ?_⟩
  intro t ht
  by_cases habs : |t| ≤ |t₁|
  · exact (isMinOn_iff.1 hmin) t ⟨ht, abs_le.1 habs⟩
  · exact (abs_le.2 ht₀.2).trans (lt_of_not_ge habs).le

/-- Minimality handles smaller parameters, and decreasing radii handle larger
ones, giving half-radius separation outside the selected disk. -/
theorem half_radius_separation_of_minimal_parameter {γ : ℝ → ℂ} {δ : ℝ → ℝ}
    {z : ℂ} {t₀ : ℝ} (hnear : ‖γ t₀ - z‖ ≤ δ t₀ / 2)
    (hmin : ∀ t, ‖γ t - z‖ ≤ δ t / 2 → |t₀| ≤ |t|)
    (hmono : ∀ s t, |s| ≤ |t| → δ t ≤ δ s) {t : ℝ}
    (hout : δ t₀ ≤ ‖γ t - γ t₀‖) :
    δ t / 2 ≤ ‖γ t - z‖ := by
  by_cases habs : |t₀| ≤ |t|
  · have hδ := hmono t₀ t habs
    have htriangle : ‖γ t - γ t₀‖ ≤ ‖γ t - z‖ + ‖γ t₀ - z‖ := by
      simpa only [dist_eq_norm, norm_sub_rev z (γ t₀)] using dist_triangle (γ t) z (γ t₀)
    linarith
  · by_contra! hbad
    exact habs (hmin t hbad.le)

/-- The scaled quartic radius is continuous and decreasing with absolute
parameter, so its near set has a minimum giving separation off one disk. -/
theorem exists_minimal_scaled_near_parameter {γ : ℝ → ℂ} (hγ : Continuous γ)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) {z : ℂ}
    (hnear : ∃ t, ‖γ t - z‖ ≤ (ε * σ / (max |t| 1) ^ 4) / 2) :
    ∃ t₀ : ℝ,
      ‖γ t₀ - z‖ ≤ (ε * σ / (max |t₀| 1) ^ 4) / 2 ∧
      (∀ t, ‖γ t - z‖ ≤ (ε * σ / (max |t| 1) ^ 4) / 2 → |t₀| ≤ |t|) ∧
      ∀ t, ε * σ / (max |t₀| 1) ^ 4 ≤ ‖γ t - γ t₀‖ →
        (ε * σ / (max |t| 1) ^ 4) / 2 ≤ ‖γ t - z‖ := by
  let δ : ℝ → ℝ := fun t ↦ ε * σ / (max |t| 1) ^ 4
  have hδ : Continuous δ :=
    continuous_const.div ((continuous_abs.max continuous_const).pow 4)
      (fun t ↦ ne_of_gt (by positivity : 0 < (max |t| 1) ^ 4))
  obtain ⟨t₀, ht₀, hmin⟩ := exists_minimal_abs_near_parameter hγ hδ hnear
  have hmono : ∀ s t, |s| ≤ |t| → δ t ≤ δ s := by
    intro s t hst
    apply div_le_div_of_nonneg_left (by positivity : 0 ≤ ε * σ)
      (by positivity : 0 < (max |s| 1) ^ 4)
    exact pow_le_pow_left₀ (by positivity) (max_le_max hst le_rfl) 4
  refine ⟨t₀, ht₀, hmin, ?_⟩
  intro t hout
  exact half_radius_separation_of_minimal_parameter ht₀ hmin hmono hout

/-- The actual canonical contour admits the minimal near parameter and the
pointwise separation needed on the surviving part of the curve. -/
theorem NormalizedModel.exists_minimal_near_parameter (m : NormalizedModel)
    {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hnear : ∃ t, ‖m.contour t - z‖ ≤
      (ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2) :
    ∃ t₀ : ℝ,
      ‖m.contour t₀ - z‖ ≤ (ε * ‖deriv m.inverse 1‖ / (max |t₀| 1) ^ 4) / 2 ∧
      (∀ t, ‖m.contour t - z‖ ≤
        (ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2 → |t₀| ≤ |t|) ∧
      ∀ t, ε * ‖deriv m.inverse 1‖ / (max |t₀| 1) ^ 4 ≤
          ‖m.contour t - m.contour t₀‖ →
        (ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2 ≤ ‖m.contour t - z‖ :=
  exists_minimal_scaled_near_parameter m.proper_contour_and_localDetour_holomorphy.1.continuous
    hε m.norm_inverse_deriv_one_pos hnear

#print axioms exists_minimal_abs_near_parameter
#print axioms half_radius_separation_of_minimal_parameter
#print axioms exists_minimal_scaled_near_parameter
#print axioms NormalizedModel.exists_minimal_near_parameter

end MaxModulusPoints.CauchyApproximation
