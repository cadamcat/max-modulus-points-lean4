module

public import MaxModulusPoints.CauchyApproximation.CanonicalApproximation
public import MaxModulusPoints.CauchyApproximation.CanonicalDecay
public import MaxModulusPoints.CauchyApproximation.ContourTube
public import MaxModulusPoints.CauchyApproximation.DetourBounds
public import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral
public import MaxModulusPoints.CauchyApproximation.InverseDistortion
public import MaxModulusPoints.CauchyApproximation.LocalDetour
public import MaxModulusPoints.CauchyApproximation.MinimalParameter
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.QuantitativeDetour
public import MaxModulusPoints.CauchyApproximation.SeparatedDecay

/-!
# Separation and decay for the whole modified contour

A near parameter of minimal absolute value supplies separation on the
unchanged tails. The tent's uniform avoidance of a scaled ball supplies
separation on the modified interval. The actual modified Cauchy integral
therefore has uniform inverse-norm decay, and its established agreement
with the canonical entire function gives the same bound near the original
contour, including on that contour.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Minimality controls the unchanged part with smaller absolute parameter;
ball avoidance and local radius comparison control the rest of the detour. -/
theorem half_radius_separation_of_minimal_parameter_detour
    {γ η : ℝ → ℂ} {δ : ℝ → ℝ} {s : ℝ} {z : ℂ}
    (hδ : 0 ≤ δ s) (hnear : ‖γ s - z‖ ≤ δ s / 2)
    (hmin : ∀ t, ‖γ t - z‖ ≤ δ t / 2 → |s| ≤ |t|)
    (hmono : ∀ t, |s| ≤ |t| → δ t ≤ δ s)
    (hlocal : ∀ t, |t - s| ≤ 1 → δ t ≤ 16 * δ s)
    (hagree : ∀ t, 1 < |t - s| → η t = γ t)
    (haway : ∀ t, 64 * δ s ≤ ‖η t - γ s‖) :
    ∀ t, δ t / 2 ≤ ‖η t - z‖ := by
  intro t
  have htriangle : ‖η t - γ s‖ ≤ ‖η t - z‖ + ‖γ s - z‖ := by
    simpa only [dist_eq_norm, norm_sub_rev z (γ s)] using dist_triangle (η t) z (γ s)
  by_cases ht : |t - s| ≤ 1
  · have hl := hlocal t ht
    have ha := haway t
    linarith
  · by_cases habs : |s| ≤ |t|
    · have hm := hmono t habs
      have ha := haway t
      linarith
    · rw [hagree t (lt_of_not_ge ht)]
      by_contra! hbad
      exact habs (hmin t hbad.le)

/-- Moving a parameter by at most one changes its scaled quartic radius by
at most a factor sixteen. -/
theorem scaled_quartic_radius_local_comparison {ε σ s t : ℝ}
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (ht : |t - s| ≤ 1) :
    ε * σ / (max |t| 1) ^ 4 ≤ 16 * (ε * σ / (max |s| 1) ^ 4) := by
  have hst : |s| ≤ |t - s| + |t| := by
    have h := norm_add_le (s - t) t
    simpa only [sub_add_cancel, Real.norm_eq_abs, abs_sub_comm s t] using h
  have hb : max |s| 1 ≤ 2 * max |t| 1 := by
    apply max_le
    · linarith [le_max_left |t| 1, le_max_right |t| 1]
    · linarith [le_max_right |t| 1]
  have hp : (max |s| 1) ^ 4 ≤ 16 * (max |t| 1) ^ 4 := by
    calc
      _ ≤ (2 * max |t| 1) ^ 4 := pow_le_pow_left₀ (by positivity) hb 4
      _ = _ := by ring
  have hps : 0 < (max |s| 1) ^ 4 := by positivity
  have hpt : 0 < (max |t| 1) ^ 4 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hpt hps).2
  calc
    _ ≤ (ε * σ) * (16 * (max |t| 1) ^ 4) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hε hσ)
    _ = _ := by ring

/-- One near-set coefficient gives a genuine modified contour separated
everywhere from the evaluation point and with the correct canonical value. -/
theorem exists_scaled_near_detour :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (m : NormalizedModel) (z : ℂ),
      (∃ t, ‖m.contour t - z‖ ≤
        (ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2) →
      ∃ s : ℝ,
        (∀ t, (ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2 ≤
          ‖m.localDetour s t - z‖) ∧
        m.canonicalEntire z = cauchyIntegral (m.localDetour s)
          (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t) z := by
  obtain ⟨β, hβ, hball⟩ := exists_scaled_localDetour_agreement
  let ε : ℝ := β / 64
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨ε, hε, ?_⟩
  intro m z hnear
  obtain ⟨s, hs, hmin, -⟩ := m.exists_minimal_near_parameter hε hnear
  let δ : ℝ → ℝ := fun t ↦ ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4
  let r : ℝ := β * ‖deriv m.inverse 1‖ / (max |s| 1) ^ 4
  have hscale := m.norm_inverse_deriv_one_pos
  have hδ : 0 < δ s := by dsimp only [δ]; positivity
  have hr : r = 64 * δ s := by dsimp only [r, δ, ε]; ring
  obtain ⟨-, havoid, -, hvalue⟩ := hball m s
  have haway (t : ℝ) : 64 * δ s ≤ ‖m.localDetour s t - m.contour s‖ := by
    rw [← hr]
    by_contra! hbad
    have hin : m.localDetour s t ∈ Metric.ball (m.contour s) r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hbad
    exact havoid hin ⟨t, rfl⟩
  have hmono (t : ℝ) (ht : |s| ≤ |t|) : δ t ≤ δ s := by
    apply div_le_div_of_nonneg_left (by positivity : 0 ≤ ε * ‖deriv m.inverse 1‖)
      (by positivity : 0 < (max |s| 1) ^ 4)
    exact pow_le_pow_left₀ (by positivity) (max_le_max ht le_rfl) 4
  obtain ⟨-, -, hagree, -, -⟩ :=
    m.localDetour_properties s m.proper_contour_and_localDetour_holomorphy.1
  have heq (t : ℝ) (ht : 1 < |t - s|) : m.localDetour s t = m.contour t := by
    apply hagree
    intro hin
    have habs : |t - s| < 1 := abs_lt.2 ⟨by linarith [hin.1], by linarith [hin.2]⟩
    linarith
  have hsep := half_radius_separation_of_minimal_parameter_detour hδ.le hs hmin hmono
    (fun t ht ↦ scaled_quartic_radius_local_comparison hε.le hscale.le ht) heq haway
  refine ⟨s, hsep, ?_⟩
  apply hvalue
  have hnorm : ‖z - m.contour s‖ < r := by
    rw [norm_sub_rev]
    change ‖m.contour s - z‖ ≤ δ s / 2 at hs
    rw [hr]
    linarith
  simpa only [Metric.mem_ball, dist_eq_norm] using hnorm

/-- The canonical entire function has a uniform inverse-norm bound on one
scaled neighborhood of its original contour, including the contour itself. -/
theorem exists_uniform_near_canonical_bound :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ (m : NormalizedModel) (z : ℂ),
      0 < ‖z‖ →
      (∃ t, ‖m.contour t - z‖ ≤
        (ε * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4) / 2) →
      ‖m.canonicalEntire z‖ ≤ C / ‖z‖ := by
  obtain ⟨ε, hε, hdetour⟩ := exists_scaled_near_detour
  obtain ⟨A, hA, hpos⟩ := exists_uniform_localDetour_position_bound
  obtain ⟨D, hD, hdensity⟩ := exists_scaled_localDetour_density_bound
  let S : ℝ := 4 * Real.exp (-1)
  let B : ℝ := 4 * Real.pi * D * S + (4 * Real.pi + 1) * (A * D / (ε / 2))
  let K : ℝ := ‖(2 * (Real.pi : ℂ) * I)⁻¹‖
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hB : 0 ≤ B := by dsimp only [B, S]; positivity
  have hK : 0 ≤ K := norm_nonneg _
  refine ⟨ε, K * B + 1, hε, by positivity, ?_⟩
  intro m z hz hnear
  obtain ⟨s, hsep, heq⟩ := hdetour m z hnear
  obtain ⟨hproper, hρ, -⟩ :=
    m.proper_contour_and_localDetour_holomorphy.2 s m.integrable_density
  have hsep' (t : ℝ) : (ε / 2) * ‖deriv m.inverse 1‖ / (max |t| 1) ^ 4 ≤
      ‖m.localDetour s t - z‖ := by
    convert hsep t using 1
    ring
  have h := norm_cauchyIntegral_le_of_quartic_growth hproper hρ hA hD.le
    m.norm_inverse_deriv_one_pos m.norm_inverse_deriv_one_le (by positivity : 0 < ε / 2)
    (hpos m s) (hdensity m s) hz hsep'
  rw [heq]
  change ‖cauchyIntegral (m.localDetour s)
    (fun t ↦ m.modelFunction (m.localDetour s t) * deriv (m.localDetour s) t) z‖ ≤
      (K * B + 1) / ‖z‖
  calc
    _ ≤ K * (B / ‖z‖) := h
    _ = (K * B) / ‖z‖ := by ring
    _ ≤ (K * B + 1) / ‖z‖ := div_le_div_of_nonneg_right (by linarith) hz.le

#print axioms half_radius_separation_of_minimal_parameter_detour
#print axioms scaled_quartic_radius_local_comparison
#print axioms exists_scaled_near_detour
#print axioms exists_uniform_near_canonical_bound

end MaxModulusPoints.CauchyApproximation
