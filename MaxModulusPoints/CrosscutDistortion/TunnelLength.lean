module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.PotentialSpeed
public import MaxModulusPoints.CrosscutDistortion.TunnelHalfLength

/-!
# Weighted length of a tunnel crosscut

The positive and negative halves of an interior tunnel crosscut each
contribute at least one half to its slab-weighted length. Negating the
real parameter identifies the negative-half speed with the full speed.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set MeasureTheory Blueprint

/-- An interior tunnel crosscut has slab-weighted length at least one,
assuming integrability of its full weighted speed. -/
theorem tunnel_weighted_length (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    (w z : ℂ) (hw : w ∈ passageSlice p n) (hz : z ∈ cleanSlice p n)
    (hwV : w ∈ tract p δ) (hzV : z ∈ tract p δ)
    (hspeed : IntervalIntegrable
      (slabWeightedSpeed (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        (fun t : ℝ => φ.toFun ((s : ℂ) + t * Complex.I)))
      volume (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2)) :
    1 ≤ ∫ t in (-p.tunnelHeight n / 2)..(p.tunnelHeight n / 2),
      slabWeightedSpeed (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        (fun u : ℝ => φ.toFun ((s : ℂ) + u * Complex.I)) t := by
  let H : ℝ := p.tunnelHeight n / 2
  let a : ℝ := (φ.toFun w).re
  let b : ℝ := max a (φ.toFun z).re
  let γ : ℝ → ℂ := fun t => φ.toFun ((s : ℂ) + t * Complex.I)
  let g : ℝ → ℝ := slabWeightedSpeed a b γ
  have hH : 0 < H := half_pos (p.tunnel_pos n)
  have hfull : IntervalIntegrable g volume (-H) H := by
    simpa only [neg_div] using hspeed
  have hleft : IntervalIntegrable g volume (-H) 0 := by
    apply hfull.mono_set
    rw [uIcc_of_le (by linarith : -H ≤ 0), uIcc_of_le (by linarith : -H ≤ H)]
    exact Icc_subset_Icc le_rfl hH.le
  have hright : IntervalIntegrable g volume 0 H := by
    apply hfull.mono_set
    rw [uIcc_of_le hH.le, uIcc_of_le (by linarith : -H ≤ H)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hnegative : slabWeightedSpeed a b (fun t => γ (-t)) = fun t => g (-t) := by
    funext t
    simp only [g, slabWeightedSpeed, deriv_comp_neg, norm_neg]
  have hnegintegrable : IntervalIntegrable (fun t => g (-t)) volume 0 H := by
    have h := (IntervalIntegrable.iff_comp_neg (f := g) (a := -H) (b := 0)).mp hleft
    simpa only [neg_neg, neg_zero] using h.symm
  have hplus : 1 / 2 ≤ ∫ t in 0..H, g t := by
    simpa only [one_mul] using
      tunnel_half_weighted_length p δ φ hφ0 hφre hφim n s hs w z hw hz hwV hzV
        1 (by norm_num) (by simpa only [one_mul] using hright)
  have hminus : 1 / 2 ≤ ∫ t in 0..H, g (-t) := by
    have hsigned : IntervalIntegrable
        (slabWeightedSpeed a b (fun t : ℝ => φ.toFun ((s : ℂ) + (-1 * t : ℝ) * Complex.I)))
        volume 0 H := by
      simpa only [neg_one_mul, ← hnegative] using hnegintegrable
    have h := tunnel_half_weighted_length p δ φ hφ0 hφre hφim n s hs w z hw hz
      hwV hzV (-1) (by norm_num) hsigned
    simp only [neg_one_mul] at h
    change 1 / 2 ≤ ∫ t in 0..H, slabWeightedSpeed a b (fun u => γ (-u)) t at h
    simpa only [hnegative] using h
  rw [intervalIntegral.integral_comp_neg, neg_zero] at hminus
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have htotal : 1 ≤ ∫ t in (-H)..H, g t := by linarith
  simpa only [neg_div] using htotal

end MaxModulusPoints.CrosscutDistortion
