module

public import TauCeti.Analysis.Complex.Conformal.SchwarzPick.Basic
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.ExponentialChart
public import MaxModulusPoints.StripMap.Symmetry

/-!
# Imaginary contraction for symmetric strip maps

Schwarz--Pick applied to conjugate points shows that a symmetric holomorphic
self-map of the strip contracts the absolute imaginary coordinate.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology ComplexConjugate

theorem halfToDisc_conj (z : ℂ) : halfToDisc (conj z) = conj (halfToDisc z) := by
  simp [halfToDisc]

theorem stripExp_conj (z : ℂ) : stripExp (conj z) = conj (stripExp z) := by
  change Complex.exp ((Real.pi : ℂ) * conj z) = conj (Complex.exp ((Real.pi : ℂ) * z))
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]

theorem halfToDisc_reflected_distance {u : ℂ} (hu : u ∈ rightHalfPlane) :
    TauCeti.pseudoHyperbolicExpr (halfToDisc u) (halfToDisc (conj u)) = |u.im| / ‖u‖ := by
  have huc : conj u ∈ rightHalfPlane := by simpa only [rightHalfPlane, mem_ofPred_eq,
    Complex.conj_re] using hu
  have hn : u ≠ 0 := by
    intro h
    simpa only [rightHalfPlane, mem_ofPred_eq, h, Complex.zero_re, lt_self_iff_false] using hu
  have ha := half_add_one_ne_zero hu
  have hac := half_add_one_ne_zero huc
  have hden := TauCeti.one_sub_conj_mul_ne_zero_of_norm_lt_one
    (mem_ball_zero_iff.mp (halfToDisc_mapsTo hu))
    (mem_ball_zero_iff.mp (halfToDisc_mapsTo huc))
  have hstar : conj (halfToDisc (conj u)) = halfToDisc u := by
    rw [halfToDisc_conj, Complex.conj_conj]
  have hid : (halfToDisc u - halfToDisc (conj u)) /
      (1 - conj (halfToDisc (conj u)) * halfToDisc u) =
      ((u - conj u) / (2 * u)) * ((u + 1) / (conj u + 1)) := by
    apply (div_eq_iff hden).mpr
    rw [hstar]
    dsimp only [halfToDisc]
    field_simp [hn, ha, hac]
    ring
  have hc : ‖conj u + 1‖ = ‖u + 1‖ := by
    simpa only [map_add, map_one] using Complex.norm_conj (u + 1)
  have hi : u - conj u = ((2 * u.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [TauCeti.pseudoHyperbolicExpr_def, hid, norm_mul, norm_div, norm_div, hc,
    div_self (norm_ne_zero_iff.mpr ha), mul_one, hi, norm_mul, Complex.norm_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    norm_mul]
  norm_num
  field_simp <;> ring

theorem strip_reflected_distance {z : ℂ} (hz : z ∈ strip) :
    TauCeti.pseudoHyperbolicExpr (stripToDisc z) (stripToDisc (conj z)) =
      |Real.sin (Real.pi * z.im)| := by
  rw [stripToDisc, stripToDisc, stripExp_conj,
    halfToDisc_reflected_distance (stripExp_mapsTo hz)]
  simp only [stripExp, Complex.exp_im, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

theorem strip_symmetric_selfMap_im_abs_le {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f strip) (hm : MapsTo f strip strip)
    (hs : ∀ z ∈ strip, f (conj z) = conj (f z)) {z : ℂ} (hz : z ∈ strip) :
    |(f z).im| ≤ |z.im| := by
  let g : ℂ → ℂ := fun w => stripToDisc (f (discToStrip w))
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    stripToDisc_differentiableOn.comp
      (hd.comp discToStrip_differentiableOn discToStrip_mapsTo)
      (hm.comp discToStrip_mapsTo)
  have hgm : MapsTo g (ball 0 1) (ball 0 1) :=
    stripToDisc_mapsTo.comp (hm.comp discToStrip_mapsTo)
  have hconj := conj_mem_strip hz
  have h := TauCeti.pseudoHyperbolicExpr_map_le hgd hgm
    (stripToDisc_mapsTo hz) (stripToDisc_mapsTo hconj)
  have hpoint : ∀ w ∈ strip, g (stripToDisc w) = stripToDisc (f w) := by
    intro w hw
    dsimp only [g]
    rw [discToStrip_stripToDisc hw]
  rw [hpoint z hz, hpoint (conj z) hconj, strip_reflected_distance hz] at h
  have hf : TauCeti.pseudoHyperbolicExpr (stripToDisc (f z))
      (stripToDisc (f (conj z))) = |Real.sin (Real.pi * (f z).im)| := by
    rw [hs z hz]
    exact strip_reflected_distance (hm hz)
  rw [hf] at h
  have hzabs : |Real.pi * z.im| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [show |z.im| < 1 / 2 from hz, Real.pi_pos]
  have hfabs : |Real.pi * (f z).im| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [show |(f z).im| < 1 / 2 from hm hz, Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos]),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])] at h
  have harg := (Real.strictMonoOn_sin.le_iff_le
    (show |Real.pi * (f z).im| ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [abs_nonneg (Real.pi * (f z).im)])
    (show |Real.pi * z.im| ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [abs_nonneg (Real.pi * z.im)])).mp h
  simpa only [abs_mul, abs_of_pos Real.pi_pos, mul_le_mul_iff_right₀ Real.pi_pos] using harg

end MaxModulusPoints.StripMap
