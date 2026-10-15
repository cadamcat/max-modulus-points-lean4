import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.CauchyApproximation.RealInverseGrowth
import MaxModulusPoints.WallGrowth.CircleControl
import MaxModulusPoints.WallGrowth.RightCuts
/-!
# Quadratic inverse growth throughout a chamber and gate tract

Connected right-hand portions and short restricted circular images compare
an arbitrary point with the positive real axis. The real-axis quadratic
bound consequently controls the whole tract.
-/

namespace MaxModulusPoints.WallGrowth

open Set Filter Metric Complex Blueprint TractGeometry CauchyApproximation

/-- A universal coefficient for quadratic growth of the exponential inverse. -/
noncomputable def inverseGrowthConstant : ℝ :=
  130 * Real.exp 2 * Real.exp (64 * Real.pi) ^ 2

theorem inverseGrowthConstant_pos : 0 < inverseGrowthConstant := by
  unfold inverseGrowthConstant
  positivity

/-- The exponential of each tract point is bounded quadratically in the
norm of its target value, uniformly in the chambers and gates. -/
theorem norm_exp_le_quadratic (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) (G : LogModel (tract p δ))
    {z : ℂ} (hz : z ∈ tract p δ) (hx : 0 < z.re) :
    ‖Complex.exp z‖ ≤ inverseGrowthConstant * (max 2 ‖G.toFun z‖) ^ 2 := by
  let f : ℂ → ℂ := fun w => Complex.exp (-G.invFun w)
  have hf : DifferentiableOn ℂ f target := G.inverse_holomorphic.neg.cexp
  have hinj : InjOn f target := by
    intro w hw v hv heq
    have hexp : Complex.exp (G.invFun w) = Complex.exp (G.invFun v) := by
      apply inv_injective
      simpa only [f, Complex.exp_neg] using heq
    have hinv := G.exp_injective (G.inverse_mapsTo hw) (G.inverse_mapsTo hv) hexp
    calc
      w = G.toFun (G.invFun w) := (G.right_inv w hw).symm
      _ = G.toFun (G.invFun v) := congrArg G.toFun hinv
      _ = v := G.right_inv v hv
  let R : ℝ := max 2 ‖G.toFun z‖
  let Q : ℝ := R * Real.exp (64 * Real.pi)
  let D : ℝ := 65 * Q ^ 2
  let r : ℝ := 1 / D
  have hR : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hQ : 0 < Q := mul_pos hR (Real.exp_pos _)
  have hD : 0 < D := by dsimp [D]; positivity
  have hr : 0 < r := one_div_pos.mpr hD
  obtain ⟨ρ, hρ, hshort⟩ := exists_short_cutoff_circle hf hinj hr hR
  have hρone : 1 < ρ := by
    have htwo : 2 ≤ R := le_max_left _ _
    linarith [hρ.1]
  have hρpos : 0 < ρ := zero_lt_one.trans hρone
  have hρQ : ρ < Q := hρ.2
  have hreal : ‖Complex.exp (G.invFun (ρ : ℂ))‖ ≤ D := by
    calc
      _ ≤ 65 * Real.exp (-1) * ρ ^ 2 := logModel_exp_inverse_real_le _ G hρone.le
      _ ≤ 65 * ρ ^ 2 := by
        have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg ρ)]
      _ ≤ D := by dsimp [D]; nlinarith [sq_nonneg (Q - ρ)]
  have hstart : r ≤ ‖f (ρ : ℂ)‖ := by
    rw [show ‖f (ρ : ℂ)‖ = 1 / ‖Complex.exp (G.invFun (ρ : ℂ))‖ by
      simp only [f, Complex.exp_neg, norm_inv, one_div]]
    exact one_div_le_one_div_of_le (norm_pos_iff.mpr (Complex.exp_ne_zero _)) hreal
  obtain ⟨s, _, hnear, hsz, hline⟩ := exists_nearby_right_cut p δ hx
  have hscale : inverseGrowthConstant * R ^ 2 = 2 * Real.exp 2 * D := by
    dsimp [inverseGrowthConstant, D, Q]
    ring
  change ‖Complex.exp z‖ ≤ inverseGrowthConstant * R ^ 2
  by_contra h
  have hbig : 2 * Real.exp 2 * D < ‖Complex.exp z‖ := by
    rw [← hscale]
    exact lt_of_not_ge h
  have hcoord : Real.exp z.re ≤ Real.exp 2 * Real.exp s := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hslarge : 2 * D < Real.exp s := by
    rw [Complex.norm_exp] at hbig
    nlinarith [Real.exp_pos 2]
  have hsmall : Real.exp (-s) < r / 2 := by
    calc
      Real.exp (-s) = 1 / Real.exp s := by rw [Real.exp_neg, one_div]
      _ < 1 / (2 * D) := one_div_lt_one_div_of_lt (by positivity) hslarge
      _ = r / 2 := by dsimp [r]; ring
  obtain ⟨v, hv, hsv, hvnorm⟩ := right_cut_meets_circle p δ hδ G hline hz hsz
    ((le_max_right 2 ‖G.toFun z‖).trans hρ.1.le)
  have hupper : ∃ u ∈ tract p δ,
      s ≤ u.re ∧ ‖G.toFun u‖ = ρ ∧ 0 ≤ (G.toFun u).arg := by
    by_cases him : 0 ≤ (G.toFun v).im
    · exact ⟨v, hv, hsv, hvnorm, Complex.arg_nonneg_iff.mpr him⟩
    · have hsym := G.symmetric_map v hv
      refine ⟨star v, G.symmetric_domain v hv, ?_, ?_, ?_⟩
      · simpa only [Complex.star_def, Complex.conj_re] using hsv
      · rw [hsym, norm_star]
        exact hvnorm
      · apply Complex.arg_nonneg_iff.mpr
        rw [hsym]
        simp only [Complex.star_def, Complex.conj_im]
        linarith
  obtain ⟨u, hu, hsu, hunorm, huarg⟩ := hupper
  have hend : ‖f (G.toFun u)‖ < r / 2 := by
    change ‖Complex.exp (-G.invFun (G.toFun u))‖ < r / 2
    rw [G.left_inv u hu, Complex.norm_exp, Complex.neg_re]
    exact (Real.exp_le_exp.mpr (neg_le_neg hsu)).trans_lt hsmall
  have hlower := cutoff_circle_length_lower hf hρone hr (G.mapsTo hu) hunorm huarg hstart hend
  exact (not_lt_of_ge hlower) hshort

end MaxModulusPoints.WallGrowth
