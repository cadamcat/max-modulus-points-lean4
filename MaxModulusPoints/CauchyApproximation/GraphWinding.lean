module

public import TauCeti.Analysis.Contour.LogDerivFTC
public import MaxModulusPoints.CauchyApproximation.ResidueJump

/-!
# Winding between two graphs

An upward graph and a downward return graph with shared endpoints form a
closed curve. Splitting both arcs at the imaginary coordinate of a point
evaluates their winding integrals by the logarithmic fundamental theorem of
calculus in the two half-planes. The endpoint terms cancel. The remaining
branch terms give winding number −1 between the graphs and zero to their left.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open TauCeti.Contour
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Follow a graph upward and a second graph backward. To the left of the
return graph, the resulting loop winds clockwise once
precisely when the point lies to the right of the first graph. -/
theorem windingNumber_graph_difference {γ η : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (hγ : IsPiecewiseC1On γ a b) (hη : IsPiecewiseC1On η a b)
    (hγim : ∀ t ∈ Icc a b, (γ t).im = t)
    (hηim : ∀ t ∈ Icc a b, (η t).im = t)
    (ha : γ a = η a) (hb : γ b = η b) (hz : z.im ∈ Ioo a b)
    (hzγ : (γ z.im).re ≠ z.re) (hzη : z.re < (η z.im).re) :
    windingNumber (closedContourDifference γ η b) a (2 * b - a) z =
      if (γ z.im).re < z.re then (-1 : ℂ) else 0 := by
  have hab : a ≤ b := hz.1.le.trans hz.2.le
  have hzu : z.im ∈ uIcc a b := (uIcc_of_le hab).symm ▸ ⟨hz.1.le, hz.2.le⟩
  have hlog {v : ℂ} (hvim : v.im = 0) (hvre : v.re ≠ 0) :
      log (-v) - log v = if v.re < 0 then -(Real.pi : ℂ) * I else (Real.pi : ℂ) * I := by
    have hvreal : v = (v.re : ℂ) := by
      apply Complex.ext <;> simp [hvim]
    by_cases hn : v.re < 0
    · rw [if_pos hn]
      apply Complex.ext
      · simp [Complex.log_re]
      · simp only [sub_im, log_im]
        rw [hvreal, ← ofReal_neg, arg_ofReal_of_nonneg (by linarith),
          arg_ofReal_of_neg hn]
        simp
    · have hp : 0 < v.re := lt_of_le_of_ne (le_of_not_gt hn) hvre.symm
      rw [if_neg hn]
      apply Complex.ext
      · simp [Complex.log_re]
      · simp only [sub_im, log_im]
        rw [hvreal, ← ofReal_neg, arg_ofReal_of_neg (by linarith),
          arg_ofReal_of_nonneg hp.le]
        simp
  have hgraph {θ : ℝ → ℂ} (hθ : IsPiecewiseC1On θ a b)
      (him : ∀ t ∈ Icc a b, (θ t).im = t) (hne : (θ z.im).re ≠ z.re) :
      (∀ t ∈ uIcc a b, θ t ≠ z) ∧
        (∫ t in a..b, deriv θ t / (θ t - z)) =
          log (θ b - z) - log (-(θ a - z)) +
            (if (θ z.im).re < z.re then -(Real.pi : ℂ) * I else (Real.pi : ℂ) * I) := by
    have hoff (t : ℝ) (ht : t ∈ uIcc a b) : θ t ≠ z := by
      intro heq
      have ht' : t = z.im := (him t ((uIcc_of_le hab) ▸ ht)).symm.trans
        (congrArg Complex.im heq)
      exact hne (congrArg Complex.re (ht' ▸ heq))
    let Q : ℝ → ℂ := fun t ↦ θ t - z
    have hQ : IsPiecewiseC1On Q a b :=
      hθ.sub (IsPiecewiseC1On.of_contDiffOn contDiffOn_const)
    have hQne (t : ℝ) (ht : t ∈ uIcc a b) : Q t ≠ 0 := sub_ne_zero.2 (hoff t ht)
    have hlow : IsPiecewiseC1On Q a z.im := by
      apply hQ.mono
      rw [uIcc_of_le hz.1.le, uIcc_of_le hab]
      exact fun t ht ↦ ⟨ht.1, ht.2.trans hz.2.le⟩
    have hupp : IsPiecewiseC1On Q z.im b := by
      apply hQ.mono
      rw [uIcc_of_le hz.2.le, uIcc_of_le hab]
      exact fun t ht ↦ ⟨hz.1.le.trans ht.1, ht.2⟩
    have hlowmem : uIcc a z.im ⊆ uIcc a b := by
      rw [uIcc_of_le hz.1.le, uIcc_of_le hab]
      exact fun t ht ↦ ⟨ht.1, ht.2.trans hz.2.le⟩
    have huppmem : uIcc z.im b ⊆ uIcc a b := by
      rw [uIcc_of_le hz.2.le, uIcc_of_le hab]
      exact fun t ht ↦ ⟨hz.1.le.trans ht.1, ht.2⟩
    have hint {c d : ℝ} (hpc : IsPiecewiseC1On Q c d)
        (hmem : uIcc c d ⊆ uIcc a b) :
        IntervalIntegrable (fun t ↦ deriv Q t / Q t) volume c d := by
      simpa only [sub_zero, inv_mul_eq_div] using
        intervalIntegrable_inv_sub_mul_deriv hpc.continuousOn
          (fun t ht ↦ hQne t (hmem ht)) hpc.intervalIntegrable_deriv
    obtain ⟨P, hP, hdiff⟩ := hlow.exists_countable_differentiableAt
    have hlo := intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_neg_sub_log_neg_of_im_nonpos
      (g := Q) (h := Q) hP hlow.continuousOn hdiff (hint hlow hlowmem)
      (fun t ht ↦ by
        rw [uIcc_of_le hz.1.le] at ht
        simp only [Q, sub_im, him t ⟨ht.1, ht.2.trans hz.2.le⟩]
        linarith [ht.2])
      (hQne a left_mem_uIcc) (hQne z.im hzu)
      (fun t ht ↦ by
        rw [min_eq_left hz.1.le, max_eq_right hz.1.le] at ht
        apply mem_slitPlane_iff.2
        right
        simp only [neg_im, Q, sub_im, him t ⟨ht.1.le, ht.2.le.trans hz.2.le⟩]
        linarith [ht.2])
      (fun _ _ ↦ rfl) rfl rfl
    obtain ⟨P', hP', hdiff'⟩ := hupp.exists_countable_differentiableAt
    have hhi := intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg
      (g := Q) (h := Q) hP' hupp.continuousOn hdiff' (hint hupp huppmem)
      (fun t ht ↦ by
        rw [uIcc_of_le hz.2.le] at ht
        simp only [Q, sub_im, him t ⟨hz.1.le.trans ht.1, ht.2⟩]
        linarith [ht.1])
      (hQne z.im hzu) (hQne b right_mem_uIcc)
      (fun t ht ↦ by
        rw [min_eq_left hz.2.le, max_eq_right hz.2.le] at ht
        apply mem_slitPlane_iff.2
        right
        simp only [Q, sub_im, him t ⟨hz.1.le.trans ht.1.le, ht.2.le⟩]
        linarith [ht.1])
      (fun _ _ ↦ rfl) rfl rfl
    have hbranch := hlog (v := Q z.im)
      (by simp only [Q, sub_im, him z.im (Ioo_subset_Icc_self hz), sub_self])
      (by simpa only [Q, sub_re, sub_ne_zero] using hne)
    have hsum := intervalIntegral.integral_add_adjacent_intervals hlo.1 hhi.1
    rw [hlo.2, hhi.2] at hsum
    refine ⟨hoff, ?_⟩
    calc
      _ = ∫ t in a..b, deriv Q t / Q t := by simp only [Q, deriv_sub_const]
      _ = log (-(Q z.im)) - log (-(Q a)) + (log (Q b) - log (Q z.im)) := hsum.symm
      _ = log (Q b) - log (-(Q a)) + (log (-(Q z.im)) - log (Q z.im)) := by ring
      _ = _ := by
        rw [hbranch]
        dsimp only [Q]
        simp only [sub_re, sub_lt_zero]
  obtain ⟨hγoff, hγint⟩ := hgraph hγ hγim hzγ
  obtain ⟨hηoff, hηint⟩ := hgraph hη hηim (ne_of_gt hzη)
  have hγi : IntervalIntegrable (fun t ↦ deriv γ t • (γ t - z)⁻¹) volume a b := by
    simpa only [smul_eq_mul, mul_comm] using
      intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn hγoff hγ.intervalIntegrable_deriv
  have hηi : IntervalIntegrable (fun t ↦ deriv η t • (η t - z)⁻¹) volume a b := by
    simpa only [smul_eq_mul, mul_comm] using
      intervalIntegrable_inv_sub_mul_deriv hη.continuousOn hηoff hη.intervalIntegrable_deriv
  let ηrev : ℝ → ℂ := fun t ↦ η (2 * b - t)
  let K := closedContourDifference γ η b
  have hbc : b ≤ 2 * b - a := by linarith
  have hac : a ≤ 2 * b - a := hab.trans hbc
  have hbb : 2 * b - b = b := by ring
  have haa : 2 * b - (2 * b - a) = a := by ring
  have hrev : IsPiecewiseC1On ηrev b (2 * b - a) := by
    simpa only [hbb] using (hη.comp_const_sub (2 * b)).symm
  have hK : IsPiecewiseC1On K a (2 * b - a) :=
    hγ.if_le hrev hab hbc (by simpa only [ηrev, hbb] using hb)
  have hrevOff (t : ℝ) (ht : t ∈ uIcc b (2 * b - a)) : ηrev t ≠ z := by
    apply hηoff (2 * b - t)
    rw [uIcc_of_le hbc] at ht
    rw [uIcc_of_le hab]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hKoff (t : ℝ) (ht : t ∈ uIcc a (2 * b - a)) : K t ≠ z := by
    rw [uIcc_of_le hac] at ht
    by_cases htb : t ≤ b
    · simp only [K, closedContourDifference, if_pos htb]
      exact hγoff t ((uIcc_of_le hab).symm ▸ ⟨ht.1, htb⟩)
    · simp only [K, closedContourDifference, if_neg htb]
      apply hrevOff t
      rw [uIcc_of_le hbc]
      exact ⟨(not_le.1 htb).le, ht.2⟩
  have hrevi : IntervalIntegrable (fun t ↦ deriv ηrev t • (ηrev t - z)⁻¹)
      volume b (2 * b - a) := by
    simpa only [smul_eq_mul, mul_comm] using
      intervalIntegrable_inv_sub_mul_deriv hrev.continuousOn hrevOff hrev.intervalIntegrable_deriv
  have heqγ : EqOn K γ (uIoo a b) := by
    intro t ht
    rw [uIoo_of_le hab] at ht
    simp only [K, closedContourDifference, if_pos ht.2.le]
  have heqη : EqOn K ηrev (uIoo b (2 * b - a)) := by
    intro t ht
    rw [uIoo_of_le hbc] at ht
    simp only [K, closedContourDifference, if_neg (not_le.2 ht.1), ηrev]
  have hsplit := intervalIntegral_deriv_smul_eq_add_of_eqOn (f := fun w : ℂ ↦ (w - z)⁻¹)
    heqγ heqη hγi hrevi
  have hreverse : (∫ t in b..(2 * b - a), deriv ηrev t • (ηrev t - z)⁻¹) =
      -(∫ t in a..b, deriv η t • (η t - z)⁻¹) := by
    calc
      _ = ∫ t in b..a, deriv η t • (η t - z)⁻¹ := by
        simpa only [hbb, haa] using
          intervalIntegral_deriv_smul_comp_const_sub η (fun w ↦ (w - z)⁻¹) b (2 * b - a) (2 * b)
      _ = _ := intervalIntegral.integral_symm _ _
  rw [hreverse, ← sub_eq_add_neg] at hsplit
  have hnormalized : windingNumber K a (2 * b - a) z =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ((∫ t in a..b, deriv γ t / (γ t - z)) - ∫ t in a..b, deriv η t / (η t - z)) := by
    rw [windingNumber_eq_integral_of_avoidance hK.continuousOn hKoff
      (intervalIntegrable_inv_sub_mul_deriv hK.continuousOn hKoff hK.intervalIntegrable_deriv)]
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      congrArg (fun w : ℂ ↦ (2 * (Real.pi : ℂ) * I)⁻¹ * w) hsplit
  rw [hnormalized, hγint, hηint, ha, hb, if_neg (not_lt_of_ge hzη.le)]
  split_ifs with hin
  · have hval : log (η b - z) - log (-(η a - z)) + -(Real.pi : ℂ) * I -
        (log (η b - z) - log (-(η a - z)) + (Real.pi : ℂ) * I) =
        (2 * (Real.pi : ℂ) * I) * (-1) := by ring
    rw [hval, inv_mul_cancel_left₀ Complex.two_pi_I_ne_zero]
  · simp

#print axioms windingNumber_graph_difference

end MaxModulusPoints.CauchyApproximation
