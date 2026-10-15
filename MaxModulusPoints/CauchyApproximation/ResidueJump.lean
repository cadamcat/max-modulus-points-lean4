import TauCeti.Analysis.Contour.Curve.Concat
import TauCeti.Analysis.Contour.HomologyCauchy
import TauCeti.Analysis.Contour.Dixon.FunctionDiff
import MaxModulusPoints.CauchyApproximation.ContourModification
import MaxModulusPoints.CauchyApproximation.ImproperIntegral
/-!
# The residue of a compact contour modification

Following one arc and then the other backwards makes the finite closed
contour whose Cauchy integral measures the change in the improper integral.
The homology Cauchy formula identifies that change with the winding-number
multiple of the holomorphic function.
-/

open Complex Filter MeasureTheory Set
open TauCeti.Contour
open scoped Topology Real Interval

namespace MaxModulusPoints.CauchyApproximation

/-- Follow the first arc up to `b`, then follow the second arc backwards.
The parameter interval for the closed contour is `[a, 2*b-a]`. -/
noncomputable def closedContourDifference (γ η : ℝ → ℂ) (b t : ℝ) : ℂ :=
  if t ≤ b then γ t else η (2 * b - t)

/-- The residue identity for a compact modification, with the winding number
of the finite closed contour left explicit. -/
theorem cauchyIntegral_sub_eq_winding_mul {γ η : ℝ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hγ : IsProperMap γ) (hη : IsProperMap η)
    (hργ : Integrable (fun t : ℝ ↦ g (γ t) * deriv γ t))
    (hρη : Integrable (fun t : ℝ ↦ g (η t) * deriv η t))
    {a b : ℝ} (hab : a ≤ b) (hγpc : IsPiecewiseC1On γ a b)
    (hηpc : IsPiecewiseC1On η a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hηU : ∀ t ∈ uIcc a b, η t ∈ U)
    (hagree : ∀ t ∉ Ioo a b, γ t = η t)
    (hnull : IsNullHomologous (closedContourDifference γ η b) a (2 * b - a) U)
    {z : ℂ} (hzU : z ∈ U) (hzγ : z ∉ range γ) (hzη : z ∉ range η) :
    cauchyIntegral γ (fun t ↦ g (γ t) * deriv γ t) z -
        cauchyIntegral η (fun t ↦ g (η t) * deriv η t) z =
      windingNumber (closedContourDifference γ η b) a (2 * b - a) z * g z := by
  let ηrev : ℝ → ℂ := fun t ↦ η (2 * b - t)
  let K : ℂ → ℂ := fun w ↦ g w / (w - z)
  have hbb : 2 * b - b = b := by ring
  have haa : 2 * b - (2 * b - a) = a := by ring
  have hbc : b ≤ 2 * b - a := by linarith
  have hac : a ≤ 2 * b - a := hab.trans hbc
  have hb : γ b = ηrev b := by
    simpa only [ηrev, hbb] using hagree b (by simp)
  have hrev : IsPiecewiseC1On ηrev b (2 * b - a) := by
    simpa only [hbb] using (hηpc.comp_const_sub (2 * b)).symm
  have hloop : IsPiecewiseC1On (closedContourDifference γ η b) a (2 * b - a) :=
    hγpc.if_le hrev hab hbc hb
  have hrevU (t : ℝ) (ht : t ∈ uIcc b (2 * b - a)) : ηrev t ∈ U := by
    rw [uIcc_of_le hbc] at ht
    apply hηU (2 * b - t)
    rw [uIcc_of_le hab]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hloopγ : EqOn (closedContourDifference γ η b) γ (uIoo a b) := by
    intro t ht
    rw [uIoo_of_le hab] at ht
    simp only [closedContourDifference, if_pos ht.2.le]
  have hlooprev : EqOn (closedContourDifference γ η b) ηrev
      (uIoo b (2 * b - a)) := by
    intro t ht
    rw [uIoo_of_le hbc] at ht
    simp only [closedContourDifference, if_neg (not_le.mpr ht.1), ηrev]
  have hlooprev_closed : EqOn (closedContourDifference γ η b) ηrev
      (Icc b (2 * b - a)) := by
    intro t ht
    by_cases htb : t ≤ b
    · have heq : t = b := le_antisymm htb ht.1
      subst t
      simpa only [closedContourDifference, if_pos le_rfl] using hb
    · simp only [closedContourDifference, if_neg htb, ηrev]
  have hclosed : closedContourDifference γ η b a =
      closedContourDifference γ η b (2 * b - a) := by
    calc
      closedContourDifference γ η b a = γ a := by
        simp only [closedContourDifference, if_pos hab]
      _ = η a := hagree a (by simp)
      _ = ηrev (2 * b - a) := by simp only [ηrev, haa]
      _ = closedContourDifference γ η b (2 * b - a) :=
        (hlooprev_closed ⟨hbc, le_rfl⟩).symm
  have hloopU (t : ℝ) (ht : t ∈ uIcc a (2 * b - a)) :
      closedContourDifference γ η b t ∈ U := by
    rw [uIcc_of_le hac] at ht
    by_cases htb : t ≤ b
    · simp only [closedContourDifference, if_pos htb]
      exact hγU t (by rw [uIcc_of_le hab]; exact ⟨ht.1, htb⟩)
    · rw [hlooprev_closed ⟨(not_le.mp htb).le, ht.2⟩]
      exact hrevU t (by rw [uIcc_of_le hbc]; exact ⟨(not_le.mp htb).le, ht.2⟩)
  have hoffγ (t : ℝ) (_ht : t ∈ uIcc a b) : γ t ≠ z := fun h ↦ hzγ ⟨t, h⟩
  have hoffη (t : ℝ) (_ht : t ∈ uIcc a b) : η t ≠ z := fun h ↦ hzη ⟨t, h⟩
  have hoffrev (t : ℝ) (_ht : t ∈ uIcc b (2 * b - a)) : ηrev t ≠ z :=
    fun h ↦ hzη ⟨2 * b - t, h⟩
  have hoffloop (t : ℝ) (_ht : t ∈ uIcc a (2 * b - a)) :
      closedContourDifference γ η b t ≠ z := by
    by_cases htb : t ≤ b
    · simpa only [closedContourDifference, if_pos htb] using (fun h ↦ hzγ ⟨t, h⟩)
    · simpa only [closedContourDifference, if_neg htb] using
        (fun h ↦ hzη ⟨2 * b - t, h⟩)
  have hint {θ : ℝ → ℂ} {c d : ℝ} (hθ : IsPiecewiseC1On θ c d)
      (hθU : ∀ t ∈ uIcc c d, θ t ∈ U) (hoff : ∀ t ∈ uIcc c d, θ t ≠ z) :
      IntervalIntegrable (fun t ↦ deriv θ t • K (θ t)) volume c d := by
    convert! cauchy_integrand_intervalIntegrable hg.continuousOn hθ.continuousOn
      hθU hθ.intervalIntegrable_deriv hoff using 1
    funext t
    simp only [K, smul_eq_mul, mul_comm]
  have hγi := hint hγpc hγU hoffγ
  have hηi := hint hηpc hηU hoffη
  have hrevi := hint hrev hrevU hoffrev
  have hsplit := intervalIntegral_deriv_smul_eq_add_of_eqOn hloopγ hlooprev hγi hrevi
  have hreverse : (∫ t in b..(2 * b - a), deriv ηrev t • K (ηrev t)) =
      -(∫ t in a..b, deriv η t • K (η t)) := by
    calc
      (∫ t in b..(2 * b - a), deriv ηrev t • K (ηrev t)) =
          ∫ t in b..a, deriv η t • K (η t) := by
        simpa only [hbb, haa] using
          intervalIntegral_deriv_smul_comp_const_sub η K b (2 * b - a) (2 * b)
      _ = -(∫ t in a..b, deriv η t • K (η t)) := intervalIntegral.integral_symm _ _
  rw [hreverse, ← sub_eq_add_neg] at hsplit
  have hfinite : (∫ t in a..b,
      g (γ t) * deriv γ t / (γ t - z) - g (η t) * deriv η t / (η t - z)) =
      ∫ t in a..(2 * b - a), deriv (closedContourDifference γ η b) t •
        K (closedContourDifference γ η b t) := by
    calc
      _ = ∫ t in a..b, deriv γ t • K (γ t) - deriv η t • K (η t) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp only [K]
        simp only [smul_eq_mul]
        ring
      _ = (∫ t in a..b, deriv γ t • K (γ t)) - ∫ t in a..b, deriv η t • K (η t) :=
        intervalIntegral.integral_sub hγi hηi
      _ = _ := hsplit.symm
  obtain ⟨P, hP, hdiff⟩ := hloop.exists_countable_differentiableAt
  have hres_raw := dixonH2_eq_windingNumber_mul_f_of_nullHomologous
    hU hg hloop.continuousOn hloopU hloop.intervalIntegrable_deriv hclosed hP hdiff
    hnull hzU hoffloop
  have hres : (∫ t in a..(2 * b - a), deriv (closedContourDifference γ η b) t •
      K (closedContourDifference γ η b t)) =
      2 * (Real.pi : ℂ) * I *
        windingNumber (closedContourDifference γ η b) a (2 * b - a) z * g z := by
    calc
      _ = dixonH2 g (closedContourDifference γ η b) a (2 * b - a) z := by
        rw [dixonH2_def]
        apply intervalIntegral.integral_congr
        intro t _ht
        simp only [K, smul_eq_mul, mul_comm]
      _ = _ := hres_raw
  rw [cauchyIntegral_sub_of_compact_modification hγ hη hργ hρη hab
    (fun t ht ↦ hagree t (fun h ↦ ht ⟨h.1.le, h.2.le⟩)) hzγ hzη, hfinite, hres]
  have hk : 2 * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  calc
    _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
        ((2 * (Real.pi : ℂ) * I) *
          (windingNumber (closedContourDifference γ η b) a (2 * b - a) z * g z)) := by ring
    _ = _ := inv_mul_cancel_left₀ hk _

#print axioms cauchyIntegral_sub_eq_winding_mul

end MaxModulusPoints.CauchyApproximation
