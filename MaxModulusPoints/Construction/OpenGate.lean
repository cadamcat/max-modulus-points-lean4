import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
import MaxModulusPoints.Blueprint.Interfaces.StripMapData
/-!
# Quantitative estimates for open gates

Pardo-Simón–Sixsmith, Proposition 4.1, first uses the tunnel crosscut
separation to suppress the passage values. The rescaled strip map then
gives a uniform lower bound on compact sets of translated strip coordinates.
The final strict comparison survives the uniform approximation error.
-/

namespace MaxModulusPoints.Construction

open Set Filter
open scoped Topology

noncomputable section

/-- Strip growth converts horizontal separation into exponential suppression;
this is the pointwise form of equation (4.3). -/
theorem strip_decay_from_separation (ψ : Blueprint.StripMapData)
    {u : ℂ} {b D : ℝ} (hu : u ∈ Blueprint.strip)
    (hD : 0 ≤ D) (hsep : D ≤ b - u.re) :
    (ψ.toFun u).re ≤ Real.exp (-ψ.lowerRate * D) * (ψ.toFun b).re := by
  have hvertical : (ψ.toFun u).re ≤ (ψ.toFun (u.re : ℂ)).re := by
    simpa only [Complex.re_add_im] using ψ.vertical_maximum u.re u.im hu
  have hgrowth := (ψ.growth u.re (b - u.re) (by linarith)).1
  rw [show u.re + (b - u.re) = b by ring] at hgrowth
  have hexp : Real.exp (ψ.lowerRate * D) ≤
      Real.exp (ψ.lowerRate * (b - u.re)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsep ψ.lowerRate_pos.le)
  have hproduct : Real.exp (ψ.lowerRate * D) * (ψ.toFun u).re ≤
      (ψ.toFun b).re :=
    (mul_le_mul_of_nonneg_left hvertical (Real.exp_pos _).le).trans
      ((mul_le_mul_of_nonneg_right hexp (ψ.positive_real u.re).1.le).trans hgrowth)
  calc
    (ψ.toFun u).re ≤ (ψ.toFun b).re / Real.exp (ψ.lowerRate * D) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa [mul_comm] using hproduct)
    _ = Real.exp (-ψ.lowerRate * D) * (ψ.toFun b).re := by
      rw [neg_mul, Real.exp_neg, div_eq_mul_inv, mul_comm]

/-- The frozen bottleneck estimate gives the passage bound simultaneously for
all admissible gate parameters. Membership in the tract is displayed because
the conformal equivalence has no prescribed values outside its domain. -/
theorem bottleneck_passage_bound (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i)
    (φ : Blueprint.ConformalEquivalence (Blueprint.tract p δ) Blueprint.strip)
    (hbase : φ.toFun (-1) = 0) (hpositive : 0 < (deriv φ.toFun (-1)).re)
    (hreal : (deriv φ.toFun (-1)).im = 0)
    {n : ℕ} {z w : ℂ} (hz : z ∈ Blueprint.cleanSlice p n)
    (hw : w ∈ Blueprint.passageSlice p n) (hwV : w ∈ Blueprint.tract p δ)
    {D : ℝ} (hD : 0 ≤ D)
    (hheight : D ≤ 1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi) :
    (ψ.toFun (φ.toFun w)).re ≤
      Real.exp (-ψ.lowerRate * D) * (ψ.toFun ((φ.toFun z).re : ℂ)).re := by
  apply strip_decay_from_separation ψ (φ.mapsTo hwV) hD
  exact hheight.trans (hbottleneck p δ hδ φ hbase hpositive hreal n z hz w hw)

/-- A positive tunnel height at most one quarter can enforce any prescribed
crosscut separation. This choice depends on the desired separation only. -/
theorem exists_tunnelHeight_separation (D : ℝ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 4 ∧
      D ≤ 1 / (2 * t) - Real.log 32 / Real.pi := by
  let C := Real.log 32 / Real.pi
  let A := |D| + |C| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg D, abs_nonneg C]
  let t := 1 / (4 * A)
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨t, ht, ?_, ?_⟩
  · dsimp [t]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * A) (by norm_num)).mpr
    nlinarith
  · have hrecip : 1 / (2 * t) = 2 * A := by
      dsimp [t]
      field_simp
      norm_num
    rw [hrecip]
    change D ≤ 2 * A - C
    dsimp [A]
    linarith [le_abs_self D, le_abs_self C, abs_nonneg D, abs_nonneg C]

/-- The limiting exponential has positive real part throughout the strip. -/
theorem strip_limit_re_pos {z : ℂ} (hz : z ∈ Blueprint.strip) :
    0 < (Complex.exp ((Real.pi : ℂ) * z)).re := by
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  have hz' := abs_lt.mp (show |z.im| < 1 / 2 from hz)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  constructor <;> nlinarith [Real.pi_pos]

/-- The rescaled strip limit supplies one positive chamber proportion on any
fixed compact subset of the strip. Both constants are independent of the
translation and of the point in that compact set; Proposition 4.1, pp. 20–21. -/
theorem uniform_strip_translate_lower (ψ : Blueprint.StripMapData)
    {K : Set ℂ} (hK : IsCompact K) (hKstrip : K ⊆ Blueprint.strip) :
    ∃ c B : ℝ, 0 < c ∧ c < 1 ∧ 0 < B ∧ ∀ b : ℝ, B ≤ b →
      ∀ η ∈ K, c * (ψ.toFun b).re ≤ (ψ.toFun ((b : ℂ) + η)).re := by
  rcases K.eq_empty_or_nonempty with hEmpty | hne
  · refine ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    simp [hEmpty]
  have hcont : Continuous (fun z : ℂ => (Complex.exp ((Real.pi : ℂ) * z)).re) :=
    Complex.continuous_re.comp (Complex.continuous_exp.comp (continuous_const.mul continuous_id))
  obtain ⟨η₀, hη₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  let m := (Complex.exp ((Real.pi : ℂ) * η₀)).re
  have hm : 0 < m := strip_limit_re_pos (hKstrip hη₀)
  let c := min (1 / 2) (m / 2)
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hconv := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (ψ.rescaled_limit.mono hKstrip)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hconv) (m / 2) (by positivity))
  refine ⟨c, max 1 B₀, hc, hc1, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro b hb η hη
  have hdist := hB₀ b ((le_max_right _ _).trans hb) η hη
  have hclose : (Complex.exp ((Real.pi : ℂ) * η)).re -
      (ψ.toFun ((b : ℂ) + η) / ψ.toFun b).re < m / 2 := by
    have hbound := Complex.re_le_norm
      (Complex.exp ((Real.pi : ℂ) * η) - ψ.toFun ((b : ℂ) + η) / ψ.toFun b)
    rw [Complex.dist_eq] at hdist
    exact hbound.trans_lt hdist
  have hminimum : m ≤ (Complex.exp ((Real.pi : ℂ) * η)).re := hmin hη
  have hquotient : c ≤ (ψ.toFun ((b : ℂ) + η) / ψ.toFun b).re := by
    have hcm : c ≤ m / 2 := min_le_right _ _
    linarith
  have hbpos := (ψ.positive_real b).1
  have hbreal : ψ.toFun b = ((ψ.toFun b).re : ℂ) := by
    apply Complex.ext <;> simp [(ψ.positive_real b).2]
  rw [hbreal, Complex.div_ofReal_re] at hquotient
  exact (le_div_iff₀ hbpos).mp hquotient

/-- A strict model gap exceeding twice the approximation error gives a strict
comparison for the approximating function, as at the end of Proposition 4.1. -/
theorem approximation_preserves_strict_gap {f G : ℂ → ℂ} {z w : ℂ} {ε : ℝ}
    (hz : ‖f (Complex.exp z) - Complex.exp (G z)‖ ≤ ε)
    (hw : ‖f (Complex.exp w) - Complex.exp (G w)‖ ≤ ε)
    (hgap : Real.exp (G w).re + 2 * ε < Real.exp (G z).re) :
    ‖f (Complex.exp w)‖ < ‖f (Complex.exp z)‖ := by
  have hzw := (abs_norm_sub_norm_le (f (Complex.exp z)) (Complex.exp (G z))).trans hz
  have hww := (abs_norm_sub_norm_le (f (Complex.exp w)) (Complex.exp (G w))).trans hw
  rw [Complex.norm_exp] at hzw hww
  have hzbounds := abs_le.mp hzw
  have hwbounds := abs_le.mp hww
  linarith

#print axioms bottleneck_passage_bound
#print axioms exists_tunnelHeight_separation
#print axioms uniform_strip_translate_lower
#print axioms approximation_preserves_strict_gap

end

end MaxModulusPoints.Construction
