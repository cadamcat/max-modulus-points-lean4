module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CauchyApproximation.CanonicalApproximation
public import MaxModulusPoints.CauchyApproximation.GlobalCoreBounds
public import MaxModulusPoints.CauchyApproximation.Model
public import MaxModulusPoints.CauchyApproximation.RealSymmetry
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.TractGeometry.StripContainment

/-!
# Non-monomiality of the canonical entire approximation

The conformal exponential grows on inverse images of the positive real
axis, so its canonical approximation is nonzero. If the tract lies in the
right half-plane, decay on the negative real axis excludes every nonzero
monomial.
-/


@[expose] public section

open Complex Filter Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- Core approximation and inverse escape imply that the canonical entire
function is not identically zero. -/
theorem NormalizedModel.canonicalEntire_ne_zero (m : NormalizedModel) :
    m.canonicalEntire ≠ 0 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_core_approximation_bound
  let w : ℕ → ℂ := fun n => (n : ℂ) + 2
  have hw (n : ℕ) : w n ∈ modelHalfPlane := by
    simp [w, modelHalfPlane]
    positivity
  have hnorm (n : ℕ) : ‖w n‖ = (n : ℝ) + 2 := by
    have heq : w n = (((n : ℝ) + 2 : ℝ) : ℂ) := by simp [w]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht : Tendsto (fun n => ‖w n‖) atTop atTop := by
    simp_rw [hnorm]
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  obtain ⟨n, hn, hnexp⟩ := ((m.inverse_infinity w hw ht).eventually
    (eventually_gt_atTop 1) |>.and (hexp.eventually (eventually_gt_atTop C))).exists
  have hz : m.inverse (w n) ∈ m.core := by
    refine ⟨m.inverse_mem (hw n), ?_⟩
    rw [m.right_inverse _ (hw n)]
    simp [w]
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hg : ‖m.modelFunction (m.inverse (w n))‖ = Real.exp ((n : ℝ) + 2) := by
    rw [NormalizedModel.modelFunction, m.right_inverse _ (hw n), Complex.norm_exp]
    simp [w]
  intro hf
  have hb := (hbound m (m.inverse (w n)) (by linarith : 0 < ‖m.inverse (w n)‖)).1 hz
  rw [hf] at hb
  simp only [Pi.zero_apply, zero_sub, norm_neg, hg] at hb
  have hquot : C / ‖m.inverse (w n)‖ ≤ C :=
    (div_le_self hC.le hn.le)
  exact (not_lt_of_ge (hb.trans hquot)) hnexp

/-- Exterior decay along the negative real ray rules out a monomial when
the original tract lies in the right half-plane. -/
theorem NormalizedModel.canonicalEntire_not_monomial (m : NormalizedModel)
    (hT : ∀ z ∈ m.domain, 0 < z.re) : ¬ MaxModulusPoints.IsMonomial m.canonicalEntire := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_exterior_bound
  rintro ⟨c, n, hf⟩
  have hc : c ≠ 0 := by
    intro hc
    apply m.canonicalEntire_ne_zero
    funext z
    simpa [hc] using congrFun hf z
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let R : ℝ := max 2 ((C + 1) / ‖c‖)
  have hR : 1 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hz : -((R : ℝ) : ℂ) ∉ m.domain := by
    intro hz
    have hh := hT _ hz
    simp only [neg_re, ofReal_re] at hh
    linarith
  have hnorm : ‖-((R : ℝ) : ℂ)‖ = R := by
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
  have hb := hbound m _ hz (by simpa only [hnorm] using hRpos)
  rw [hf] at hb
  simp only [norm_mul, norm_pow, hnorm] at hb
  have hp : 1 ≤ R ^ n := one_le_pow₀ hR.le
  have hsmall : ‖c‖ ≤ C / R := by nlinarith
  have hprod : ‖c‖ * R ≤ C := (le_div_iff₀ hRpos).mp hsmall
  have hlarge : C + 1 ≤ ‖c‖ * R := by
    have hh := (div_le_iff₀ hcn).mp (le_max_right 2 ((C + 1) / ‖c‖))
    simpa only [R, mul_comm] using hh
  linarith

/-- Exponentials of the chamber and gate tracts lie in the right half-plane. -/
theorem tract_exp_re_pos (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i) {z : ℂ}
    (hz : z ∈ Complex.exp '' Blueprint.tract p δ) : 0 < z.re := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  exact Real.cos_pos_of_mem_Ioo (abs_lt.mp (TractGeometry.tract_im_lt p δ hδ hw))

#print axioms NormalizedModel.canonicalEntire_ne_zero
#print axioms NormalizedModel.canonicalEntire_not_monomial
#print axioms tract_exp_re_pos

end MaxModulusPoints.CauchyApproximation
