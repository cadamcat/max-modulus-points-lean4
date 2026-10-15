import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.StripMapData
import MaxModulusPoints.Construction.PassageCut
import MaxModulusPoints.Construction.RealOrientation
import MaxModulusPoints.Construction.StripClearance
import MaxModulusPoints.Construction.StripCoordinates
import MaxModulusPoints.Construction.Tract
import MaxModulusPoints.Construction.TractMembership
/-!
# A uniform positive witness on each passage slice

The passage lower bound in Pardo-Simón–Sixsmith, Proposition 4.3,
follows quantitatively from the fixed height of the ambient strip.
An omitted boundary value bounds the inverse strip-coordinate derivative;
the mean-value estimate and strip growth then give a positive real witness.
-/

namespace MaxModulusPoints.Construction

open Set Metric
open scoped Topology

noncomputable section

/-- A fixed radius about any real point fits inside the height-one strip. -/
theorem real_ball_quarter_subset_strip (b : ℝ) :
    ball (b : ℂ) (1 / 4) ⊆ Blueprint.strip := by
  intro z hz
  have hn : ‖z - (b : ℂ)‖ < 1 / 4 := by simpa only [mem_ball, dist_eq_norm] using hz
  have hi := (Complex.abs_im_le_norm (z - (b : ℂ))).trans_lt hn
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  change |z.im| < 1 / 2
  linarith

/-- Only the image strip height enters this derivative bound. -/
theorem inverse_strip_derivative_bound {V : Set ℂ}
    (φ : Blueprint.ConformalEquivalence V Blueprint.strip)
    (hV : ∀ z ∈ V, |z.im| < Real.pi / 2) (b : ℝ) :
    ‖deriv φ.invFun (b : ℂ)‖ ≤ 512 * Real.pi ^ 2 := by
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hball := real_ball_quarter_subset_strip b
  have hd := φ.inverse_holomorphic.mono hball
  have hi : InjOn φ.invFun (ball (b : ℂ) (1 / 4)) := by
    intro z hz w hw he
    have h := congrArg φ.toFun he
    rwa [φ.right_inv z (hball hz), φ.right_inv w (hball hw)] at h
  let a : ℂ := ((φ.invFun b).re : ℂ) + (Real.pi / 2 : ℝ) * Complex.I
  have haim : a.im = Real.pi / 2 := by simp [a]
  have hnot : a ∉ φ.invFun '' ball (b : ℂ) (1 / 4) := by
    rintro ⟨z, hz, he⟩
    have h := hV _ (φ.inverse_mapsTo (hball hz))
    rw [he, haim, abs_of_pos Real.pi_div_two_pos] at h
    exact lt_irrefl _ h
  have hdiff : φ.invFun b - a = (((φ.invFun b).im - Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [a]
  have hnorm : ‖φ.invFun b - a‖ ≤ Real.pi := by
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    have hb := abs_lt.mp (hV _ (φ.inverse_mapsTo (real_mem_strip b)))
    rw [abs_of_neg (by linarith : (φ.invFun b).im - Real.pi / 2 < 0)]
    linarith [hb.1]
  have h := OAI.SLEExactGauge.univalent_omitted_value_bound_ball hr hd hi a hnot
  have hm := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 128 * Real.pi)
  nlinarith

/-- The inverse coordinate is uniformly Lipschitz along the real axis. -/
theorem inverse_strip_real_lipschitz {V : Set ℂ}
    (φ : Blueprint.ConformalEquivalence V Blueprint.strip)
    (hV : ∀ z ∈ V, |z.im| < Real.pi / 2) {b : ℝ} (hb : 0 ≤ b) :
    ‖φ.invFun (b : ℂ) - φ.invFun 0‖ ≤ (512 * Real.pi ^ 2) * b := by
  have hder (t : ℝ) : HasDerivAt (fun s : ℝ => φ.invFun (s : ℂ))
      (deriv φ.invFun (t : ℂ)) t :=
    ((φ.inverse_holomorphic t (real_mem_strip t)).differentiableAt
      (strip_isOpen.mem_nhds (real_mem_strip t))).hasDerivAt.comp_ofReal
  have hLip : LipschitzOnWith ⟨512 * Real.pi ^ 2, by positivity⟩
      (fun s : ℝ => φ.invFun (s : ℂ)) (Icc 0 b) :=
    (convex_Icc (0 : ℝ) b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t _ => (hder t).hasDerivWithinAt)
      (fun t _ => inverse_strip_derivative_bound φ hV t)
  have h := hLip.dist_le_mul b ⟨hb, le_rfl⟩ 0 ⟨le_rfl, hb⟩
  rw [dist_eq_norm, Complex.ofReal_zero] at h
  change ‖φ.invFun (b : ℂ) - φ.invFun 0‖ ≤ (512 * Real.pi ^ 2) * dist b 0 at h
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hb] using h

/-- A linear lower bound for the real strip coordinate, uniform over all
admissible tracts and logarithmic maps. -/
theorem stripCoordinates_real_lower (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) {x : ℝ} (hx : -1 < x) :
    (x + 1) / (512 * Real.pi ^ 2) ≤ ((stripCoordinates ψ G).toFun x).re := by
  let φ := stripCoordinates ψ G
  let b := (φ.toFun x).re
  have hxV : (x : ℂ) ∈ Blueprint.tract p δ := real_mem_tract p δ (by linarith)
  have hb : 0 ≤ b := (stripCoordinates_pos ψ p δ G hx).le
  have hreal : φ.toFun x = (b : ℂ) := by
    apply Complex.ext
    · rfl
    · exact stripCoordinates_real ψ G hxV
  have hzero : φ.invFun 0 = -1 := by
    rw [← (stripCoordinates_normalized ψ G).1]
    exact φ.left_inv _ G.base_mem
  have h := inverse_strip_real_lipschitz φ
    (fun z hz => (tract_subset_ambient p δ hδ hz).2) hb
  rw [hzero, ← hreal, φ.left_inv _ hxV] at h
  have hnorm : ‖(x : ℂ) - (-1)‖ = x + 1 := by
    rw [show (x : ℂ) - (-1) = ((x + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hnorm] at h
  exact (div_le_iff₀ (by positivity : 0 < 512 * Real.pi ^ 2)).mpr (by simpa only [mul_comm] using h)

theorem real_logModel_value_lower (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) {x : ℝ} (hx : -1 < x) :
    Real.exp (ψ.lowerRate * ((x + 1) / (512 * Real.pi ^ 2))) ≤ (G.toFun x).re := by
  let φ := stripCoordinates ψ G
  let b := (φ.toFun x).re
  have hxV : (x : ℂ) ∈ Blueprint.tract p δ := real_mem_tract p δ (by linarith)
  have hb : 0 ≤ b := (stripCoordinates_pos ψ p δ G hx).le
  have hreal : φ.toFun x = (b : ℂ) := by
    apply Complex.ext
    · rfl
    · exact stripCoordinates_real ψ G hxV
  have hid : ψ.toFun (b : ℂ) = G.toFun x := by
    rw [← hreal]
    exact ψ.right_inv _ (G.mapsTo hxV)
  have h := (ψ.growth 0 b hb).1
  simp only [zero_add, Complex.ofReal_zero, ψ.base_value, Complex.one_re, mul_one] at h
  rw [hid] at h
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (stripCoordinates_real_lower ψ p δ hδ G hx) ψ.lowerRate_pos.le)).trans h

/-- Enlarging the initial gap gives an arbitrarily large passage witness,
simultaneously for every block, every gate function and every conformal map. -/
theorem exists_initial_gap_for_passage_lower (ψ : Blueprint.StripMapData) (A : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p : Blueprint.BlockParameters, R ≤ p.gap 0 →
      ∀ δ : Blueprint.GateIndex → ℝ, (∀ i, δ i ≤ Blueprint.gateUpper i) →
      ∀ G : Blueprint.LogModel (Blueprint.tract p δ), ∀ n : ℕ,
        A ≤ (G.toFun (Blueprint.slicePosition p n : ℝ)).re := by
  let C : ℝ := 512 * Real.pi ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  let T := C * (|A| + 1) / ψ.lowerRate
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro p hp δ hδ G n
  have hbase := (blockParametersLayout p).monotone_base (Nat.zero_le n)
  change Blueprint.blockPosition p 0 ≤ Blueprint.blockPosition p n at hbase
  have hbase0 : Blueprint.blockPosition p 0 = p.gap 0 := by simp [Blueprint.blockPosition]
  rw [hbase0] at hbase
  have hx : T ≤ Blueprint.slicePosition p n := by
    dsimp [Blueprint.slicePosition]
    linarith [(le_max_right (1 : ℝ) T).trans hp]
  have hxpos : -1 < Blueprint.slicePosition p n := by
    dsimp [Blueprint.slicePosition]
    linarith [(le_max_left (1 : ℝ) T).trans hp]
  have hmul : |A| + 1 ≤ ψ.lowerRate * ((Blueprint.slicePosition p n + 1) / C) := by
    have hT := (div_le_iff₀ ψ.lowerRate_pos).mp hx
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hC).mpr
    nlinarith [ψ.lowerRate_pos]
  have hlarge : A ≤ Real.exp (ψ.lowerRate * ((Blueprint.slicePosition p n + 1) / C)) := by
    linarith [le_abs_self A, Real.add_one_le_exp
      (ψ.lowerRate * ((Blueprint.slicePosition p n + 1) / C))]
  exact hlarge.trans (real_logModel_value_lower ψ p δ hδ G hxpos)

#print axioms inverse_strip_derivative_bound
#print axioms stripCoordinates_real_lower
#print axioms real_logModel_value_lower
#print axioms exists_initial_gap_for_passage_lower

end

end MaxModulusPoints.Construction
