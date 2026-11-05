module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.StripCoordinates
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# Orientation and growth of real strip coordinates

The positive derivative normalization fixes the orientation of the real axis.
Together with the tunnel crosscut estimate, this makes the clean reference
coordinate and its logarithmic conformal value uniformly large as the tunnel
height decreases; Pardo-Simón–Sixsmith, Proposition 4.1.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set

noncomputable section

/-- A positive derivative at one interior point selects the increasing
orientation of a continuous injective real function on a closed interval. -/
theorem strictMonoOn_Icc_of_positive_derivative {f : ℝ → ℝ} {a b x d : ℝ}
    (hx : a < x ∧ x < b) (hcont : ContinuousOn f (Icc a b))
    (hinj : InjOn f (Icc a b)) (hd : HasDerivAt f d x) (hpos : 0 < d) :
    StrictMonoOn f (Icc a b) := by
  rcases hcont.strictMonoOn_of_injOn_Icc' (le_of_lt (hx.1.trans hx.2)) hinj with hm | ha
  · exact hm
  · have hnonpos := ha.antitoneOn.derivWithin_nonpos (x := x)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2), hd.deriv] at hnonpos
    exact False.elim (hpos.not_ge hnonpos)

/-- A real-valued conformal equivalence has increasing real restriction when
its domain contains the real half-line and its derivative at -1 is positive. -/
theorem conformal_real_strictMonoOn {U W : Set ℂ}
    (F : Blueprint.ConformalEquivalence U W) (hU : IsOpen U)
    (haxis : ∀ x : ℝ, -2 < x → (x : ℂ) ∈ U)
    (hreal : ∀ x : ℝ, -2 < x → (F.toFun x).im = 0)
    (hpositive : 0 < (deriv F.toFun (-1)).re) :
    StrictMonoOn (fun x : ℝ => (F.toFun x).re) (Ioi (-2)) := by
  intro a ha b hb hab
  let l := min a (-3 / 2)
  let u := max b 0
  have hl : -2 < l := lt_min ha (by norm_num)
  have hlbase : l < -1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hubase : -1 < u := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have haxisI (x : ℝ) (hx : x ∈ Icc l u) : (x : ℂ) ∈ U :=
    haxis x (hl.trans_le hx.1)
  have hcont : ContinuousOn (fun x : ℝ => (F.toFun x).re) (Icc l u) := by
    intro x hx
    exact (Complex.continuous_re.continuousAt.comp
      (((F.holomorphic x (haxisI x hx)).differentiableAt
        (hU.mem_nhds (haxisI x hx))).continuousAt.comp
          Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hinj : InjOn (fun x : ℝ => (F.toFun x).re) (Icc l u) := by
    intro s hs t ht hst
    have hfull : F.toFun s = F.toFun t :=
      Complex.ext hst ((hreal s (hl.trans_le hs.1)).trans (hreal t (hl.trans_le ht.1)).symm)
    have heq := congrArg F.invFun hfull
    rw [F.left_inv s (haxisI s hs), F.left_inv t (haxisI t ht)] at heq
    exact Complex.ofReal_injective heq
  have hbase : (-1 : ℂ) ∈ U := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using haxis (-1) (by norm_num)
  have hdiff : HasDerivAt F.toFun (deriv F.toFun (-1)) ((-1 : ℝ) : ℂ) := by
    simpa using ((F.holomorphic (-1) hbase).differentiableAt (hU.mem_nhds hbase)).hasDerivAt
  have hmono := strictMonoOn_Icc_of_positive_derivative ⟨hlbase, hubase⟩ hcont hinj
    hdiff.real_of_complex hpositive
  apply hmono ?_ ?_ hab
  · exact ⟨min_le_left _ _, hab.le.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_left _ _).trans hab.le, le_max_left _ _⟩

theorem stripCoordinates_strictMonoOn_real (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) :
    StrictMonoOn (fun x : ℝ => ((stripCoordinates ψ G).toFun x).re) (Ioi (-2)) := by
  apply conformal_real_strictMonoOn (stripCoordinates ψ G) G.open_domain
    (fun x hx => real_mem_tract p δ hx)
    (fun x hx => stripCoordinates_real ψ G (real_mem_tract p δ hx))
  exact (stripCoordinates_normalized ψ G).2.1

theorem stripCoordinates_pos (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) {x : ℝ} (hx : -1 < x) :
    0 < ((stripCoordinates ψ G).toFun x).re := by
  have h := stripCoordinates_strictMonoOn_real ψ p δ G
    (show (-1 : ℝ) ∈ Ioi (-2) by norm_num)
    (show x ∈ Ioi (-2) by change -2 < x; linarith) hx
  simpa only [Complex.ofReal_neg, Complex.ofReal_one,
    (stripCoordinates_normalized ψ G).1, Complex.zero_re] using h

/-- The clean reference coordinate exceeds every lower bound enforced by the
tunnel, uniformly over all other gates and all later block parameters. -/
theorem clean_reference_strip_gt_separation (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) (n : ℕ) {D : ℝ}
    (hheight : D ≤ 1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi) :
    D < ((stripCoordinates ψ G).toFun
      (Blueprint.blockPosition p n + 3 / 2 : ℝ)).re := by
  have hbase : 0 ≤ Blueprint.blockPosition p n := (blockParametersLayout p).base_nonneg n
  have hbasePos : 0 < Blueprint.chamberBase := passageHalfHeight_pos
  have hpass : ((Blueprint.slicePosition p n : ℝ) : ℂ) ∈ Blueprint.passageSlice p n :=
    ⟨rfl, by simpa using hbasePos⟩
  have hclean : ((Blueprint.blockPosition p n + 3 / 2 : ℝ) : ℂ) ∈
      Blueprint.cleanSlice p n := ⟨rfl, by simpa using Real.pi_div_two_pos⟩
  obtain ⟨hzero, hpos, him⟩ := stripCoordinates_normalized ψ G
  have hsep := hbottleneck p δ hδ (stripCoordinates ψ G) hzero hpos him n
    _ hclean _ hpass
  have hpasspos := stripCoordinates_pos ψ p δ G
    (show -1 < Blueprint.slicePosition p n by
      dsimp [Blueprint.slicePosition]
      linarith)
  linarith

/-- The clean logarithmic conformal value has the exponential lower bound
required when choosing the open-gate tunnel heights. -/
theorem clean_reference_value_lower (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) (n : ℕ) {D : ℝ}
    (hD : 0 ≤ D)
    (hheight : D ≤ 1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi) :
    Real.exp (ψ.lowerRate * D) ≤
      (G.toFun (Blueprint.blockPosition p n + 3 / 2 : ℝ)).re := by
  let x := Blueprint.blockPosition p n + 3 / 2
  let φ := stripCoordinates ψ G
  let b := (φ.toFun (x : ℂ)).re
  have hDb : D < b := clean_reference_strip_gt_separation hbottleneck ψ p δ hδ G n hheight
  have hb : 0 ≤ b := hD.trans hDb.le
  have hgrowth := (ψ.growth 0 b hb).1
  simp only [zero_add, Complex.ofReal_zero, ψ.base_value, Complex.one_re, mul_one] at hgrowth
  have hxbase : 0 ≤ Blueprint.blockPosition p n := (blockParametersLayout p).base_nonneg n
  have hxV : (x : ℂ) ∈ Blueprint.tract p δ := real_mem_tract p δ (by dsimp [x]; linarith)
  have hxreal : φ.toFun (x : ℂ) = (b : ℂ) := by
    apply Complex.ext
    · rfl
    · exact stripCoordinates_real ψ G hxV
  have hidentify : ψ.toFun (b : ℂ) = G.toFun (x : ℂ) := by
    rw [← hxreal]
    exact ψ.right_inv _ (G.mapsTo hxV)
  change Real.exp (ψ.lowerRate * D) ≤ (G.toFun (x : ℂ)).re
  rw [hidentify] at hgrowth
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hDb.le ψ.lowerRate_pos.le)).trans hgrowth

#print axioms conformal_real_strictMonoOn
#print axioms stripCoordinates_pos
#print axioms clean_reference_strip_gt_separation
#print axioms clean_reference_value_lower

end

end MaxModulusPoints.Construction
