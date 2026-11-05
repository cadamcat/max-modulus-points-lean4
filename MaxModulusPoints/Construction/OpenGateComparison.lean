module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.Maxima
public import MaxModulusPoints.Construction.OpenChamberLocalization
public import MaxModulusPoints.Construction.OpenGate
public import MaxModulusPoints.Construction.RealOrientation
public import MaxModulusPoints.Construction.StripCoordinates
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# Uniform strict comparison at open gates

Pardo-Simón–Sixsmith, Proposition 4.1, chooses a tunnel height that
simultaneously suppresses the passage and raises the clean reference
value. The resulting chamber excess survives the approximation error,
uniformly over all the other gates and all later geometric choices.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set

noncomputable section

/-- An elementary exponential gap with a fixed positive margin. -/
theorem exp_double_gap {M a : ℝ} (hM : 0 ≤ M) (ha : 2 * M + 3 ≤ a) :
    Real.exp a + 2 * M + 1 < Real.exp (2 * a) := by
  have hq : 2 * M + 3 ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have hq2 : 2 ≤ Real.exp a := by linarith
  rw [show 2 * a = a + a by ring, Real.exp_add]
  nlinarith [mul_nonneg (Real.exp_pos a).le (sub_nonneg.mpr hq2)]

/-- One positive tunnel height enforces all three thresholds. Every smaller
positive height preserves the resulting lower bound on separation. -/
theorem exists_open_tunnel_thresholds {rate c M : ℝ} (hrate : 0 < rate)
    (hc : 0 < c) (hM : 0 ≤ M) (B : ℝ) :
    ∃ D t : ℝ, 0 ≤ D ∧ B ≤ D ∧ 0 < t ∧ t ≤ 1 / 4 ∧
      D ≤ 1 / (2 * t) - Real.log 32 / Real.pi ∧
      Real.exp (-rate * D) ≤ c / 2 ∧
      (4 * M + 6) / c ≤ Real.exp (rate * D) := by
  let L := (4 * M + 6) / c
  have hL : 0 < L := by dsimp [L]; positivity
  let D := max 0 (max B ((2 / c + L) / rate))
  have hD : 0 ≤ D := le_max_left _ _
  have hBD : B ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hRD : 2 / c + L ≤ rate * D := by
    have h := (le_max_right B ((2 / c + L) / rate)).trans (le_max_right 0 _)
    simpa only [mul_comm] using (div_le_iff₀ hrate).mp h
  have hE : 2 / c + L ≤ Real.exp (rate * D) := by
    linarith [Real.add_one_le_exp (rate * D)]
  have hdecay : Real.exp (-rate * D) ≤ c / 2 := by
    rw [neg_mul, Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos (rate * D))).mpr
    have hEc : 2 ≤ Real.exp (rate * D) * c :=
      (div_le_iff₀ hc).mp (by linarith : 2 / c ≤ Real.exp (rate * D))
    nlinarith
  obtain ⟨t, ht, htq, htD⟩ := exists_tunnelHeight_separation D
  exact ⟨D, t, hD, hBD, ht, htq, htD, hdecay, by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hc]⟩

theorem approximation_preserves_norm_margin {f G : ℂ → ℂ} {z w : ℂ} {M A : ℝ}
    (hz : ‖f (Complex.exp z) - Complex.exp (G z)‖ ≤ M)
    (hw : ‖f (Complex.exp w) - Complex.exp (G w)‖ ≤ M)
    (hgap : Real.exp (G w).re + 2 * M + A < Real.exp (G z).re) :
    ‖f (Complex.exp w)‖ + A < ‖f (Complex.exp z)‖ := by
  have hznorm := (abs_norm_sub_norm_le (f (Complex.exp z)) (Complex.exp (G z))).trans hz
  have hwnorm := (abs_norm_sub_norm_le (f (Complex.exp w)) (Complex.exp (G w))).trans hw
  rw [Complex.norm_exp] at hznorm hwnorm
  linarith [(abs_le.mp hznorm).1, (abs_le.mp hwnorm).2]

/-- On a positive sample line, the reciprocal approximation error is at
most the normalization-universal constant. -/
theorem approximation_error_on_sample (p : Blueprint.BlockParameters) (n : ℕ)
    {δ : Blueprint.GateIndex → ℝ} {G f : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (happrox : ∀ z ∈ Blueprint.tract p δ, 1 < ‖Complex.exp z‖ →
      ‖f (Complex.exp z) - Complex.exp (G z)‖ ≤ M / ‖Complex.exp z‖)
    {z : ℂ} (hz : z ∈ Blueprint.tract p δ) (hx : z.re = Blueprint.slicePosition p n) :
    ‖f (Complex.exp z) - Complex.exp (G z)‖ ≤ M := by
  have hbase := (blockParametersLayout p).base_nonneg n
  change 0 ≤ Blueprint.blockPosition p n at hbase
  have hpos : 0 < Blueprint.slicePosition p n := by dsimp [Blueprint.slicePosition]; linarith
  have he : 1 < ‖Complex.exp z‖ := by
    rw [Complex.norm_exp, hx]
    exact Real.one_lt_exp_iff.mpr hpos
  apply (happrox z hz he).trans
  exact (div_le_iff₀ (by linarith : 0 < ‖Complex.exp z‖)).mpr (by nlinarith)

/-- A tunnel height depending only on the block and approximation constant
makes each fully open upper chamber dominate the whole passage by margin one.
The order of quantifiers includes all other gates and later spacings/tunnels. -/
theorem exists_open_gate_tunnel (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 4 ∧
      ∀ p : Blueprint.BlockParameters, p.tunnelHeight n ≤ t →
      ∀ δ : Blueprint.GateIndex → ℝ,
        (∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i) →
      ∀ m : Fin (n + 1), δ ⟨n, m⟩ = Blueprint.gateUpper ⟨n, m⟩ →
      ∀ (G : Blueprint.LogModel (Blueprint.tract p δ)) (f : ℂ → ℂ),
        (∀ z ∈ Blueprint.tract p δ, 1 < ‖Complex.exp z‖ →
          ‖f (Complex.exp z) - Complex.exp (G.toFun z)‖ ≤ M / ‖Complex.exp z‖) →
      ∀ w ∈ Blueprint.passageSlice p n,
        ‖f (Complex.exp w)‖ + 1 < ‖f (Complex.exp (upperChamberCentre p ⟨n, m⟩))‖ := by
  obtain ⟨c, B, hc, _hc1, _hB, hlower⟩ := uniform_open_chamber_lower ψ n
  obtain ⟨D, t, hD, hBD, ht, htq, htD, hdecay, hlarge⟩ :=
    exists_open_tunnel_thresholds ψ.lowerRate_pos hc hM B
  refine ⟨t, ht, htq, ?_⟩
  intro p hsmall δ hδ m hgate G f happrox w hw
  have hheight : D ≤ 1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi := by
    have hrec := one_div_le_one_div_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 2) (p.tunnel_pos n))
      (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 2))
    exact htD.trans (sub_le_sub_right hrec _)
  let Q := (G.toFun (Blueprint.blockPosition p n + 3 / 2 : ℝ)).re
  have hQ : Real.exp (ψ.lowerRate * D) ≤ Q :=
    clean_reference_value_lower hbottleneck ψ p δ hδ G n hD hheight
  have hQpos : 0 < Q := lt_of_lt_of_le (Real.exp_pos _) hQ
  have hcentre : c * Q ≤ (G.toFun (upperChamberCentre p ⟨n, m⟩)).re :=
    hlower p δ m hgate G
      (hBD.trans (clean_reference_strip_gt_separation hbottleneck ψ p δ hδ G n hheight).le)
  have hpass : (G.toFun w).re ≤ c * Q / 2 := by
    have hp := passage_bound_at_clean_reference hbottleneck ψ p δ hδ G hw hD hheight
    have hm := mul_le_mul_of_nonneg_right hdecay hQpos.le
    dsimp [Q] at *
    linarith
  have ha : 2 * M + 3 ≤ c * Q / 2 := by
    have h := (div_le_iff₀ hc).mp (hlarge.trans hQ)
    nlinarith
  have hgap : Real.exp (G.toFun w).re + 2 * M + 1 <
      Real.exp (G.toFun (upperChamberCentre p ⟨n, m⟩)).re := by
    calc
      Real.exp (G.toFun w).re + 2 * M + 1 ≤ Real.exp (c * Q / 2) + 2 * M + 1 := by
        linarith [Real.exp_le_exp.mpr hpass]
      _ < Real.exp (2 * (c * Q / 2)) := exp_double_gap hM ha
      _ = Real.exp (c * Q) := by congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hcentre
  exact approximation_preserves_norm_margin
    (approximation_error_on_sample p n hM happrox (upperChamberCentre_mem_tract p δ ⟨n, m⟩ hgate) rfl)
    (approximation_error_on_sample p n hM happrox (passageSlice_subset_tract p δ n hw) hw.1) hgap

/-- Choose the whole tunnel sequence before choosing any spacing, gate
family, conformal map, or approximant. -/
theorem exists_open_gate_tunnels (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) {M : ℝ} (hM : 0 ≤ M) :
    ∃ τ : ℕ → ℝ, (∀ n, 0 < τ n ∧ τ n ≤ 1 / 4) ∧
      ∀ p : Blueprint.BlockParameters, (∀ n, p.tunnelHeight n ≤ τ n) →
      ∀ δ : Blueprint.GateIndex → ℝ,
        (∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i) →
      ∀ (G : Blueprint.LogModel (Blueprint.tract p δ)) (f : ℂ → ℂ),
        (∀ z ∈ Blueprint.tract p δ, 1 < ‖Complex.exp z‖ →
          ‖f (Complex.exp z) - Complex.exp (G.toFun z)‖ ≤ M / ‖Complex.exp z‖) →
      ∀ i : Blueprint.GateIndex, δ i = Blueprint.gateUpper i →
      ∀ w ∈ Blueprint.passageSlice p i.1,
        ‖f (Complex.exp w)‖ + 1 < ‖f (Complex.exp (upperChamberCentre p i))‖ := by
  choose τ hτ hτq hcomp using fun n => exists_open_gate_tunnel hbottleneck ψ n hM
  refine ⟨τ, fun n => ⟨hτ n, hτq n⟩, ?_⟩
  intro p hp δ hδ G f happrox i hi w hw
  exact hcomp i.1 p (hp i.1) δ hδ i.2 hi G f happrox w hw

/-- Retaining the open-chamber centre in a fixed compact segment preserves
the positive margin between the two compact maxima. -/
theorem compact_open_gate_comparison (p : Blueprint.BlockParameters)
    (i : Blueprint.GateIndex) {f : ℂ → ℂ} (hf : Continuous f)
    {P C : Set ℂ} (hP : IsCompact P) (hne : P.Nonempty)
    (hPsub : P ⊆ Blueprint.passageSlice p i.1)
    (hC : IsCompact C) (hcentre : upperChamberCentre p i ∈ C)
    (hcomp : ∀ w ∈ Blueprint.passageSlice p i.1,
      ‖f (Complex.exp w)‖ + 1 < ‖f (Complex.exp (upperChamberCentre p i))‖) :
    Blueprint.sliceMaximum P f + 1 < Blueprint.sliceMaximum C f := by
  have hcont : Continuous (logModulus f) := (hf.comp Complex.continuous_exp).norm
  obtain ⟨w, hw, he⟩ := exists_compactMaximum hP hne hcont.continuousOn
  change compactMaximum (logModulus f) P + 1 < compactMaximum (logModulus f) C
  rw [← he]
  exact (hcomp w (hPsub hw)).trans_le (le_compactMaximum hC hcont.continuousOn hcentre)

#print axioms exists_open_tunnel_thresholds
#print axioms approximation_preserves_norm_margin
#print axioms exists_open_gate_tunnel
#print axioms exists_open_gate_tunnels
#print axioms compact_open_gate_comparison

end

end MaxModulusPoints.Construction
