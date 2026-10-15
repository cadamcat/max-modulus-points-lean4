import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.BlockPositions
import MaxModulusPoints.TractGeometry.Connectedness
import MaxModulusPoints.TractGeometry.GapPaths
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
import MaxModulusPoints.TractGeometry.RealAxis
import MaxModulusPoints.TractGeometry.RealAxisLimits
import MaxModulusPoints.TractGeometry.StripContainment
/-!
# Connected right-hand portions of a tract

Every point of positive real part lies within two units of a full vertical
line to its left. Clamping at this line retracts the tract onto a connected
right-hand portion.
-/

namespace MaxModulusPoints.WallGrowth

open Set Filter Blueprint TractGeometry

/-- A full vertical line occurs within two units to the left of each positive
real coordinate. -/
theorem exists_nearby_right_cut (p : BlockParameters) (δ : GateIndex → ℝ)
    {x : ℝ} (hx : 0 < x) :
    ∃ s : ℝ, -2 < s ∧ x - 2 ≤ s ∧ s ≤ x ∧
      ∀ y : ℝ, |y| < Real.pi / 2 → (⟨s, y⟩ : ℂ) ∈ tract p δ := by
  have hline {s : ℝ} (hs : -2 < s)
      (hgap : ∀ n, s < blockPosition p n ∨ blockPosition p n + 1 < s) :
      ∀ y : ℝ, |y| < Real.pi / 2 → (⟨s, y⟩ : ℂ) ∈ tract p δ := by
    intro y hy
    exact (tract_gap_joined p δ (z := ⟨s, y⟩) hs hy hgap).source_mem
  by_cases hb : ∃ n, blockPosition p n ≤ x ∧ x ≤ blockPosition p n + 1
  · obtain ⟨n, hn⟩ := hb
    let s := blockPosition p n - 1 / 2
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    have hgrow := blockPosition_growth p (Nat.zero_le n)
    simp only [Nat.cast_zero, sub_zero] at hgrow
    have hs : -2 < s := by dsimp [s]; linarith [Nat.cast_nonneg (α := ℝ) n]
    refine ⟨s, hs, ?_, ?_, hline hs ?_⟩
    · dsimp [s]; linarith [hn.2]
    · dsimp [s]; linarith [hn.1]
    · intro k
      by_cases hkn : n ≤ k
      · left
        have hg := blockPosition_growth p hkn
        have hc : (n : ℝ) ≤ k := by exact_mod_cast hkn
        dsimp [s]; linarith
      · right
        have hkn' : k + 1 ≤ n := Nat.succ_le_of_lt (lt_of_not_ge hkn)
        have hg := blockPosition_growth p (Nat.le_of_succ_le hkn')
        have hc : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn'
        dsimp [s]; linarith
  · refine ⟨x, by linarith, by linarith, le_rfl, hline (by linarith) ?_⟩
    intro n
    by_cases hn : x < blockPosition p n
    · exact Or.inl hn
    · exact Or.inr (lt_of_not_ge fun hn' => hb ⟨n, le_of_not_gt hn, hn'⟩)

/-- A full vertical line gives a retraction onto the portion to its right. -/
theorem tract_right_isConnected (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) {s : ℝ}
    (hs : ∀ y : ℝ, |y| < Real.pi / 2 → (⟨s, y⟩ : ℂ) ∈ tract p δ) :
    IsConnected {z ∈ tract p δ | s ≤ z.re} := by
  let c : ℂ → ℂ := fun z => ⟨max z.re s, z.im⟩
  have hc : Continuous c :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((Complex.continuous_re.max continuous_const).prodMk Complex.continuous_im)
  have himage : c '' tract p δ = {z ∈ tract p δ | s ≤ z.re} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, le_max_right _ _⟩
      by_cases hws : s ≤ w.re
      · simpa only [c, max_eq_left hws, Complex.eta] using hw
      · simpa only [c, max_eq_right (le_of_not_ge hws)] using
          hs w.im (tract_im_lt p δ (fun i => (hδ i).2) hw)
    · rintro ⟨hz, hzs⟩
      exact ⟨z, hz, by simp only [c, max_eq_left hzs, Complex.eta]⟩
  rw [← himage]
  exact (tract_isConnected p δ (fun i => (hδ i).2) (fun i => (hδ i).1)).image c hc.continuousOn

/-- Regard the symmetric logarithmic equivalence as its normalized
conformal equivalence. -/
def normalizedEquivalence (p : BlockParameters) (δ : GateIndex → ℝ)
    (G : LogModel (tract p δ)) :
    NormalizedSymmetricEquivalence (tract p δ) target (-1) 1 where
  toConformalEquivalence := G.toConformalEquivalence
  base_value := by simpa using G.base_value
  positive_derivative := by simpa using G.positive_derivative
  real_derivative := by simpa using G.real_derivative
  symmetric_map := G.symmetric_map

/-- Every sufficiently large target circle has a preimage in the connected
right-hand portion containing the given point. -/
theorem right_cut_meets_circle (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) (G : LogModel (tract p δ))
    {s : ℝ} (hs : ∀ y : ℝ, |y| < Real.pi / 2 → (⟨s, y⟩ : ℂ) ∈ tract p δ)
    {z : ℂ} (hz : z ∈ tract p δ) (hsz : s ≤ z.re)
    {ρ : ℝ} (hρ : ‖G.toFun z‖ ≤ ρ) :
    ∃ v ∈ tract p δ, s ≤ v.re ∧ ‖G.toFun v‖ = ρ := by
  let e := normalizedEquivalence p δ G
  obtain ⟨T, hT⟩ := tendsto_atTop_atTop.mp
    (tract_real_axis_limits p δ (fun i => (hδ i).2) e).1 ρ
  let a : ℝ := max (max s T) 0
  have ha : -2 < a := by dsimp [a]; linarith [le_max_right (max s T) 0]
  have haT : T ≤ a := (le_max_right s T).trans (le_max_left _ _)
  have has : s ≤ a := (le_max_left s T).trans (le_max_left _ _)
  have hlarge : ρ ≤ ‖G.toFun (a : ℂ)‖ :=
    (hT a haT).trans (Complex.re_le_norm _)
  let S := {v ∈ tract p δ | s ≤ v.re}
  have hS : IsConnected S := tract_right_isConnected p δ hδ hs
  have hcont : ContinuousOn (fun v => ‖G.toFun v‖) S :=
    G.holomorphic.continuousOn.norm.mono (fun _ hv => hv.1)
  obtain ⟨v, hv, heq⟩ := hS.isPreconnected.intermediate_value
    (show z ∈ S from ⟨hz, hsz⟩)
    (show (a : ℂ) ∈ S from ⟨tract_real_mem p δ ha, has⟩)
    hcont ⟨hρ, hlarge⟩
  exact ⟨v, hv.1, hv.2, heq⟩

end MaxModulusPoints.WallGrowth
