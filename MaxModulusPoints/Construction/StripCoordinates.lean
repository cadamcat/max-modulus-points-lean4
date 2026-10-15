import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.IntermediateValue
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
import MaxModulusPoints.Blueprint.Interfaces.StripMapData
import MaxModulusPoints.Construction.OpenGate
/-!
# Normalized strip coordinates

For the passage comparison in Pardo-Simón–Sixsmith, Proposition 4.1,
compose the logarithmic conformal map with the inverse strip map.
The normalization and real-axis properties follow from the displayed
conformal and strip-growth data.
-/

namespace MaxModulusPoints.Construction

open Set Filter
open scoped Topology

noncomputable section

theorem strip_isOpen : IsOpen Blueprint.strip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem real_mem_strip (x : ℝ) : (x : ℂ) ∈ Blueprint.strip := by
  simp [Blueprint.strip]

theorem positive_halfPlane_subset_target :
    {z : ℂ | 0 < z.re} ⊆ Blueprint.target := by
  intro z hz
  change 0 < z.re at hz
  change -14 * max 0 (Real.log |z.im|) < z.re
  linarith [le_max_left (0 : ℝ) (Real.log |z.im|)]

theorem target_mem_nhds_one : Blueprint.target ∈ 𝓝 (1 : ℂ) := by
  apply mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by norm_num : (1 : ℂ) ∈ {z : ℂ | 0 < z.re}))
  exact positive_halfPlane_subset_target

/-- The inverse strip map is differentiable at the normalized target point. -/
theorem strip_inverse_differentiableAt_one (ψ : Blueprint.StripMapData) :
    DifferentiableAt ℂ ψ.invFun 1 :=
  (ψ.inverse_holomorphic 1 (positive_halfPlane_subset_target (by norm_num))).differentiableAt
    target_mem_nhds_one

theorem strip_inverse_at_one (ψ : Blueprint.StripMapData) : ψ.invFun 1 = 0 := by
  simpa only [ψ.base_value] using ψ.left_inv 0 (real_mem_strip 0)

/-- Inverting the normalized strip map preserves its positive real derivative. -/
theorem strip_inverse_derivative_normalization (ψ : Blueprint.StripMapData) :
    0 < (deriv ψ.invFun 1).re ∧ (deriv ψ.invFun 1).im = 0 := by
  have hforward : DifferentiableAt ℂ ψ.toFun 0 :=
    (ψ.holomorphic 0 (real_mem_strip 0)).differentiableAt
      (strip_isOpen.mem_nhds (real_mem_strip 0))
  have hinverse : DifferentiableAt ℂ ψ.invFun (ψ.toFun 0) := by
    rw [ψ.base_value]
    exact strip_inverse_differentiableAt_one ψ
  have hlocal : (ψ.invFun ∘ ψ.toFun) =ᶠ[𝓝 0] id := by
    filter_upwards [strip_isOpen.mem_nhds (real_mem_strip 0)] with z hz
    exact ψ.left_inv z hz
  have hproduct : deriv ψ.invFun 1 * deriv ψ.toFun 0 = 1 := by
    have hchain := deriv_comp 0 hinverse hforward
    rw [ψ.base_value] at hchain
    have hid : deriv (ψ.invFun ∘ ψ.toFun) 0 = 1 := by
      rw [hlocal.deriv_eq, deriv_id]
    exact hchain.symm.trans hid
  have hre := congrArg Complex.re hproduct
  have him := congrArg Complex.im hproduct
  simp only [Complex.mul_re, Complex.one_re, ψ.real_derivative, mul_zero, sub_zero] at hre
  simp only [Complex.mul_im, Complex.one_im, ψ.real_derivative, mul_zero, zero_add] at him
  constructor
  · nlinarith [ψ.positive_derivative]
  · exact (mul_eq_zero.mp him).resolve_right (ne_of_gt ψ.positive_derivative)

/-- The strip map is strictly increasing on the real axis. -/
theorem strip_real_strictMono (ψ : Blueprint.StripMapData) :
    StrictMono (fun x : ℝ => (ψ.toFun x).re) := by
  intro s t hst
  have h := (ψ.growth s (t - s) (by linarith)).1
  rw [show s + (t - s) = t by ring] at h
  have he : 1 < Real.exp (ψ.lowerRate * (t - s)) :=
    Real.one_lt_exp_iff.mpr (mul_pos ψ.lowerRate_pos (sub_pos.mpr hst))
  nlinarith [(ψ.positive_real s).1]

/-- The positive real axis is exactly covered by real strip coordinates.
The two-sided real growth bounds suffice, without an extra symmetry assumption
on the inverse map. -/
theorem strip_real_surjective_positive (ψ : Blueprint.StripMapData)
    {y : ℝ} (hy : 0 < y) : ∃ x : ℝ, ψ.toFun x = (y : ℂ) := by
  have hcont : Continuous (fun x : ℝ => (ψ.toFun x).re) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact Complex.continuous_re.continuousAt.comp
      (((ψ.holomorphic x (real_mem_strip x)).differentiableAt
        (strip_isOpen.mem_nhds (real_mem_strip x))).continuousAt.comp
          Complex.continuous_ofReal.continuousAt)
  let R := (|Real.log y| + 1) / ψ.lowerRate
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (by positivity) ψ.lowerRate_pos
  have hmul : ψ.lowerRate * R = |Real.log y| + 1 := by
    dsimp [R]
    field_simp [ne_of_gt ψ.lowerRate_pos]
  have hleft : (ψ.toFun (-R : ℝ)).re ≤ y := by
    have hdecay := strip_decay_from_separation ψ (real_mem_strip (-R)) hR.le
      (show R ≤ 0 - ((-R : ℝ) : ℂ).re by simp)
    simp only [Complex.ofReal_zero, ψ.base_value, Complex.one_re, mul_one] at hdecay
    apply hdecay.trans
    rw [← Real.exp_log hy]
    apply Real.exp_le_exp.mpr
    rw [neg_mul, hmul]
    linarith [neg_le_abs (Real.log y)]
  have hright : y ≤ (ψ.toFun R).re := by
    have hgrowth := (ψ.growth 0 R hR.le).1
    simp only [zero_add, Complex.ofReal_zero, ψ.base_value, Complex.one_re, mul_one] at hgrowth
    apply le_trans ?_ hgrowth
    rw [← Real.exp_log hy]
    apply Real.exp_le_exp.mpr
    rw [hmul]
    linarith [le_abs_self (Real.log y)]
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show -R ≤ R by linarith)
    hcont.continuousOn ⟨hleft, hright⟩
  refine ⟨x, ?_⟩
  apply Complex.ext
  · exact hx
  · simpa using (ψ.positive_real x).2

theorem strip_inverse_positive_real (ψ : Blueprint.StripMapData)
    {y : ℝ} (hy : 0 < y) : (ψ.invFun (y : ℂ)).im = 0 := by
  obtain ⟨x, hx⟩ := strip_real_surjective_positive ψ hy
  rw [← hx, ψ.left_inv x (real_mem_strip x)]
  exact Complex.ofReal_im x

/-- The normalized logarithmic map expressed in strip coordinates. -/
def stripCoordinates {V : Set ℂ} (ψ : Blueprint.StripMapData) (G : Blueprint.LogModel V) :
    Blueprint.ConformalEquivalence V Blueprint.strip where
  toFun := ψ.invFun ∘ G.toFun
  invFun := G.invFun ∘ ψ.toFun
  holomorphic := ψ.inverse_holomorphic.comp G.holomorphic G.mapsTo
  inverse_holomorphic := G.inverse_holomorphic.comp ψ.holomorphic ψ.mapsTo
  mapsTo := ψ.inverse_mapsTo.comp G.mapsTo
  inverse_mapsTo := G.inverse_mapsTo.comp ψ.mapsTo
  left_inv := by
    intro z hz
    simp only [Function.comp_apply, ψ.right_inv _ (G.mapsTo hz), G.left_inv z hz]
  right_inv := by
    intro z hz
    simp only [Function.comp_apply, G.right_inv _ (ψ.mapsTo hz), ψ.left_inv z hz]

theorem stripCoordinates_normalized {V : Set ℂ}
    (ψ : Blueprint.StripMapData) (G : Blueprint.LogModel V) :
    (stripCoordinates ψ G).toFun (-1) = 0 ∧
      0 < (deriv (stripCoordinates ψ G).toFun (-1)).re ∧
      (deriv (stripCoordinates ψ G).toFun (-1)).im = 0 := by
  have hbase : (stripCoordinates ψ G).toFun (-1) = 0 := by
    change ψ.invFun (G.toFun (-1)) = 0
    rw [G.base_value, strip_inverse_at_one]
  have hG : DifferentiableAt ℂ G.toFun (-1) :=
    (G.holomorphic (-1) G.base_mem).differentiableAt (G.open_domain.mem_nhds G.base_mem)
  have hinverse : DifferentiableAt ℂ ψ.invFun (G.toFun (-1)) := by
    rw [G.base_value]
    exact strip_inverse_differentiableAt_one ψ
  have hchain : deriv (stripCoordinates ψ G).toFun (-1) =
      deriv ψ.invFun 1 * deriv G.toFun (-1) := by
    change deriv (ψ.invFun ∘ G.toFun) (-1) = _
    rw [deriv_comp (-1) hinverse hG, G.base_value]
  obtain ⟨hpos, him⟩ := strip_inverse_derivative_normalization ψ
  refine ⟨hbase, ?_, ?_⟩
  · rw [hchain, Complex.mul_re, him, G.real_derivative]
    simpa using mul_pos hpos G.positive_derivative
  · rw [hchain, Complex.mul_im, him, G.real_derivative]
    simp

theorem logModel_real_axis {V : Set ℂ} (G : Blueprint.LogModel V)
    {x : ℝ} (hx : (x : ℂ) ∈ V) :
    (G.toFun x).im = 0 ∧ 0 < (G.toFun x).re := by
  have hsym := congrArg Complex.im (G.symmetric_map x hx)
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_im] at hsym
  have him : (G.toFun x).im = 0 := by linarith
  refine ⟨him, ?_⟩
  have htarget := G.mapsTo hx
  change -14 * max 0 (Real.log |(G.toFun x).im|) < (G.toFun x).re at htarget
  simpa [him] using htarget

theorem stripCoordinates_real {V : Set ℂ} (ψ : Blueprint.StripMapData)
    (G : Blueprint.LogModel V) {x : ℝ} (hx : (x : ℂ) ∈ V) :
    ((stripCoordinates ψ G).toFun x).im = 0 := by
  obtain ⟨him, hpos⟩ := logModel_real_axis G hx
  have hGreal : G.toFun x = ((G.toFun x).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  change (ψ.invFun (G.toFun x)).im = 0
  rw [hGreal]
  exact strip_inverse_positive_real ψ hpos

/-- Equation (4.3) for the logarithmic conformal map itself, with no separately
assumed normalized tract-to-strip equivalence. The reference point is real. -/
theorem logModel_passage_bound (hbottleneck : Blueprint.BottleneckEstimates)
    (ψ : Blueprint.StripMapData) (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ))
    {n : ℕ} {x : ℝ} {w : ℂ} (hx : (x : ℂ) ∈ Blueprint.cleanSlice p n)
    (hxV : (x : ℂ) ∈ Blueprint.tract p δ)
    (hw : w ∈ Blueprint.passageSlice p n) (hwV : w ∈ Blueprint.tract p δ)
    {D : ℝ} (hD : 0 ≤ D)
    (hheight : D ≤ 1 / (2 * p.tunnelHeight n) - Real.log 32 / Real.pi) :
    (G.toFun w).re ≤ Real.exp (-ψ.lowerRate * D) * (G.toFun x).re := by
  let φ := stripCoordinates ψ G
  obtain ⟨hbase, hpos, him⟩ := stripCoordinates_normalized ψ G
  have hbound := bottleneck_passage_bound hbottleneck ψ p δ hδ φ
    hbase hpos him hx hw hwV hD hheight
  have hwmap : ψ.toFun (φ.toFun w) = G.toFun w := ψ.right_inv _ (G.mapsTo hwV)
  have hxreal : φ.toFun x = ((φ.toFun x).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact stripCoordinates_real ψ G hxV
  have hxmap : ψ.toFun ((φ.toFun x).re : ℂ) = G.toFun x := by
    rw [← hxreal]
    exact ψ.right_inv _ (G.mapsTo hxV)
  rwa [hwmap, hxmap] at hbound

#print axioms strip_inverse_derivative_normalization
#print axioms strip_real_surjective_positive
#print axioms stripCoordinates_normalized
#print axioms stripCoordinates_real
#print axioms logModel_passage_bound

end

end MaxModulusPoints.Construction
