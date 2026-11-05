/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The complex determinant computation is adapted from
TauCeti.Analysis.Complex.Conformal.Area.
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.ComplexEnergy
public import MaxModulusPoints.CrosscutDistortion.ConformalDensity
public import MaxModulusPoints.CrosscutDistortion.StripSlabArea

/-!
# Area control of conformal tunnel energy

The real Jacobian change of variables identifies squared complex
derivative energy with image area. Restricting to the target support slab
gives both finite pullback energy and its upper bound by the slab width.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set MeasureTheory Blueprint

private theorem abs_det_complex_derivative (c : ℂ) :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| =
      ‖c‖ ^ 2 := by
  have heq : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c =
      ContinuousLinearMap.toSpanSingleton ℂ c := by
    ext x
    simp [ContinuousLinearMap.toSpanSingleton]
  have hdet : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det =
      ‖c‖ ^ 2 := by
    simp [heq, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
  rw [hdet, abs_of_nonneg (sq_nonneg _)]

/-- A holomorphic injection onto a set of finite area has integrable squared
derivative, whose integral equals that image area. -/
theorem holomorphic_finite_area_energy {U E : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hE : MeasurableSet E) (hEU : E ⊆ U) (hinj : InjOn f E)
    (hfinite : volume (f '' E) ≠ ⊤) :
    IntegrableOn (fun q => ‖deriv f q‖ ^ 2) E ∧
      (∫ q in E, ‖deriv f q‖ ^ 2) = (volume (f '' E)).toReal := by
  let D : ℂ → ℂ →L[ℝ] ℂ := fun q =>
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f q)).restrictScalars ℝ
  have hD : ∀ q ∈ E, HasFDerivWithinAt f (D q) E q := by
    intro q hq
    have hd := ((hf q (hEU hq)).differentiableAt (hU.mem_nhds (hEU hq))).hasDerivAt
    exact (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hjac (q : ℂ) : |(D q).det| = ‖deriv f q‖ ^ 2 :=
    abs_det_complex_derivative (deriv f q)
  have hconst : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (f '' E) :=
    integrableOn_const hfinite
  have hint := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hE hD hinj (fun _ : ℂ => (1 : ℝ))).mp hconst
  have harea := integral_image_eq_integral_abs_det_fderiv_smul
    volume hE hD hinj (fun _ : ℂ => (1 : ℝ))
  constructor
  · simpa only [hjac, smul_eq_mul, mul_one] using hint
  · simpa only [hjac, smul_eq_mul, mul_one, setIntegral_const, Measure.real] using harea.symm

/-- Pullback of unit density on a finite strip slab has integrable square
on every open source subset, with energy bounded by the slab width. -/
theorem slab_density_energy_upper_bound {U E : Set ℂ}
    (φ : ConformalEquivalence U strip) (hE : IsOpen E) (hEU : E ⊆ U)
    (a b : ℝ) (hab : a ≤ b) :
    IntegrableOn (fun q => (slabPullbackDensity a b φ.toFun q) ^ 2) E ∧
      (∫ q in E, (slabPullbackDensity a b φ.toFun q) ^ 2) ≤ b - a + 1 := by
  let S : Set ℂ := E ∩ φ.toFun ⁻¹' {ξ : ℂ | ξ.re ∈ Ioo (a - 1 / 2) (b + 1 / 2)}
  have hS : IsOpen S :=
    (φ.holomorphic.continuousOn.mono hEU).isOpen_inter_preimage hE
      (isOpen_Ioo.preimage Complex.continuous_re)
  have hSE : S ⊆ E := inter_subset_left
  have hSU : S ⊆ U := hSE.trans hEU
  have himage : volume (φ.toFun '' S) ≤ ENNReal.ofReal (b - a + 1) :=
    strip_supported_image_volume_le φ S hSU a b (fun _ hq => hq.2)
  have hfinite : volume (φ.toFun '' S) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top himage
  have hinj : InjOn φ.toFun S := by
    intro q hq r hr hqr
    calc
      q = φ.invFun (φ.toFun q) := (φ.left_inv q (hSU hq)).symm
      _ = φ.invFun (φ.toFun r) := congrArg φ.invFun hqr
      _ = r := φ.left_inv r (hSU hr)
  have harea := holomorphic_finite_area_energy (strip_equivalence_source_isOpen φ)
    φ.holomorphic hS.measurableSet hSU hinj hfinite
  have heq : EqOn (fun q => (slabPullbackDensity a b φ.toFun q) ^ 2)
      (S.indicator (fun q => ‖deriv φ.toFun q‖ ^ 2)) E := by
    intro q hq
    by_cases hqslab : (φ.toFun q).re ∈ Ioo (a - 1 / 2) (b + 1 / 2)
    · rw [Set.indicator_of_mem (show q ∈ S from ⟨hq, hqslab⟩)]
      simp only [slabPullbackDensity, ite_eq_left hqslab]
    · have hqS : q ∉ S := fun h => hqslab h.2
      rw [Set.indicator_of_notMem hqS]
      simp only [slabPullbackDensity, ite_eq_right hqslab, zero_pow (by norm_num : 2 ≠ 0)]
  have hint : IntegrableOn (fun q => (slabPullbackDensity a b φ.toFun q) ^ 2) E :=
    (harea.1.integrable_indicator hS.measurableSet).integrableOn.congr_fun heq.symm
      hE.measurableSet
  have henergy : (∫ q in E, (slabPullbackDensity a b φ.toFun q) ^ 2) =
      (volume (φ.toFun '' S)).toReal := by
    calc
      _ = ∫ q in E, S.indicator (fun q => ‖deriv φ.toFun q‖ ^ 2) q :=
        setIntegral_congr_fun hE.measurableSet heq
      _ = ∫ q in S, ‖deriv φ.toFun q‖ ^ 2 := by
        rw [setIntegral_indicator hS.measurableSet, inter_eq_right.mpr hSE]
      _ = (volume (φ.toFun '' S)).toReal := harea.2
  refine ⟨hint, ?_⟩
  rw [henergy]
  exact ENNReal.toReal_le_of_le_ofReal (by linarith) himage

/-- Length and area give real-part separation across the tunnel, with
additive constant one, when both distinguished points lie in the tract. -/
theorem tunnel_separation_lower_bound_of_mem (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0) (n : ℕ)
    (w z : ℂ) (hw : w ∈ passageSlice p n) (hz : z ∈ cleanSlice p n)
    (hwV : w ∈ tract p δ) (hzV : z ∈ tract p δ) :
    1 / (2 * p.tunnelHeight n) - 1 ≤ (φ.toFun z).re - (φ.toFun w).re := by
  have hupper := slab_density_energy_upper_bound φ (isOpen_openTunnel p n)
    (openTunnel_subset_tract p δ n) (φ.toFun w).re
    (max (φ.toFun w).re (φ.toFun z).re) (le_max_left _ _)
  have hlower := tunnel_complex_energy_lower_bound p δ φ hφ0 hφre hφim n w z
    hw hz hwV hzV hupper.1
  have hbound := hlower.trans hupper.2
  have hreciprocal : 2 ≤ 1 / (2 * p.tunnelHeight n) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (p.tunnel_pos n))).mpr
    linarith [p.tunnel_le_quarter n]
  rcases le_total (φ.toFun z).re (φ.toFun w).re with h | h
  · rw [max_eq_left h] at hbound
    linarith
  · rw [max_eq_right h] at hbound
    linarith

end MaxModulusPoints.CrosscutDistortion
