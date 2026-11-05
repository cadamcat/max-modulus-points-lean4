module

public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Tactic.NormNum
public import MaxModulusPoints.Blueprint.Data

/-!
# Reflection symmetry of normalized strip equivalences

A conformal equivalence from a symmetric domain to the horizontal strip
commutes with conjugation when its base point and derivative are real.
The derivative normalization is positive, fixing the orientation.
-/


@[expose] public section

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint
open scoped ComplexOrder ComplexConjugate

/-- Positive real derivative normalization forces a strip equivalence to
respect reflection in the real axis. No boundary extension is required. -/
theorem strip_equivalence_conj {U : Set ℂ} (hUo : IsOpen U) (b : ℝ)
    (hb : (b : ℂ) ∈ U) (hU : MapsTo conj U U)
    (φ : ConformalEquivalence U strip) (hφ0 : φ.toFun b = 0)
    (hφre : 0 < (deriv φ.toFun b).re) (hφim : (deriv φ.toFun b).im = 0) :
    ∀ z ∈ U, φ.toFun (conj z) = conj (φ.toFun z) := by
  have hSo : IsOpen strip := isOpen_lt Complex.continuous_im.abs continuous_const
  have h0S : (0 : ℂ) ∈ strip := by norm_num [strip]
  have hconv : Convex ℝ strip := by
    simpa only [strip, abs_lt, setOf_and] using
      (convex_halfSpace_im_gt (-(1 / 2 : ℝ))).inter
        (convex_halfSpace_im_lt (1 / 2 : ℝ))
  let : ContractibleSpace strip := hconv.contractibleSpace ⟨0, h0S⟩
  have hsc : IsSimplyConnected strip := inferInstanceAs (SimplyConnectedSpace strip)
  have hproper : strip ≠ univ := by
    intro heq
    have hi : Complex.I ∈ strip := by rw [heq]; trivial
    norm_num [strip] at hi
  obtain ⟨C, hC⟩ := TauCeti.exists_isNormalizedRiemannMapOn hSo hsc hproper h0S
  have hφbij : BijOn φ.toFun U strip := by
    refine ⟨φ.mapsTo, ?_, ?_⟩
    · intro z hz w hw heq
      have hi := congrArg φ.invFun heq
      simpa only [φ.left_inv z hz, φ.left_inv w hw] using hi
    · intro z hz
      exact ⟨φ.invFun z, φ.inverse_mapsTo hz, φ.right_inv z hz⟩
  have hφpos : 0 < deriv φ.toFun b := Complex.pos_iff.mpr ⟨hφre, hφim.symm⟩
  let ψ : ℂ → ℂ := conj ∘ φ.toFun ∘ conj
  have hψd : DifferentiableOn ℂ ψ U := by
    intro z hz
    have hh := (φ.holomorphic.differentiableAt (hUo.mem_nhds (hU hz))).conj_conj
    simpa only [Complex.conj_conj] using hh.differentiableWithinAt
  have hψm : MapsTo ψ U strip := by
    intro z hz
    have hh := φ.mapsTo (hU hz)
    simpa only [ψ, Function.comp_apply, strip, mem_ofPred_eq, Complex.conj_im, abs_neg] using hh
  have hψbij : BijOn ψ U strip := by
    refine ⟨hψm, ?_, ?_⟩
    · intro z hz w hw heq
      have hh := congrArg conj heq
      simp only [ψ, Function.comp_apply, Complex.conj_conj] at hh
      have he := congrArg conj (hφbij.injOn (hU hz) (hU hw) hh)
      simpa only [Complex.conj_conj] using he
    · intro z hz
      have hzc : conj z ∈ strip := by
        simpa only [strip, mem_ofPred_eq, Complex.conj_im, abs_neg] using hz
      refine ⟨conj (φ.invFun (conj z)), hU (φ.inverse_mapsTo hzc), ?_⟩
      simp only [ψ, Function.comp_apply, Complex.conj_conj,
        φ.right_inv (conj z) hzc]
  have hψ0 : ψ b = 0 := by simp [ψ, hφ0]
  have hψder : deriv ψ b = deriv φ.toFun b := by
    dsimp only [ψ]
    rw [deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_ofReal]
    apply Complex.ext <;> simp [hφim]
  have hnorm (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (hfbij : BijOn f U strip)
      (hf0 : f b = 0) (hfpos : 0 < deriv f b) :
      TauCeti.IsNormalizedRiemannMapOn (C ∘ f) U b := by
    refine ⟨hb, hC.differentiableOn.comp hf hfbij.mapsTo, hC.bijOn.comp hfbij, ?_, ?_⟩
    · simp only [Function.comp_apply, hf0, hC.map_base]
    · have hfAt := (hf.differentiableAt (hUo.mem_nhds hb)).hasDerivAt
      have hCAt : HasDerivAt C (deriv C 0) (f b) := by
        rw [hf0]
        exact (hC.differentiableOn.differentiableAt (hSo.mem_nhds h0S)).hasDerivAt
      rw [(hCAt.comp (b : ℂ) hfAt).deriv]
      exact mul_pos hC.deriv_pos hfpos
  have hnormal := hnorm φ.toFun φ.holomorphic hφbij hφ0 hφpos
  have hreflected := hnorm ψ hψd hψbij hψ0 (by rw [hψder]; exact hφpos)
  have heq := hreflected.eqOn hnormal hUo
  intro z hz
  have hh := congrArg conj (hC.injOn (hψm hz) (φ.mapsTo hz) (heq hz))
  simpa only [ψ, Function.comp_apply, Complex.conj_conj] using hh

end MaxModulusPoints.CrosscutDistortion
