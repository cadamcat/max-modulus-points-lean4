module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.Geometry
public import MaxModulusPoints.StripMap.Normalization

/-!
# Real symmetry of the normalized strip map

Conjugating a normalized Riemann map on a symmetric domain preserves its
normalization. Uniqueness then makes the strip map real and positive on the
real axis.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped ComplexOrder ComplexConjugate Topology

theorem conj_mem_strip {z : ℂ} (hz : z ∈ strip) : conj z ∈ strip := by
  simpa only [strip, mem_ofPred_eq, Complex.conj_im, abs_neg] using hz

theorem conj_mem_target {z : ℂ} (hz : z ∈ target) : conj z ∈ target := by
  simpa only [target, mem_ofPred_eq, Complex.conj_im, Complex.conj_re, abs_neg] using hz

theorem normalized_riemannMap_symmetric {U : Set ℂ} {a : ℝ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hsym : ∀ z ∈ U, conj z ∈ U)
    (hf : TauCeti.IsNormalizedRiemannMapOn f U (a : ℂ)) :
    ∀ z ∈ U, f (conj z) = conj (f z) := by
  let g : ℂ → ℂ := conj ∘ f ∘ conj
  have hg : TauCeti.IsNormalizedRiemannMapOn g U (a : ℂ) := by
    refine ⟨hf.base_mem, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro z hz
      have hd := (hf.differentiableOn.differentiableAt
        (hU.mem_nhds (hsym z hz))).conj_conj
      simpa only [Complex.conj_conj] using hd.differentiableWithinAt
    · intro z hz
      simpa only [g, Function.comp_apply, mem_ball_zero_iff, Complex.norm_conj] using
        hf.mapsTo (hsym z hz)
    · intro z hz w hw he
      have hfw : f (conj z) = f (conj w) := by
        simpa only [g, Function.comp_apply, Complex.conj_conj] using congrArg conj he
      have hzw := hf.injOn (hsym z hz) (hsym w hw) hfw
      simpa only [Complex.conj_conj] using congrArg conj hzw
    · intro w hw
      have hwc : conj w ∈ ball (0 : ℂ) 1 := by
        simpa only [mem_ball_zero_iff, Complex.norm_conj] using hw
      obtain ⟨z, hz, he⟩ := hf.surjOn hwc
      refine ⟨conj z, hsym z hz, ?_⟩
      simp only [g, Function.comp_apply, Complex.conj_conj, he]
    · simp only [g, Function.comp_apply, Complex.conj_ofReal, hf.map_base,
        map_zero]
    · have hreal : conj (deriv f (a : ℂ)) = deriv f (a : ℂ) := by
        rw [← hf.coe_norm_deriv]
        exact Complex.conj_ofReal _
      simpa only [g, deriv_conj_conj, Function.comp_apply, Complex.conj_ofReal,
        hreal] using hf.deriv_pos
  intro z hz
  have h := hg.eqOn hf hU hz
  have h' := congrArg conj h
  simpa only [g, Function.comp_apply, Complex.conj_conj] using h'

/-- Real symmetry of any strip-to-target equivalence with the prescribed normalization. -/
theorem normalized_equivalence_symmetric (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) :
    ∀ z ∈ strip, e.toFun (conj z) = conj (e.toFun z) := by
  obtain ⟨g, hg⟩ := TauCeti.exists_isNormalizedRiemannMapOn
    isOpen_target isSimplyConnected_target target_ne_univ one_mem_target
  have hebij : BijOn e.toFun strip target := by
    refine ⟨e.mapsTo, ?_, ?_⟩
    · intro z hz w hw he
      simpa only [e.left_inv z hz, e.left_inv w hw] using congrArg e.invFun he
    · intro w hw
      exact ⟨e.invFun w, e.inverse_mapsTo hw, e.right_inv w hw⟩
  have hcompose : TauCeti.IsNormalizedRiemannMapOn (g ∘ e.toFun) strip 0 := by
    refine ⟨zero_mem_strip, hg.differentiableOn.comp e.holomorphic e.mapsTo,
      hg.bijOn.comp hebij, ?_, ?_⟩
    · simp only [Function.comp_apply, he0, hg.map_base]
    · rw [deriv_comp 0
        (hg.differentiableOn.differentiableAt (isOpen_target.mem_nhds
          (e.mapsTo zero_mem_strip)))
        (e.holomorphic.differentiableAt (isOpen_strip.mem_nhds zero_mem_strip)), he0]
      exact mul_pos hg.deriv_pos (Complex.pos_iff.mpr ⟨hepos, hereal.symm⟩)
  have hs := normalized_riemannMap_symmetric isOpen_strip
    (fun _ hz => conj_mem_strip hz) hcompose
  have ht := normalized_riemannMap_symmetric isOpen_target
    (fun _ hz => conj_mem_target hz) hg
  intro z hz
  apply hg.injOn (e.mapsTo (conj_mem_strip hz)) (conj_mem_target (e.mapsTo hz))
  exact (hs z hz).trans (ht (e.toFun z) (e.mapsTo hz)).symm

/-- The normalized map sends every real point to a positive real point. -/
theorem normalized_equivalence_positive_real (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (s : ℝ) :
    0 < (e.toFun s).re ∧ (e.toFun s).im = 0 := by
  have hs : (s : ℂ) ∈ strip := by norm_num [strip]
  have he := normalized_equivalence_symmetric e he0 hepos hereal (s : ℂ) hs
  have him : (e.toFun s).im = 0 := by
    have hi := congrArg Complex.im he
    simp only [Complex.conj_ofReal, Complex.conj_im] at hi
    linarith
  refine ⟨?_, him⟩
  have ht := e.mapsTo hs
  simpa only [target, mem_ofPred_eq, him, abs_zero, Real.log_zero, max_self,
    mul_zero] using ht

end MaxModulusPoints.StripMap
