import Mathlib.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.StripMap.Geometry
/-!
# Normalization of the strip map

Normalized Riemann maps to the disc produce the conformal equivalence from
the strip to the logarithmic target with value one and positive real derivative
at the origin.
-/

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped ComplexOrder Topology

/-- The strip-to-target conformal equivalence can be normalized at the origin. -/
theorem exists_normalized_equivalence :
    ∃ e : ConformalEquivalence strip target,
      e.toFun 0 = 1 ∧ 0 < (deriv e.toFun 0).re ∧ (deriv e.toFun 0).im = 0 := by
  obtain ⟨f, hf⟩ := TauCeti.exists_isNormalizedRiemannMapOn
    isOpen_strip isSimplyConnected_strip strip_ne_univ zero_mem_strip
  obtain ⟨g, hg⟩ := TauCeti.exists_isNormalizedRiemannMapOn
    isOpen_target isSimplyConnected_target target_ne_univ one_mem_target
  let F := Function.invFunOn f strip
  let G := Function.invFunOn g target
  have hFbij : BijOn F (ball 0 1) strip :=
    BijOn.symm hf.bijOn.invOn_invFunOn.symm hf.bijOn
  have hGbij : BijOn G (ball 0 1) target :=
    BijOn.symm hg.bijOn.invOn_invFunOn.symm hg.bijOn
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    have h := hf.differentiableOn.invFunOn isOpen_strip hf.injOn
    rwa [hf.image_eq] at h
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    have h := hg.differentiableOn.invFunOn isOpen_target hg.injOn
    rwa [hg.image_eq] at h
  let e : ConformalEquivalence strip target := {
    toFun := G ∘ f
    invFun := F ∘ g
    holomorphic := hGd.comp hf.differentiableOn hf.mapsTo
    inverse_holomorphic := hFd.comp hg.differentiableOn hg.mapsTo
    mapsTo := hGbij.mapsTo.comp hf.mapsTo
    inverse_mapsTo := hFbij.mapsTo.comp hg.mapsTo
    left_inv := by
      intro z hz
      change F (g (G (f z))) = z
      rw [hg.bijOn.invOn_invFunOn.right (hf.mapsTo hz)]
      exact hf.bijOn.invOn_invFunOn.left hz
    right_inv := by
      intro z hz
      change G (f (F (g z))) = z
      rw [hf.bijOn.invOn_invFunOn.right (hg.mapsTo hz)]
      exact hg.bijOn.invOn_invFunOn.left hz
  }
  have hG0 : G 0 = 1 := by
    simpa only [hg.map_base] using hg.bijOn.invOn_invFunOn.left hg.base_mem
  have hGdiff : DifferentiableAt ℂ G (g 1) :=
    hGd.differentiableAt (isOpen_ball.mem_nhds (hg.mapsTo hg.base_mem))
  have hgdiff : DifferentiableAt ℂ g 1 :=
    hg.differentiableOn.differentiableAt (isOpen_target.mem_nhds hg.base_mem)
  have hinv : (G ∘ g) =ᶠ[𝓝 (1 : ℂ)] id :=
    eventually_nhds_iff.mpr ⟨target, fun z hz =>
      hg.bijOn.invOn_invFunOn.left hz, isOpen_target, one_mem_target⟩
  have hmul : deriv G 0 * deriv g 1 = 1 := by
    have h := (hGdiff.hasDerivAt.comp 1 hgdiff.hasDerivAt).deriv.symm.trans hinv.deriv_eq
    simpa only [hg.map_base, deriv_id] using h
  have hGderiv : deriv G 0 = (deriv g 1)⁻¹ := by
    calc
      deriv G 0 = (deriv G 0 * deriv g 1) * (deriv g 1)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hg.deriv_ne_zero_base, mul_one]
      _ = (deriv g 1)⁻¹ := by rw [hmul, one_mul]
  have hderiv : deriv e.toFun 0 = (deriv g 1)⁻¹ * deriv f 0 := by
    change deriv (G ∘ f) 0 = _
    rw [deriv_comp 0 (by simpa only [hf.map_base, hg.map_base] using hGdiff)
      (hf.differentiableOn.differentiableAt (isOpen_strip.mem_nhds hf.base_mem)),
      hf.map_base, hGderiv]
  have hpositive : 0 < deriv e.toFun 0 := by
    rw [hderiv]
    exact mul_pos (inv_pos.mpr hg.deriv_pos) hf.deriv_pos
  refine ⟨e, ?_, (Complex.pos_iff.mp hpositive).1, (Complex.pos_iff.mp hpositive).2.symm⟩
  change G (f 0) = 1
  rw [hf.map_base, hG0]

end MaxModulusPoints.StripMap
