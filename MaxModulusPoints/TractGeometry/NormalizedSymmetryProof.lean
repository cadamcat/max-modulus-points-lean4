import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Equivalence
import Mathlib.Analysis.Calculus.Deriv.Star
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
/-!
# Symmetry of normalized conformal equivalences

Reflection preserves the normalized Riemann map of a conjugation invariant
plane domain at a real base point. Uniqueness then gives conjugation symmetry,
and composing two normalized disc charts gives the normalized equivalence.
-/

noncomputable section

namespace MaxModulusPoints.TractGeometry

open Set Complex Metric Function
open scoped Topology ComplexOrder ComplexConjugate

private theorem normalized_map_symmetric {U : Set ℂ} {a : ℝ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : ∀ z ∈ U, star z ∈ U)
    (hf : TauCeti.IsNormalizedRiemannMapOn f U (a : ℂ)) :
    ∀ z ∈ U, f (star z) = star (f z) := by
  let g : ℂ → ℂ := conj ∘ f ∘ conj
  have hg : TauCeti.IsNormalizedRiemannMapOn g U (a : ℂ) := by
    refine ⟨hf.base_mem, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have hd := (hf.differentiableOn.differentiableAt (hU.mem_nhds (hs z hz))).conj_conj
      simpa only [g, starRingEnd_apply, star_star] using hd.differentiableWithinAt
    · refine ⟨?_, ?_, ?_⟩
      · intro z hz
        simpa only [g, comp_apply, mem_ball_zero_iff, norm_star, starRingEnd_apply] using
          hf.mapsTo (hs z hz)
      · intro x hx y hy hxy
        have he : f (conj x) = f (conj y) := (starRingEnd ℂ).injective hxy
        have he' := hf.injOn (hs x hx) (hs y hy) he
        simpa only [starRingEnd_apply, star_star] using congrArg conj he'
      · intro w hw
        have hw' : conj w ∈ ball (0 : ℂ) 1 := by
          simpa only [mem_ball_zero_iff, norm_conj] using hw
        obtain ⟨z, hz, he⟩ := hf.surjOn hw'
        refine ⟨conj z, hs z hz, ?_⟩
        simp only [g, comp_apply, conj_conj, he]
    · simp only [g, comp_apply, conj_ofReal, hf.map_base, map_zero]
    · have hd : deriv g (a : ℂ) = conj (deriv f (a : ℂ)) := by
        simp only [g, deriv_conj_conj, comp_apply, conj_ofReal]
      rw [hd]
      rcases Complex.pos_iff.mp hf.deriv_pos with ⟨hp, hi⟩
      apply Complex.pos_iff.mpr
      exact ⟨by simpa using hp, by simp [← hi]⟩
  intro z hz
  have he := hg.eqOn hf hU hz
  have he' := congrArg conj he
  simpa only [g, comp_apply, starRingEnd_apply, star_star] using he'

/-- Real base points determine a conformal equivalence with positive real
 derivative that commutes with conjugation. -/
theorem symmetric_riemann_maps : SymmetricRiemannMaps := by
  intro U W a b hUo _hUc hUsc hUp hWo _hWc hWsc hWp ha hb hUs hWs
  obtain ⟨f, hf⟩ := TauCeti.exists_isNormalizedRiemannMapOn hUo hUsc hUp ha
  obtain ⟨g, hg⟩ := TauCeti.exists_isNormalizedRiemannMapOn hWo hWsc hWp hb
  let j := invFunOn g W
  let i := invFunOn f U
  have hjb : BijOn j (ball (0 : ℂ) 1) W := hg.bijOn.symm hg.bijOn.invOn_invFunOn.symm
  have hib : BijOn i (ball (0 : ℂ) 1) U := hf.bijOn.symm hf.bijOn.invOn_invFunOn.symm
  have hjd : DifferentiableOn ℂ j (ball (0 : ℂ) 1) := by
    simpa only [hg.image_eq] using hg.differentiableOn.invFunOn hWo hg.injOn
  have hid : DifferentiableOn ℂ i (ball (0 : ℂ) 1) := by
    simpa only [hf.image_eq] using hf.differentiableOn.invFunOn hUo hf.injOn
  have hj0 : j 0 = (b : ℂ) := by
    simpa only [hg.map_base] using hg.injOn.leftInvOn_invFunOn hb
  have hdj : HasDerivAt j (deriv g (b : ℂ))⁻¹ 0 := by
    simpa only [hg.map_base] using
      TauCeti.hasDerivAt_invFunOn hg.differentiableOn hWo hg.injOn hb
  have hd : deriv (j ∘ f) (a : ℂ) = (deriv g (b : ℂ))⁻¹ * deriv f (a : ℂ) := by
    have hdj' : HasDerivAt j (deriv g (b : ℂ))⁻¹ (f (a : ℂ)) := by
      rwa [hf.map_base]
    exact (hdj'.comp _ (hf.differentiableOn.differentiableAt
      (hUo.mem_nhds ha)).hasDerivAt).deriv
  have hpos : 0 < deriv (j ∘ f) (a : ℂ) := by
    rw [hd]
    exact mul_pos (inv_pos.mpr hg.deriv_pos) hf.deriv_pos
  have hfs := normalized_map_symmetric hUo hUs hf
  have hgs := normalized_map_symmetric hWo hWs hg
  have hjs : ∀ w ∈ ball (0 : ℂ) 1, j (star w) = star (j w) := by
    intro w hw
    have hjw := hjb.mapsTo hw
    have hjw' : star (j w) ∈ W := hWs _ hjw
    have hsw : star w ∈ ball (0 : ℂ) 1 := by
      simpa only [mem_ball_zero_iff, norm_star] using hw
    apply hg.injOn (hjb.mapsTo hsw) hjw'
    rw [hg.surjOn.rightInvOn_invFunOn hsw, hgs _ hjw,
      hg.surjOn.rightInvOn_invFunOn hw]
  refine ⟨{
    toFun := j ∘ f
    invFun := i ∘ g
    holomorphic := hjd.comp hf.differentiableOn hf.mapsTo
    inverse_holomorphic := hid.comp hg.differentiableOn hg.mapsTo
    mapsTo := hjb.mapsTo.comp hf.mapsTo
    inverse_mapsTo := hib.mapsTo.comp hg.mapsTo
    left_inv := ?_
    right_inv := ?_
    base_value := ?_
    positive_derivative := (Complex.pos_iff.mp hpos).1
    real_derivative := (Complex.pos_iff.mp hpos).2.symm
    symmetric_map := ?_ }⟩
  · intro z hz
    simp only [comp_apply]
    rw [hg.surjOn.rightInvOn_invFunOn (hf.mapsTo hz)]
    exact hf.injOn.leftInvOn_invFunOn hz
  · intro w hw
    simp only [comp_apply]
    rw [hf.surjOn.rightInvOn_invFunOn (hg.mapsTo hw)]
    exact hg.injOn.leftInvOn_invFunOn hw
  · simp only [comp_apply, hf.map_base, hj0]
  · intro z hz
    simp only [comp_apply, hfs z hz, hjs _ (hf.mapsTo hz)]

end MaxModulusPoints.TractGeometry
