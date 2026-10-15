import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
import MaxModulusPoints.ConformalKernel.TargetDomain
/-!
# Normalized conformal maps to the logarithmic target

Normalized disc maps give the unique conformal equivalence carrying a specified
source point to a specified target point with positive real derivative.
For the logarithmic tract maps the two points are `-1` and `1`.
-/

open Set Function
open scoped ComplexOrder

namespace MaxModulusPoints.ConformalKernel

/-- A biholomorphic map with the specified base points and positive real derivative. -/
structure IsNormalizedConformalMap (V H : Set ℂ) (a b : ℂ) (G : ℂ → ℂ) : Prop where
  source_mem : a ∈ V
  target_mem : b ∈ H
  differentiableOn : DifferentiableOn ℂ G V
  bijOn : BijOn G V H
  map_base : G a = b
  deriv_pos : 0 < deriv G a

private theorem complex_inv_pos {z : ℂ} (hz : 0 < z) : 0 < z⁻¹ := by
  have hreal : z = (z.re : ℂ) := Complex.eq_re_of_ofReal_le hz.le
  rw [hreal, ← Complex.ofReal_inv]
  exact Complex.zero_lt_real.mpr (inv_pos.mpr (Complex.pos_iff.mp hz).1)

/-- The holomorphic inverse of a normalized conformal map. -/
theorem IsNormalizedConformalMap.differentiableOn_inv
    {V H : Set ℂ} {a b : ℂ} {G : ℂ → ℂ}
    (hG : IsNormalizedConformalMap V H a b G) (hV : IsOpen V) :
    DifferentiableOn ℂ (invFunOn G V) H := by
  simpa only [hG.bijOn.image_eq] using
    DifferentiableOn.invFunOn hG.differentiableOn hV hG.bijOn.injOn

/-- Proper simply connected plane domains placeholder a positively normalized conformal equivalence. -/
theorem exists_normalizedConformalMap {V H : Set ℂ} {a b : ℂ}
    (hV : IsOpen V) (hsV : IsSimplyConnected V) (hpV : V ≠ univ) (ha : a ∈ V)
    (hH : IsOpen H) (hsH : IsSimplyConnected H) (hpH : H ≠ univ) (hb : b ∈ H) :
    ∃ G : ℂ → ℂ, IsNormalizedConformalMap V H a b G := by
  obtain ⟨f, hf⟩ := TauCeti.exists_isNormalizedRiemannMapOn hV hsV hpV ha
  obtain ⟨g, hg⟩ := TauCeti.exists_isNormalizedRiemannMapOn hH hsH hpH hb
  let j : ℂ → ℂ := invFunOn g H
  have hjbij : BijOn j (Metric.ball 0 1) H :=
    BijOn.symm hg.bijOn.invOn_invFunOn.symm hg.bijOn
  have hjd : DifferentiableOn ℂ j (Metric.ball 0 1) := by
    simpa only [hg.bijOn.image_eq] using
      DifferentiableOn.invFunOn hg.differentiableOn hH hg.bijOn.injOn
  refine ⟨j ∘ f, ha, hb, hjd.comp hf.differentiableOn hf.mapsTo,
    hjbij.comp hf.bijOn, ?_, ?_⟩
  · change invFunOn g H (f a) = b
    rw [hf.map_base, ← hg.map_base]
    exact hg.injOn.leftInvOn_invFunOn hb
  · have hjAt : HasDerivAt j (deriv g b)⁻¹ (f a) := by
      rw [hf.map_base, ← hg.map_base]
      exact TauCeti.hasDerivAt_invFunOn hg.differentiableOn hH hg.injOn hb
    have hfAt := (hf.differentiableOn.differentiableAt (hV.mem_nhds ha)).hasDerivAt
    rw [(hjAt.comp a hfAt).deriv]
    exact mul_pos (complex_inv_pos hg.deriv_pos) hf.deriv_pos

/-- A fixed normalized target chart turns a normalized conformal equivalence
into the normalized disc map of its source. -/
theorem normalized_discMap_comp {V H : Set ℂ} {a b : ℂ} {F g : ℂ → ℂ}
    (hV : IsOpen V) (hH : IsOpen H) (hF : IsNormalizedConformalMap V H a b F)
    (hg : TauCeti.IsNormalizedRiemannMapOn g H b) :
    TauCeti.IsNormalizedRiemannMapOn (g ∘ F) V a := by
  refine ⟨hF.source_mem, hg.differentiableOn.comp hF.differentiableOn hF.bijOn.mapsTo,
    hg.bijOn.comp hF.bijOn, ?_, ?_⟩
  · simp only [comp_apply, hF.map_base, hg.map_base]
  · have hgAt : HasDerivAt g (deriv g b) (F a) := by
      rw [hF.map_base]
      exact (hg.differentiableOn.differentiableAt (hH.mem_nhds hF.target_mem)).hasDerivAt
    have hFAt := (hF.differentiableOn.differentiableAt (hV.mem_nhds hF.source_mem)).hasDerivAt
    rw [(hgAt.comp a hFAt).deriv]
    exact mul_pos hg.deriv_pos hF.deriv_pos

/-- Positive derivative normalization makes the conformal equivalence unique on its source. -/
theorem IsNormalizedConformalMap.eqOn {V H : Set ℂ} {a b : ℂ} {F G : ℂ → ℂ}
    (hF : IsNormalizedConformalMap V H a b F) (hG : IsNormalizedConformalMap V H a b G)
    (hV : IsOpen V) (hH : IsOpen H) (hsH : IsSimplyConnected H) (hpH : H ≠ univ) :
    EqOn F G V := by
  obtain ⟨g, hg⟩ := TauCeti.exists_isNormalizedRiemannMapOn hH hsH hpH hF.target_mem
  have hfn := normalized_discMap_comp hV hH hF hg
  have hgn := normalized_discMap_comp hV hH hG hg
  have heq := hfn.eqOn hgn hV
  intro z hz
  exact hg.injOn (hF.bijOn.mapsTo hz) (hG.bijOn.mapsTo hz) (heq hz)

/-- A proper simply connected tract containing `-1` has a unique conformal map to
 the logarithmic target taking `-1` to `1` with positive real derivative. -/
theorem exists_unique_normalizedTractMap {V : Set ℂ}
    (hV : IsOpen V) (hsV : IsSimplyConnected V) (hpV : V ≠ univ) (ha : (-1 : ℂ) ∈ V) :
    ∃ G : ℂ → ℂ, IsNormalizedConformalMap V modelTarget (-1) 1 G ∧
      ∀ F : ℂ → ℂ, IsNormalizedConformalMap V modelTarget (-1) 1 F → EqOn F G V := by
  obtain ⟨G, hG⟩ := exists_normalizedConformalMap hV hsV hpV ha
    isOpen_modelTarget isSimplyConnected_modelTarget modelTarget_ne_univ one_mem_modelTarget
  exact ⟨G, hG, fun F hF => hF.eqOn hG hV isOpen_modelTarget
    isSimplyConnected_modelTarget modelTarget_ne_univ⟩

#print axioms exists_normalizedConformalMap
#print axioms normalized_discMap_comp
#print axioms IsNormalizedConformalMap.eqOn
#print axioms exists_unique_normalizedTractMap

end MaxModulusPoints.ConformalKernel
