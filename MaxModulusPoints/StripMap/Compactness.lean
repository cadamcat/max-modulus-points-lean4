import OAI.Analysis.Crouzeix.Montel
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.StripMap.BoundedTransform
import MaxModulusPoints.StripMap.Geometry
import MaxModulusPoints.StripMap.KernelGeometry
import MaxModulusPoints.StripMap.Rescaling
import MaxModulusPoints.StripMap.Symmetry
/-!
# Compactness of normalized rescaled maps

The bounded slit-plane transform gives normal-family compactness on the fixed
strip. Its normalization prevents a subsequential limit from reaching the unit
circle, so the inverse rational transform recovers locally uniform limits of
the original rescaled maps.
-/

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

theorem bounded_rescaled_subsequence (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℕ → ℝ) :
    ∃ (g : ℂ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => slitToDisc ∘ rescaledMap e (b (φ n))) g atTop strip ∧
      DifferentiableOn ℂ g strip ∧ g 0 = 0 ∧ ∀ z ∈ strip, ‖g z‖ < 1 := by
  obtain ⟨g, φ, hφ, hc, hd, hb⟩ := OAI.CrouzeixHilbert.Conformal.montel isOpen_strip
    (fun n => slitToDisc ∘ rescaledMap e (b n))
    (fun n => (bounded_rescaledMap e he0 hepos hereal (b n)).1)
    (fun n z hz => ((bounded_rescaledMap e he0 hepos hereal (b n)).2.2 z hz).le)
  have hzero : g 0 = 0 := by
    apply tendsto_nhds_unique (hc.tendsto_at zero_mem_strip)
    simpa only [Function.comp_apply, rescaledMap_zero e he0 hepos hereal, slitToDisc_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  refine ⟨g, φ, hφ, hc, hd, hzero, ?_⟩
  intro z hz
  by_contra hn
  have he : ‖g z‖ = 1 := le_antisymm (hb z hz) (le_of_not_gt hn)
  have hm : IsMaxOn (norm ∘ g) strip z := fun w hw => (hb w hw).trans_eq he.symm
  have h := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn convex_strip.isPreconnected
    isOpen_strip hd hz hm zero_mem_strip
  change ‖g 0‖ = ‖g z‖ at h
  simp only [hzero, norm_zero, he, zero_ne_one] at h

/-- Any sequence of normalized rescaled maps has a holomorphic locally uniform subsequential limit. -/
theorem rescaledMap_subsequence (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℕ → ℝ) :
    ∃ (f : ℂ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => rescaledMap e (b (φ n))) f atTop strip ∧
      DifferentiableOn ℂ f strip ∧ f 0 = 1 := by
  obtain ⟨g, φ, hφ, hc, hd, hzero, hb⟩ :=
    bounded_rescaled_subsequence e he0 hepos hereal b
  have hden (z : ℂ) (hz : z ∈ strip) : 1 - g z ≠ 0 := by
    intro he
    have hg1 : g z = 1 := (sub_eq_zero.mp he).symm
    have h := hb z hz
    simp only [hg1, norm_one, lt_self_iff_false] at h
  have hconst : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => (1 : ℂ))
      (fun _ : ℂ => (1 : ℂ)) atTop strip :=
    (tendsto_const_nhds.tendstoUniformlyOn_const strip).tendstoLocallyUniformlyOn
  have hnum := hconst.add hc
  have hdown := hconst.sub hc
  have hgc := hd.continuousOn
  have hqc : ContinuousOn (fun z => (1 + g z) / (1 - g z)) strip :=
    (continuousOn_const.add hgc).div (continuousOn_const.sub hgc) hden
  have hq := hnum.div₀ hdown (continuousOn_const.add hgc)
    (continuousOn_const.sub hgc) hden
  have hp := hq.mul₀ hq hqc hqc
  have hraw : TendstoLocallyUniformlyOn (fun n => rescaledMap e (b (φ n)))
      (discToSlit ∘ g) atTop strip := by
    have hp' : TendstoLocallyUniformlyOn
        (fun n => discToSlit ∘ slitToDisc ∘ rescaledMap e (b (φ n)))
        (discToSlit ∘ g) atTop strip := by
      convert hp using 1
      · funext n z
        simp only [discToSlit, pow_two, Function.comp_apply, Pi.mul_apply, Pi.div_apply,
          Pi.add_apply, Pi.sub_apply]
      · funext z
        simp only [discToSlit, pow_two, Function.comp_apply, Pi.mul_apply, Pi.div_apply,
          Pi.add_apply, Pi.sub_apply]
    apply hp'.congr
    intro n z hz
    exact discToSlit_slitToDisc
      (scaledTarget_subset_slitPlane
        (normalized_equivalence_positive_real e he0 hepos hereal (b (φ n))).1
        (rescaledMap_mem_scaledTarget e he0 hepos hereal (b (φ n)) hz))
  refine ⟨discToSlit ∘ g, φ, hφ, hraw,
    hraw.differentiableOn (Eventually.of_forall fun n => rescaledMap_differentiableOn e (b (φ n)))
      isOpen_strip, ?_⟩
  simp only [Function.comp_apply, hzero, discToSlit, add_zero, sub_zero, div_one, one_pow]

end MaxModulusPoints.StripMap
