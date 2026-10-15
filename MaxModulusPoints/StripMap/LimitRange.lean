import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.StripMap.BoundedTransform
import MaxModulusPoints.StripMap.Geometry
import MaxModulusPoints.StripMap.Growth
import MaxModulusPoints.StripMap.KernelGeometry
import MaxModulusPoints.StripMap.Rescaling
/-!
# The range of a rescaled map limit

The vanishing overhang of the rescaled targets forces every locally uniform
limit into the closed right half-plane. The normalization and the maximum
modulus principle then place its image in the open right half-plane.
-/

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology

theorem rescaledMap_limit_zero (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {b : ℕ → ℝ} {f : ℂ → ℂ}
    (hc : TendstoLocallyUniformlyOn (fun n => rescaledMap e (b n)) f atTop strip) :
    f 0 = 1 := by
  apply tendsto_nhds_unique (hc.tendsto_at zero_mem_strip)
  simpa only [rescaledMap_zero e he0 hepos hereal] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))

theorem rescaledMap_limit_re_nonneg (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {b : ℕ → ℝ} (hb : Tendsto b atTop atTop)
    {f : ℂ → ℂ}
    (hc : TendstoLocallyUniformlyOn (fun n => rescaledMap e (b n)) f atTop strip) :
    ∀ z ∈ strip, 0 ≤ (f z).re := by
  intro z hz
  exact scaledTarget_limit_re_nonneg
    ((normalized_equivalence_real_escape e he0 hepos hereal).comp hb)
    (hc.tendsto_at hz) (Eventually.of_forall fun n =>
      rescaledMap_mem_scaledTarget e he0 hepos hereal (b n) hz)

/-- Every rescaled limit at an escaping real sequence takes values in the right half-plane. -/
theorem rescaledMap_limit_re_pos (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) {b : ℕ → ℝ} (hb : Tendsto b atTop atTop)
    {f : ℂ → ℂ}
    (hc : TendstoLocallyUniformlyOn (fun n => rescaledMap e (b n)) f atTop strip) :
    ∀ z ∈ strip, 0 < (f z).re := by
  have hnonneg := rescaledMap_limit_re_nonneg e he0 hepos hereal hb hc
  have hf0 := rescaledMap_limit_zero e he0 hepos hereal hc
  have hd : DifferentiableOn ℂ f strip := hc.differentiableOn
    (Eventually.of_forall fun n => rescaledMap_differentiableOn e (b n)) isOpen_strip
  let g : ℂ → ℂ := fun z => Complex.exp (-f z)
  have hgd : DifferentiableOn ℂ g strip := hd.neg.cexp
  have hbound (z : ℂ) (hz : z ∈ strip) : ‖g z‖ ≤ 1 := by
    dsimp only [g]
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
    exact neg_nonpos.mpr (hnonneg z hz)
  have hg0 : ‖g 0‖ < 1 := by
    dsimp only [g]
    rw [Complex.norm_exp, hf0, Complex.neg_re, Complex.one_re, Real.exp_lt_one_iff]
    norm_num
  intro z hz
  by_contra hn
  have hzero : (f z).re = 0 := le_antisymm (le_of_not_gt hn) (hnonneg z hz)
  have he : ‖g z‖ = 1 := by
    dsimp only [g]
    rw [Complex.norm_exp, Complex.neg_re, hzero, neg_zero, Real.exp_zero]
  have hm : IsMaxOn (norm ∘ g) strip z := fun w hw => (hbound w hw).trans_eq he.symm
  have h := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn convex_strip.isPreconnected
    isOpen_strip hgd hz hm zero_mem_strip
  change ‖g 0‖ = ‖g z‖ at h
  rw [he] at h
  exact hg0.ne h

end MaxModulusPoints.StripMap
