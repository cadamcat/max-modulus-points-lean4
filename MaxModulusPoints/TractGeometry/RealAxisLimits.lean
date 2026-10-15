import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
import MaxModulusPoints.TractGeometry.RealAxis
import MaxModulusPoints.TractGeometry.RealAxisCorrespondence
import MaxModulusPoints.TractGeometry.RealAxisOrientation
/-!
# Limits at the right-hand end of the real-axis correspondence

The increasing bijection between the two real axes sends their right-hand
ends to one another, in both directions.
-/

namespace MaxModulusPoints.TractGeometry

open Set Filter
open Blueprint

theorem tract_real_axis_limits (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i)
    (e : NormalizedSymmetricEquivalence (tract p δ) target (-1) 1) :
    Tendsto (fun x : ℝ => (e.toFun (x : ℂ)).re) atTop atTop ∧
      Tendsto (fun y : ℝ => (e.invFun (y : ℂ)).re) atTop atTop := by
  have haxis := tract_real_axis_correspondence p δ e
  have hmono := tract_real_axis_strictMonoOn p δ hδ e
  have hreal {z : ℂ} (hz : z.im = 0) : (z.re : ℂ) = z := by
    apply Complex.ext
    · rfl
    · simpa using hz.symm
  constructor
  · apply tendsto_atTop_atTop.mpr
    intro b
    have hb : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
    obtain ⟨z, hz, hfz⟩ := haxis.surjOn
      (show ((max b 1 : ℝ) : ℂ) ∈ {w : ℂ | 0 < w.re ∧ w.im = 0} from ⟨hb, rfl⟩)
    refine ⟨z.re, fun a hza => ?_⟩
    have ha : a ∈ Ioi (-2) := lt_of_lt_of_le hz.1 hza
    have hle := hmono.monotoneOn hz.1 ha hza
    change (e.toFun (z.re : ℂ)).re ≤ (e.toFun (a : ℂ)).re at hle
    rw [hreal hz.2, hfz] at hle
    exact (le_max_left b 1).trans hle
  · apply tendsto_atTop_atTop.mpr
    intro b
    let a : ℝ := max b (-1)
    have ha : -2 < a := lt_of_lt_of_le (by norm_num : (-2 : ℝ) < -1)
      (le_max_right b (-1))
    have hfa := haxis.mapsTo
      (show (a : ℂ) ∈ {z : ℂ | -2 < z.re ∧ z.im = 0} from ⟨ha, rfl⟩)
    refine ⟨(e.toFun (a : ℂ)).re, fun y hy => ?_⟩
    have hypos : 0 < y := lt_of_lt_of_le hfa.1 hy
    obtain ⟨z, hz, hfz⟩ := haxis.surjOn
      (show (y : ℂ) ∈ {w : ℂ | 0 < w.re ∧ w.im = 0} from ⟨hypos, rfl⟩)
    have hzmem : z ∈ tract p δ := by
      rw [← hreal hz.2]
      exact tract_real_mem p δ hz.1
    have hinv : e.invFun (y : ℂ) = z := by
      rw [← hfz]
      exact e.left_inv z hzmem
    have haz : a ≤ z.re := by
      by_contra h
      have hlt := hmono hz.1 ha (lt_of_not_ge h)
      change (e.toFun (z.re : ℂ)).re < (e.toFun (a : ℂ)).re at hlt
      rw [hreal hz.2, hfz] at hlt
      exact (not_lt_of_ge hy) hlt
    rw [hinv]
    exact (le_max_left b (-1)).trans haz

end MaxModulusPoints.TractGeometry
