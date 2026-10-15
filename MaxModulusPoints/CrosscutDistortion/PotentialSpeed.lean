import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import MaxModulusPoints.CrosscutDistortion.SlabPotentials
/-!
# Weighted speed bounds for slab potentials

A 1-Lipschitz potential cannot increase the speed of a differentiable
curve. Slab potentials have zero derivative outside their vertical support,
so their increments are controlled by the speed spent inside that slab.
-/

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set Filter MeasureTheory
open scoped Topology

/-- A 1-Lipschitz real-valued function cannot increase the norm of a curve's
derivative. The total derivative also satisfies the bound at a corner. -/
theorem lipschitz_deriv_comp_norm_le (F : ℂ → ℝ) (hF : LipschitzWith 1 F)
    (γ : ℝ → ℂ) (x : ℝ) (v : ℂ) (hγ : HasDerivAt γ v x) :
    ‖deriv (F ∘ γ) x‖ ≤ ‖v‖ := by
  by_cases hdiff : DifferentiableAt ℝ (F ∘ γ) x
  · apply le_of_tendsto_of_tendsto hdiff.hasDerivAt.tendsto_slope.norm hγ.tendsto_slope.norm
    exact Eventually.of_forall fun y => by
      simp only [slope_def_module, norm_smul]
      apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simpa only [Function.comp_apply, NNReal.coe_one, one_mul, dist_eq_norm]
        using hF.dist_le_mul (γ y) (γ x)
  · rw [deriv_zero_of_not_differentiableAt hdiff, norm_zero]
    exact norm_nonneg _

/-- Curve speed counted only while its image lies between the slab's vertical sides. -/
def slabWeightedSpeed (a b : ℝ) (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  if (γ t).re ∈ Ioo (a - 1 / 2) (b + 1 / 2) then ‖deriv γ t‖ else 0

/-- Both pulled-back potential derivatives are bounded by slab-weighted speed,
including at points on the support boundary. -/
theorem slab_potential_deriv_le_speed (a b : ℝ) (γ : ℝ → ℂ) (x : ℝ)
    (hγ : DifferentiableAt ℝ γ x) :
    ‖deriv (fun t => slabBasePotential a b (γ t)) x‖ ≤ slabWeightedSpeed a b γ x ∧
      ‖deriv (fun t => slabRoofPotential a b (γ t)) x‖ ≤ slabWeightedSpeed a b γ x := by
  by_cases hinside : (γ x).re ∈ Ioo (a - 1 / 2) (b + 1 / 2)
  · rw [slabWeightedSpeed, ite_eq_left hinside]
    exact ⟨lipschitz_deriv_comp_norm_le _ (slab_potentials_lipschitz a b).1 γ x _ hγ.hasDerivAt,
      lipschitz_deriv_comp_norm_le _ (slab_potentials_lipschitz a b).2 γ x _ hγ.hasDerivAt⟩
  · rw [slabWeightedSpeed, ite_eq_right hinside]
    have hout : (γ x).re ≤ a - 1 / 2 ∨ b + 1 / 2 ≤ (γ x).re := by
      by_cases hl : a - 1 / 2 < (γ x).re
      · exact Or.inr (le_of_not_gt fun hr => hinside ⟨hl, hr⟩)
      · exact Or.inl (le_of_not_gt hl)
    have hzero := slab_potentials_zero_outside a b (γ x) hout
    have hminB : IsLocalMin (fun t => slabBasePotential a b (γ t)) x := by
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [hzero.1]
        exact (slab_potentials_nonneg a b (γ t)).1
    have hminR : IsLocalMin (fun t => slabRoofPotential a b (γ t)) x := by
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [hzero.2]
        exact (slab_potentials_nonneg a b (γ t)).2
    rw [hminB.deriv_eq_zero, hminR.deriv_eq_zero]
    simp

/-- On a compact interval, each potential increment is at most the integral
of slab-weighted speed. Integrability of that speed remains explicit. -/
theorem slab_potential_increments_le_integral (a b c d : ℝ) (hcd : c ≤ d)
    (γ : ℝ → ℂ) (hγ : ContDiffOn ℝ 1 γ (uIcc c d))
    (hspeed : IntervalIntegrable (slabWeightedSpeed a b γ) volume c d) :
    |slabBasePotential a b (γ d) - slabBasePotential a b (γ c)| ≤
        ∫ t in c..d, slabWeightedSpeed a b γ t ∧
      |slabRoofPotential a b (γ d) - slabRoofPotential a b (γ c)| ≤
        ∫ t in c..d, slabWeightedSpeed a b γ t := by
  have hγat (t : ℝ) (ht : t ∈ Ioo c d) : DifferentiableAt ℝ γ t := by
    apply (hγ.differentiableOn (by norm_num)).differentiableAt
    rw [uIcc_of_le hcd]
    exact Icc_mem_nhds ht.1 ht.2
  have hbound (F : ℂ → ℝ)
      (hAC : AbsolutelyContinuousOnInterval (F ∘ γ) c d)
      (hderiv : ∀ t ∈ Ioo c d, ‖deriv (F ∘ γ) t‖ ≤ slabWeightedSpeed a b γ t) :
      |F (γ d) - F (γ c)| ≤ ∫ t in c..d, slabWeightedSpeed a b γ t := by
    calc
      |F (γ d) - F (γ c)| = ‖∫ t in c..d, deriv (F ∘ γ) t‖ := by
        rw [hAC.integral_deriv_eq_sub, Real.norm_eq_abs]
        rfl
      _ ≤ ∫ t in c..d, slabWeightedSpeed a b γ t := by
        apply intervalIntegral.norm_integral_le_of_norm_le hcd ?_ hspeed
        filter_upwards [volume.ae_ne d] with t htd ht
        exact hderiv t ⟨ht.1, lt_of_le_of_ne ht.2 htd⟩
  constructor
  · exact hbound (slabBasePotential a b)
      ((slab_potentials_lipschitz a b).1.comp_absolutelyContinuousOnInterval
        hγ.absolutelyContinuousOnInterval)
      (fun t ht => (slab_potential_deriv_le_speed a b γ t (hγat t ht)).1)
  · exact hbound (slabRoofPotential a b)
      ((slab_potentials_lipschitz a b).2.comp_absolutelyContinuousOnInterval
        hγ.absolutelyContinuousOnInterval)
      (fun t ht => (slab_potential_deriv_le_speed a b γ t (hγat t ht)).2)

end MaxModulusPoints.CrosscutDistortion
