module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.Geometry
public import MaxModulusPoints.StripMap.Growth
public import MaxModulusPoints.StripMap.Symmetry

/-!
# Rescaling the strip map

Real translation preserves the strip. Dividing by the positive real value
at the translation point normalizes the translated map at the origin.
Locally uniform convergence of these holomorphic maps implies convergence
of their derivatives.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter
open MaxModulusPoints.Blueprint
open scoped Topology

def rescaledMap (e : ConformalEquivalence strip target) (b : ℝ) (z : ℂ) : ℂ :=
  e.toFun ((b : ℂ) + z) / e.toFun b

theorem rescaledMap_differentiableOn (e : ConformalEquivalence strip target) (b : ℝ) :
    DifferentiableOn ℂ (rescaledMap e b) strip := by
  apply (e.holomorphic.comp
    ((differentiable_const (b : ℂ)).add differentiable_id).differentiableOn ?_).div_const
  intro z hz
  simpa only [Pi.add_apply, id_eq, strip, mem_ofPred_eq, Complex.add_im,
    Complex.ofReal_im, zero_add] using hz

theorem rescaledMap_zero (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (b : ℝ) : rescaledMap e b 0 = 1 := by
  have hne : e.toFun b ≠ 0 := by
    intro h
    have hp := (normalized_equivalence_positive_real e he0 hepos hereal b).1
    simp only [h, Complex.zero_re, lt_self_iff_false] at hp
  simp only [rescaledMap, add_zero, div_self hne]

/-- Derivative convergence follows from the rescaled map limit. -/
theorem rescaled_derivative_limit_of_limit (e : ConformalEquivalence strip target)
    (h : TendstoLocallyUniformlyOn (rescaledMap e)
      (fun z : ℂ => Complex.exp (Real.pi * z)) atTop strip) :
    TendstoLocallyUniformlyOn (fun b : ℝ => deriv (rescaledMap e b))
      (fun z : ℂ => (Real.pi : ℂ) * Complex.exp (Real.pi * z)) atTop strip := by
  have hd := h.deriv (Filter.Eventually.of_forall (rescaledMap_differentiableOn e)) isOpen_strip
  have he : deriv (fun z : ℂ => Complex.exp (Real.pi * z)) =
      (fun z : ℂ => (Real.pi : ℂ) * Complex.exp (Real.pi * z)) := by
    funext z
    have hder := (((hasDerivAt_id z).const_mul (Real.pi : ℂ)).cexp).deriv
    simpa only [mul_one, mul_comm, id_eq] using hder
  simpa only [Function.comp_def, he] using hd

end MaxModulusPoints.StripMap
