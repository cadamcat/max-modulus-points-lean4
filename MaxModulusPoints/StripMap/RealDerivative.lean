import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.IntermediateValue
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.StripMap.Geometry
import MaxModulusPoints.StripMap.Symmetry
/-!
# The real derivative of the normalized strip map

The derivative is real and never vanishes on the real axis. Continuity
propagates the positive orientation at the origin to every real point.
-/

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Metric
open MaxModulusPoints.Blueprint

theorem equivalence_injOn (e : ConformalEquivalence strip target) : InjOn e.toFun strip := by
  intro z hz w hw he
  simpa only [e.left_inv z hz, e.left_inv w hw] using congrArg e.invFun he

theorem real_mem_strip (s : ℝ) : (s : ℂ) ∈ strip := by norm_num [strip]

theorem normalized_equivalence_derivative_real (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (s : ℝ) :
    (deriv e.toFun s).im = 0 := by
  have hd := (e.holomorphic.differentiableAt
    (isOpen_strip.mem_nhds (real_mem_strip s))).hasDerivAt
  have heq : (fun t : ℝ => ((e.toFun t).re : ℂ)) = (fun t : ℝ => e.toFun t) := by
    funext t
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im,
        (normalized_equivalence_positive_real e he0 hepos hereal t).2]
  have hdreal := hd.real_of_complex.ofReal_comp
  rw [heq] at hdreal
  have hi := congrArg Complex.im (hdreal.unique hd.comp_ofReal)
  simpa only [Complex.ofReal_im] using hi.symm

/-- The prescribed orientation holds on the entire real axis. -/
theorem normalized_equivalence_derivative_positive (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) (s : ℝ) :
    0 < (deriv e.toFun s).re := by
  have hne (t : ℝ) : (deriv e.toFun t).re ≠ 0 := by
    intro ht
    apply TauCeti.deriv_ne_zero_of_injOn e.holomorphic isOpen_strip
      (equivalence_injOn e) (real_mem_strip t)
    exact Complex.ext ht (normalized_equivalence_derivative_real e he0 hepos hereal t)
  have hc : Continuous (fun t : ℝ => (deriv e.toFun t).re) :=
    Complex.continuous_re.comp ((e.holomorphic.deriv isOpen_strip).continuousOn.comp_continuous
      Complex.continuous_ofReal (fun t => real_mem_strip t))
  by_contra hs
  have hs0 : (deriv e.toFun s).re ≤ 0 := le_of_not_gt hs
  obtain ⟨t, ht⟩ := intermediate_value_univ s 0 hc
    ⟨hs0, by simpa only [Complex.ofReal_zero] using hepos.le⟩
  exact hne t ht

end MaxModulusPoints.StripMap
