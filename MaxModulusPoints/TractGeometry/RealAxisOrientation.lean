import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
import MaxModulusPoints.TractGeometry.Openness
import MaxModulusPoints.TractGeometry.RealAxis
import MaxModulusPoints.TractGeometry.RealAxisCorrespondence
/-!
# Orientation of the real-axis conformal correspondence

The real-axis restriction is a continuous injection. Its positive derivative
at the normalization point selects the increasing orientation.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_real_axis_strictMonoOn (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i)
    (e : NormalizedSymmetricEquivalence (tract p δ) target (-1) 1) :
    StrictMonoOn (fun x : ℝ => (e.toFun (x : ℂ)).re) (Ioi (-2)) := by
  let x : ℝ → ℝ := fun t => Real.exp t - 2
  let F : ℝ → ℝ := fun t => (e.toFun (x t : ℂ)).re
  have hx (t : ℝ) : -2 < x t := by
    dsimp [x]
    linarith [Real.exp_pos t]
  have hxcont : Continuous x := Real.continuous_exp.sub continuous_const
  have hcont : Continuous F := by
    apply Complex.continuous_re.comp
    exact e.holomorphic.continuousOn.comp_continuous
      (Complex.continuous_ofReal.comp hxcont) (fun t => tract_real_mem p δ (hx t))
  have haxis := tract_real_axis_correspondence p δ e
  have hinj : Function.Injective F := by
    intro s t hst
    have hs : (x s : ℂ) ∈ {z : ℂ | -2 < z.re ∧ z.im = 0} := ⟨hx s, rfl⟩
    have ht : (x t : ℂ) ∈ {z : ℂ | -2 < z.re ∧ z.im = 0} := ⟨hx t, rfl⟩
    have he : e.toFun (x s : ℂ) = e.toFun (x t : ℂ) := by
      apply Complex.ext
      · exact hst
      · exact (haxis.mapsTo hs).2.trans (haxis.mapsTo ht).2.symm
    have he' := congrArg Complex.re (haxis.injOn hs ht he)
    have hexp : Real.exp s = Real.exp t := by
      simpa only [Complex.ofReal_re, x, sub_left_inj] using he'
    exact Real.exp_injective hexp
  have hd : HasDerivAt F (deriv e.toFun ((-1 : ℝ) : ℂ)).re 0 := by
    have he : HasDerivAt (fun y : ℝ => (e.toFun (y : ℂ)).re)
        (deriv e.toFun ((-1 : ℝ) : ℂ)).re (-1 : ℝ) := by
      exact (e.holomorphic.differentiableAt
        ((tract_isOpen p δ hδ).mem_nhds (tract_real_mem p δ (by norm_num : -2 < (-1 : ℝ))))
        ).hasDerivAt.real_of_complex
    have hexp : HasDerivAt x 1 0 := by
      simpa only [Real.exp_zero] using (Real.hasDerivAt_exp (0 : ℝ)).sub_const 2
    have hzero : x 0 = -1 := by norm_num [x]
    have he' : HasDerivAt (fun y : ℝ => (e.toFun (y : ℂ)).re)
        (deriv e.toFun ((-1 : ℝ) : ℂ)).re (x 0) := by
      simpa only [hzero] using he
    convert he'.comp 0 hexp using 1 <;> simp only [F, Function.comp_def, mul_one]
  have hmono : StrictMono F := by
    rcases hcont.strictMono_of_inj hinj with h | h
    · exact h
    · exact False.elim ((not_le_of_gt e.positive_derivative)
        (hd.nonpos_of_antitone h.antitone))
  intro a ha b hb hab
  change -2 < a at ha
  change -2 < b at hb
  have ha' : 0 < a + 2 := by linarith
  have hb' : 0 < b + 2 := by linarith
  have hlog : Real.log (a + 2) < Real.log (b + 2) :=
    Real.log_lt_log ha' (by linarith)
  have h := hmono hlog
  simpa only [F, x, Real.exp_log ha', Real.exp_log hb', add_sub_cancel_right] using h

end MaxModulusPoints.TractGeometry
