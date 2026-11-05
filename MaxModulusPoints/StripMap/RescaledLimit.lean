module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.StripMap.Compactness
public import MaxModulusPoints.StripMap.ExponentialChart
public import MaxModulusPoints.StripMap.Geometry
public import MaxModulusPoints.StripMap.LimitIdentification
public import MaxModulusPoints.StripMap.Rescaling

/-!
# The rescaled exponential limit

Every sequence of normalized translates has a locally uniform subsequential
limit. For escaping translation parameters, the limit is uniquely the
exponential. The subsequence criterion for convergence therefore gives the
limit of the entire real-parameter family, together with its derivatives.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set Filter Metric
open MaxModulusPoints.Blueprint
open scoped Topology UniformConvergence

theorem normalized_equivalence_rescaled_limit (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) :
    TendstoLocallyUniformlyOn (rescaledMap e)
      (fun z : ℂ => Complex.exp (Real.pi * z)) atTop strip := by
  change TendstoLocallyUniformlyOn (rescaledMap e) stripExp atTop strip
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_strip).mpr
  intro K hK hcompact
  let F : ℝ → ℂ →ᵤ[{K}] ℂ := fun b => UniformOnFun.ofFun {K} (rescaledMap e b)
  have hF : Tendsto F atTop (𝓝 (UniformOnFun.ofFun {K} stripExp)) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro b hb
    obtain ⟨f, φ, hφ, hc, _, _⟩ := rescaledMap_subsequence e he0 hepos hereal b
    have heq := rescaledMap_limit_eq_stripExp e he0 hepos hereal (hb.comp hφ.tendsto_atTop) hc
    have hcs := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_strip).mp
      (hc.congr_right heq) K hK hcompact
    refine ⟨φ, UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr ?_⟩
    intro S hS
    have hSK : S = K := mem_singleton_iff.mp hS
    subst S
    simpa only [F, UniformOnFun.toFun_ofFun, Function.comp_def] using hcs
  simpa only [F, UniformOnFun.toFun_ofFun, Function.comp_def] using
    (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hF) K (mem_singleton K)

theorem normalized_equivalence_rescaled_derivative_limit (e : ConformalEquivalence strip target)
    (he0 : e.toFun 0 = 1) (hepos : 0 < (deriv e.toFun 0).re)
    (hereal : (deriv e.toFun 0).im = 0) :
    TendstoLocallyUniformlyOn (fun b : ℝ => deriv (rescaledMap e b))
      (fun z : ℂ => (Real.pi : ℂ) * Complex.exp (Real.pi * z)) atTop strip :=
  rescaled_derivative_limit_of_limit e
    (normalized_equivalence_rescaled_limit e he0 hepos hereal)

end MaxModulusPoints.StripMap
