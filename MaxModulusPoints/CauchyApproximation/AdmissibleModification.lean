module

public import TauCeti.Analysis.Contour.PiecewiseC1On
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import MaxModulusPoints.CauchyApproximation.Convergence

/-!
# Admissibility of compact contour modifications

A continuous replacement of a bounded contour arc preserves properness.
If the replacement arc is piecewise C¹ and the integrand is continuous along
it, its density is integrable on that arc. The unchanged tails retain the
integrability of the original density. These facts supply the analytic
hypotheses needed when deforming an improper Cauchy contour locally.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open TauCeti.Contour
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- A continuous compact modification with a piecewise C¹ replacement arc
preserves properness and integrability of the contour density. No matching
of the derivatives at the splice endpoints is required. -/
theorem proper_and_integrable_of_compact_modification
    {γ η : ℝ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (hγ : IsProperMap γ) (hη : Continuous η)
    (hργ : Integrable (fun t : ℝ ↦ g (γ t) * deriv γ t))
    {a b : ℝ} (hab : a ≤ b) (hηpc : IsPiecewiseC1On η a b)
    (hg : ContinuousOn g U) (hηU : MapsTo η (uIcc a b) U)
    (hagree : ∀ t ∉ Icc a b, γ t = η t) :
    IsProperMap η ∧ Integrable (fun t : ℝ ↦ g (η t) * deriv η t) := by
  have heq : γ =ᶠ[cocompact ℝ] η := by
    filter_upwards [isCompact_Icc.compl_mem_cocompact] with t ht using hagree t ht
  have hproper : IsProperMap η :=
    isProperMap_iff_tendsto_cocompact.2
      ⟨hη, (isProperMap_iff_tendsto_cocompact.1 hγ).2.congr' heq⟩
  have hderiv : IntegrableOn (deriv η) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hηpc.intervalIntegrable_deriv
  have hcomp : ContinuousOn (fun t ↦ g (η t)) (Icc a b) := by
    apply hg.comp hη.continuousOn
    intro t ht
    exact hηU (by simpa only [uIcc_of_le hab] using ht)
  have hlocal : IntegrableOn (fun t ↦ g (η t) * deriv η t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hcomp hderiv isCompact_Icc
  have htail : IntegrableOn (fun t ↦ g (η t) * deriv η t) (Icc a b)ᶜ := by
    apply hργ.integrableOn.congr_fun ?_ measurableSet_Icc.compl
    intro t ht
    have heqnhds : γ =ᶠ[𝓝 t] η := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with s hs using hagree s hs
    dsimp only
    rw [hagree t ht, heqnhds.deriv_eq]
  refine ⟨hproper, ?_⟩
  rw [← integrableOn_univ, ← union_compl_self (Icc a b)]
  exact integrableOn_union.2 ⟨hlocal, htail⟩

#print axioms proper_and_integrable_of_compact_modification

end MaxModulusPoints.CauchyApproximation
