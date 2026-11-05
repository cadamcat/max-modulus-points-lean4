module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral

/-!
# Compact modifications of improper Cauchy integrals

Changing a contour on a bounded parameter interval changes the improper
Cauchy integral by exactly the corresponding finite integral. The common
infinite tails cancel. Agreement on the open tails also implies agreement
of their derivatives, without any assumption at the endpoints.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The difference produced by a compact contour modification is a finite
Cauchy integral. Endpoint derivatives need not match. -/
theorem cauchyIntegral_sub_of_compact_modification {γ η : ℝ → ℂ} {g : ℂ → ℂ}
    (hγ : IsProperMap γ) (hη : IsProperMap η)
    (hργ : Integrable (fun t : ℝ ↦ g (γ t) * deriv γ t))
    (hρη : Integrable (fun t : ℝ ↦ g (η t) * deriv η t))
    {a b : ℝ} (hab : a ≤ b) (hagree : ∀ t ∉ Icc a b, γ t = η t)
    {z : ℂ} (hzγ : z ∉ range γ) (hzη : z ∉ range η) :
    cauchyIntegral γ (fun t ↦ g (γ t) * deriv γ t) z -
        cauchyIntegral η (fun t ↦ g (η t) * deriv η t) z =
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t in a..b,
        g (γ t) * deriv γ t / (γ t - z) - g (η t) * deriv η t / (η t - z) := by
  let F : ℝ → ℂ := fun t ↦ g (γ t) * deriv γ t / (γ t - z)
  let G : ℝ → ℂ := fun t ↦ g (η t) * deriv η t / (η t - z)
  have hF : Integrable F := (cauchyIntegral_converges_of_integrable hγ hργ hzγ).1
  have hG : Integrable G := (cauchyIntegral_converges_of_integrable hη hρη hzη).1
  have hzero (t : ℝ) (ht : t ∉ Icc a b) : F t - G t = 0 := by
    have heq : γ =ᶠ[𝓝 t] η := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds ht] with s hs using hagree s hs
    dsimp only [F, G]
    rw [hagree t ht, heq.deriv_eq, sub_self]
  have hlocal : (∫ t in a..b, F t - G t) = ∫ t : ℝ, F t - G t := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  change (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ t : ℝ, F t) -
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ t : ℝ, G t) =
    (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ t in a..b, F t - G t
  rw [← mul_sub, ← integral_sub hF hG, hlocal]

#print axioms cauchyIntegral_sub_of_compact_modification

end MaxModulusPoints.CauchyApproximation
