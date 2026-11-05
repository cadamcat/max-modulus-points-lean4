module

public import Mathlib.Analysis.Complex.Liouville
public import MaxModulusPoints.Liminf.Basic

/-!
# `MaxModulusPoints.Liminf.Products`
-/

@[expose] public section

open Filter Topology
open scoped ComplexConjugate

namespace MaxModulusPoints.Liminf

/-- Schwarz reflection of an entire function. -/
def reflected (g : ℂ → ℂ) (z : ℂ) : ℂ := conj (g (conj z))

/-- A reflected product of a nonconstant entire function cannot be constant on the
punctured plane. -/
theorem reflected_product_nonconstant (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hg0 : g 0 ≠ 0) (hgnc : ¬ ∃ c : ℂ, ∀ z, g z = c)
    (s : ℂ) :
    ¬ ∃ c : ℂ, ∀ z, z ≠ 0 → g z * reflected g (s / z) = c := by
  rintro ⟨c, hc⟩
  let u : ℂ → ℂ := fun z => conj (g (conj (s / z)))
  have hInv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0 : ℂ)) := by
    simpa [Metric.cobounded_eq_cocompact] using
      (Filter.tendsto_inv₀_cobounded (α := ℂ))
  have harg : Tendsto (fun z : ℂ => s / z) (cocompact ℂ) (𝓝 (0 : ℂ)) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := s)).mul hInv
  have hreflectDiff : Differentiable ℂ (fun z : ℂ => conj (g (conj z))) := by
    intro z
    have hz : DifferentiableAt ℂ g (conj z) := hg (conj z)
    simpa [Function.comp_def] using hz.conj_conj
  have hreflect : Tendsto u (cocompact ℂ) (𝓝 (star (g 0))) := by
    change Tendsto (fun z : ℂ => conj (g (conj (s / z))))
      (cocompact ℂ) (𝓝 (star (g 0)))
    simpa [Function.comp_def] using
      (hreflectDiff 0).continuousAt.tendsto.comp harg
  have hu0 : star (g 0) ≠ 0 := star_ne_zero.mpr hg0
  have hquot : Tendsto (fun z : ℂ => c / u z) (cocompact ℂ)
      (𝓝 (c / star (g 0))) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := c)).mul ((tendsto_inv₀ hu0).comp hreflect)
  have hu_ne : ∀ᶠ z in cocompact ℂ, u z ≠ 0 :=
    hreflect.eventually (isOpen_ne.mem_nhds hu0)
  have hz_ne : ∀ᶠ z in cocompact ℂ, z ≠ 0 := by
    apply mem_cocompact.mpr
    refine ⟨{(0 : ℂ)}, isCompact_singleton, ?_⟩
    intro z hz
    simpa using hz
  have hEq : g =ᶠ[cocompact ℂ] fun z => c / u z := by
    filter_upwards [hz_ne, hu_ne] with z hz hzu
    have hprod : g z * u z = c := by simpa [u, reflected] using hc z hz
    exact (eq_div_iff hzu).2 hprod
  have hglimit : Tendsto g (cocompact ℂ) (𝓝 (c / star (g 0))) :=
    Tendsto.congr' hEq.symm hquot
  have hgconst := hg.eq_const_of_tendsto_cocompact hglimit
  exact hgnc ⟨c / star (g 0), fun z => by simpa using congrFun hgconst z⟩

end MaxModulusPoints.Liminf
