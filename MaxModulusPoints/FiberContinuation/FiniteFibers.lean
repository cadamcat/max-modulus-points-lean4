import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Challenge
import MaxModulusPoints.FiberContinuation.CompactCapture
import MaxModulusPoints.FiberContinuation.LogarithmicValues
/-!
# Finite physical fibers

The first coordinate embeds each nonzero-product fiber into the zeros of one
nonzero entire function. Compact capture and isolated zeros give finiteness.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter
open scoped Topology
open MaxModulusPoints.Blueprint

/-- The zeros of a nonzero entire function in a compact set form a finite set. -/
theorem finite_zeros_on_compact {g : ℂ → ℂ} (hg : Entire g) (hg0 : g 0 ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) : {z ∈ K | g z = 0}.Finite := by
  by_contra hinfinite
  obtain ⟨a, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinfinite hK
    (fun _ hz => hz.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] a, g z = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono (fun _ hz => hz.2)
  exact not_eventually_zero_of_entire hg hg0 a
    ((hg.analyticAt a).frequently_zero_iff_eventually_zero.mp hfreq)

/-- A nonzero product determines a physical pair from its first coordinate. -/
theorem injOn_fst_physicalFiber {f : ℂ → ℂ} (d : NormalizedFunction f)
    {s : ℂ} (hs : s ≠ 0) (q : OnePoint ℂ) : InjOn Prod.fst (physicalFiber d s q) := by
  intro v hv w hw heq
  have hv0 : v.1 ≠ 0 := by
    intro hzero
    apply hs
    rw [← hv.1, hzero, zero_mul]
  apply Prod.ext heq
  apply mul_left_cancel₀ hv0
  calc
    v.1 * v.2 = s := hv.1
    _ = w.1 * w.2 := hw.1.symm
    _ = v.1 * w.2 := by rw [heq]

/-- Every nonzero-product physical fiber away from the omitted value is finite,
including the fiber over infinity. -/
theorem finite_physicalFiber {f : ℂ → ℂ} (d : NormalizedFunction f)
    {s : ℂ} (hs : s ≠ 0) (q : OnePoint ℂ)
    (hq : q ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)) :
    (physicalFiber d s q).Finite := by
  apply Set.Finite.of_finite_image (f := Prod.fst) (hi := injOn_fst_physicalFiber d hs q)
  have hK : IsCompact (Prod.fst '' physicalFiber d s q) :=
    (isCompact_physicalFiber d s q hq).image continuous_fst
  cases q using OnePoint.rec with
  | infty =>
    apply (finite_zeros_on_compact d.entire d.at_zero _ hK).subset
    rintro z ⟨v, hv, rfl⟩
    refine ⟨mem_image_of_mem Prod.fst hv, ?_⟩
    by_contra hzero
    have hvalue := hv.2.1
    simp [logarithmicValue, hzero] at hvalue
  | coe q =>
    have hqm : q ≠ (d.multiplicity : ℂ) := by
      intro heq
      exact hq (congrArg (fun z : ℂ => (z : OnePoint ℂ)) heq)
    let H : ℂ → ℂ := fun z => z * deriv d.g z - (q - (d.multiplicity : ℂ)) * d.g z
    have hH : Entire H := by
      change Differentiable ℂ H
      exact (differentiable_id.mul d.entire.deriv).sub
        ((differentiable_const (q - (d.multiplicity : ℂ))).mul d.entire)
    have hH0 : H 0 ≠ 0 := by
      simpa only [H, zero_mul, zero_sub, ne_eq, neg_eq_zero] using
        mul_ne_zero (sub_ne_zero.mpr hqm) d.at_zero
    apply (finite_zeros_on_compact hH hH0 _ hK).subset
    rintro z ⟨v, hv, rfl⟩
    refine ⟨mem_image_of_mem Prod.fst hv, ?_⟩
    have hgz : d.g v.1 ≠ 0 := by
      intro hzero
      have hvalue := hv.2.1
      simp [logarithmicValue, hzero] at hvalue
    have hfinite : (d.multiplicity : ℂ) + v.1 * deriv d.g v.1 / d.g v.1 = q :=
      OnePoint.coe_injective (by simpa [logarithmicValue, hgz] using hv.2.1)
    have hquot : v.1 * deriv d.g v.1 / d.g v.1 = q - (d.multiplicity : ℂ) :=
      (eq_sub_iff_add_eq').mpr hfinite
    exact sub_eq_zero.mpr ((div_eq_iff hgz).mp hquot)

end MaxModulusPoints.FiberContinuation
