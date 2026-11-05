module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.CompactCapture
public import MaxModulusPoints.FiberContinuation.FiniteFibers
public import MaxModulusPoints.FiberContinuation.InverseCoordinates
public import MaxModulusPoints.FiberContinuation.InverseRoots
public import MaxModulusPoints.FiberContinuation.LogarithmicValues
public import MaxModulusPoints.FiberContinuation.SphericalInverseRoots
public import MaxModulusPoints.FiberContinuation.ValueCoordinates

/-!
# Exact finite common-power families

Compact capture and local power coordinates enumerate every nearby physical
pair at the same common-power parameter. Indices may repeat physical pairs.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

/-- A finite physical family with exact nearby capture in a spherical value chart. -/
structure CommonPowerFamily {f : ℂ → ℂ} (d : NormalizedFunction f)
    (s : ℂ) (p : OnePoint ℂ) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  index : Type
  finite_index : Finite index
  pair : index → ℂ → ℂ × ℂ
  analytic_pair : ∀ i, AnalyticAt ℂ (pair i) 0
  central_pair : ∀ i, pair i 0 ∈ physicalFiber d s p
  central_capture : ∀ v ∈ physicalFiber d s p, ∃ i, pair i 0 = v
  radius : ℝ
  radius_pos : 0 < radius
  neighborhood : Set (ℂ × OnePoint ℂ)
  open_neighborhood : IsOpen neighborhood
  center_mem : (s, p) ∈ neighborhood
  forward : ∀ i t, t ∈ ball 0 radius →
    pair i t ∈ physicalFiber d ((pair i t).1 * (pair i t).2)
      (centeredValue p (t ^ exponent))
  capture : ∀ y ∈ neighborhood, ∀ t ∈ ball 0 radius,
    centeredValue p (t ^ exponent) = y.2 →
      ∀ v ∈ physicalFiber d y.1 y.2, ∃ i, pair i t = v

/-- Every target away from the omitted value has an exact finite physical family,
including targets over infinity and targets with empty central fiber. -/
theorem exists_common_power_family {f : ℂ → ℂ} (d : NormalizedFunction f)
    {s : ℂ} (hs : s ≠ 0) (p : OnePoint ℂ)
    (hp : p ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)) :
    Nonempty (CommonPowerFamily d s p) := by
  classical
  let I := physicalFiber d s p
  letI : Fintype I := (finite_physicalFiber d hs p hp).fintype
  have hAchart (i : I) := exists_logarithmic_power_coordinate d.entire d.at_zero
    d.nonconstant d.multiplicity i.property.2.1
  have hBchart (i : I) := exists_logarithmic_power_coordinate
    (entire_reflected d.entire) (reflected_zero_ne d.at_zero)
    (nonconstant_reflected d.nonconstant) d.multiplicity i.property.2.2
  choose cA hcA0 hcArep using hAchart
  choose cB hcB0 hcBrep using hBchart
  let orders : I × Bool → ℕ := fun ib => if ib.2 then (cA ib.1).order else (cB ib.1).order
  have horders : ∀ ib, 0 < orders ib := by
    rintro ⟨i, b⟩
    cases b <;> simp only [orders, Bool.false_eq_true, ite_false, ite_true]
    · exact (cB i).order_pos
    · exact (cA i).order_pos
  obtain ⟨N, hN, hcommon⟩ := exists_common_power orders horders
  choose k hkpos hkN using hcommon
  have hNA (i : I) : N = k (i, true) * (cA i).order := by simpa [orders] using hkN (i, true)
  have hNB (i : I) : N = k (i, false) * (cB i).order := by simpa [orders] using hkN (i, false)
  have hAfamily (i : I) := exists_exact_spherical_inverse_family (cA i) (hcA0 i)
    (logarithmicValue d.multiplicity d.g) p (hcArep i) (hkpos (i, true))
  have hBfamily (i : I) := exists_exact_spherical_inverse_family (cB i) (hcB0 i)
    (logarithmicValue d.multiplicity (reflected d.g)) p (hcBrep i) (hkpos (i, false))
  choose UA δA hUA haA hδA hexactA using hAfamily
  choose UB δB hUB haB hδB hexactB using hBfamily
  have hparams : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i : I,
      t ∈ ball 0 (δA i) ∧ t ∈ ball 0 (δB i) := by
    apply eventually_all.mpr
    intro i
    exact Filter.Eventually.and (ball_mem_nhds 0 (hδA i)) (ball_mem_nhds 0 (hδB i))
  obtain ⟨δ, hδ, hsmall⟩ := nhds_basis_ball.eventually_iff.mp hparams
  let O : Set (ℂ × ℂ) := ⋃ i : I, UA i ×ˢ UB i
  have hO : IsOpen O := isOpen_iUnion (fun i => (hUA i).prod (hUB i))
  have hcover : physicalFiber d s p ⊆ O := by
    intro v hv
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, haA ⟨v, hv⟩, haB ⟨v, hv⟩⟩
  obtain ⟨W, hW, hcenter, hcapture⟩ := exists_neighborhood_capturing_fiber d s p hp O hO hcover
  let J := Σ i : I, PowerRootIndex (cA i).order × PowerRootIndex (cB i).order
  let P : J → ℂ → ℂ × ℂ := fun j t =>
    (inverseRoot (cA j.1) (k (j.1, true)) j.2.1 t,
      inverseRoot (cB j.1) (k (j.1, false)) j.2.2 t)
  have hP0 (j : J) : P j 0 = j.1.val := by
    apply Prod.ext
    · exact inverseRoot_center (cA j.1) (hkpos (j.1, true)) j.2.1
    · exact inverseRoot_center (cB j.1) (hkpos (j.1, false)) j.2.2
  refine ⟨{
    exponent := N
    exponent_pos := hN
    index := J
    finite_index := inferInstance
    pair := P
    analytic_pair := fun j => (analyticAt_inverseRoot (cA j.1) (hkpos (j.1, true)) j.2.1).prod
      (analyticAt_inverseRoot (cB j.1) (hkpos (j.1, false)) j.2.2)
    central_pair := fun j => hP0 j ▸ j.1.property
    central_capture := ?_
    radius := δ
    radius_pos := hδ
    neighborhood := W
    open_neighborhood := hW
    center_mem := hcenter
    forward := ?_
    capture := ?_ }⟩
  · intro v hv
    let i : I := ⟨v, hv⟩
    let ζA : PowerRootIndex (cA i).order :=
      ⟨1, Polynomial.one_mem_nthRootsFinset (cA i).order_pos⟩
    let ζB : PowerRootIndex (cB i).order :=
      ⟨1, Polynomial.one_mem_nthRootsFinset (cB i).order_pos⟩
    exact ⟨⟨i, ζA, ζB⟩, hP0 ⟨i, ζA, ζB⟩⟩
  · intro j t ht
    have hAmem : inverseRoot (cA j.1) (k (j.1, true)) j.2.1 t ∈
        {z ∈ UA j.1 | logarithmicValue d.multiplicity d.g z =
          centeredValue p (t ^ (k (j.1, true) * (cA j.1).order))} := by
      rw [hexactA j.1 t (hsmall ht j.1).1]
      exact mem_range_self j.2.1
    have hBmem : inverseRoot (cB j.1) (k (j.1, false)) j.2.2 t ∈
        {z ∈ UB j.1 | logarithmicValue d.multiplicity (reflected d.g) z =
          centeredValue p (t ^ (k (j.1, false) * (cB j.1).order))} := by
      rw [hexactB j.1 t (hsmall ht j.1).2]
      exact mem_range_self j.2.2
    exact ⟨rfl, by simpa only [← hNA j.1] using hAmem.2,
      by simpa only [← hNB j.1] using hBmem.2⟩
  · intro y hy t ht hvalue v hv
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcapture y hy hv)
    have hAmem : v.1 ∈ {z ∈ UA i | logarithmicValue d.multiplicity d.g z =
        centeredValue p (t ^ (k (i, true) * (cA i).order))} :=
      ⟨hi.1, by rw [← hNA i]; exact hv.2.1.trans hvalue.symm⟩
    have hBmem : v.2 ∈ {z ∈ UB i | logarithmicValue d.multiplicity (reflected d.g) z =
        centeredValue p (t ^ (k (i, false) * (cB i).order))} :=
      ⟨hi.2, by rw [← hNB i]; exact hv.2.2.trans hvalue.symm⟩
    rw [hexactA i t (hsmall ht i).1] at hAmem
    rw [hexactB i t (hsmall ht i).2] at hBmem
    obtain ⟨ζA, hζA⟩ := hAmem
    obtain ⟨ζB, hζB⟩ := hBmem
    exact ⟨⟨i, ζA, ζB⟩, Prod.ext hζA hζB⟩

end MaxModulusPoints.FiberContinuation
