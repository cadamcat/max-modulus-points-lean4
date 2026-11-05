module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Order.Filter.Finite
public import MaxModulusPoints.Blueprint.Data

/-!
# Stabilizing finite physical families

Isolated zeros stabilize every comparison in a finite family of analytic germs.
Cardinalities are taken after identifying equal physical pairs, so repeated
indices do not affect the count.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

universe u v w

/-- All comparisons in a finite analytic family agree with their germ comparison
on one common punctured disk. -/
theorem analytic_comparisons_stabilize {ι : Type u} [Finite ι]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F G : ι → ℂ → E) (hF : ∀ i, AnalyticAt ℂ (F i) 0)
    (hG : ∀ i, AnalyticAt ℂ (G i) 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i t, t ∈ ball 0 δ → t ≠ 0 →
      (F i t = G i t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), F i u = G i u) := by
  have hlocal : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
      (F i t = G i t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), F i u = G i u) := by
    intro i
    rcases (hF i).eventually_eq_or_eventually_ne (hG i) with heq | hne
    · filter_upwards [heq] with t ht
      exact fun _ => ⟨fun _ => heq, fun _ => ht⟩
    · have hnot : ¬ ∀ᶠ u in 𝓝 (0 : ℂ), F i u = G i u := by
        intro heq
        have hfalse := (heq.filter_mono nhdsWithin_le_nhds).and hne
        exact hfalse.exists.elim fun _ h => h.2 h.1
      filter_upwards [eventually_nhdsWithin_iff.mp hne] with t ht hzero
      exact ⟨fun heq => False.elim (ht hzero heq), fun heq => False.elim (hnot heq)⟩
  obtain ⟨δ, hδ, hcomp⟩ := nhds_basis_ball.eventually_iff.mp
    (eventually_all.mpr hlocal)
  exact ⟨δ, hδ, fun i t ht hzero => hcomp ht i hzero⟩

/-- A finite family's equality relation is constant on a punctured disk.
An equality there also implies equality of the central physical values. -/
theorem analytic_family_stabilizes {ι : Type u} [Finite ι]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : ι → ℂ → E) (hP : ∀ i, AnalyticAt ℂ (P i) 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j t, t ∈ ball 0 δ → t ≠ 0 →
      (P i t = P j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), P i u = P j u) ∧
      (P i t = P j t → P i 0 = P j 0) := by
  obtain ⟨δ, hδ, hcomp⟩ := analytic_comparisons_stabilize
    (fun ij : ι × ι => P ij.1) (fun ij => P ij.2)
    (fun ij => hP ij.1) (fun ij => hP ij.2)
  refine ⟨δ, hδ, ?_⟩
  intro i j t ht hzero
  have h := hcomp (i, j) t ht hzero
  exact ⟨h, fun heq => Filter.EventuallyEq.eq_of_nhds (h.mp heq)⟩

/-- If equality in a second image implies equality in the first, the first
image has no larger cardinality. -/
theorem encard_image_le_of_kernel_imp {ι : Type u} {α : Type v} {β : Type w}
    (P : ι → α) (Q : ι → β) (I : Set ι)
    (h : ∀ i ∈ I, ∀ j ∈ I, Q i = Q j → P i = P j) :
    (P '' I).encard ≤ (Q '' I).encard := by
  classical
  let r : (P '' I) → ι := fun x => x.property.choose
  have hrI (x : P '' I) : r x ∈ I := x.property.choose_spec.1
  have hrP (x : P '' I) : P (r x) = x := x.property.choose_spec.2
  let e : (P '' I) → (Q '' I) := fun x => ⟨Q (r x), r x, hrI x, rfl⟩
  exact ENat.card_le_card_of_injective (f := e) (by
    intro x y heq
    apply Subtype.ext
    calc
      (x : α) = P (r x) := (hrP x).symm
      _ = P (r y) := h _ (hrI x) _ (hrI y) (congrArg Subtype.val heq)
      _ = (y : α) := hrP y)

/-- Equal kernels give equal counts of distinct physical values. -/
theorem encard_image_eq_of_same_kernel {ι : Type u} {α : Type v} {β : Type w}
    (P : ι → α) (Q : ι → β) (I : Set ι)
    (h : ∀ i ∈ I, ∀ j ∈ I, P i = P j ↔ Q i = Q j) :
    (P '' I).encard = (Q '' I).encard := by
  apply le_antisymm
  · exact encard_image_le_of_kernel_imp P Q I fun i hi j hj => (h i hi j hj).mpr
  · exact encard_image_le_of_kernel_imp Q P I fun i hi j hj => (h i hi j hj).mp

/-- Forward validity and capture at the same parameter give the exact physical
fiber, rather than a list counted with multiplicity. -/
theorem physicalFiber_eq_image {f : ℂ → ℂ} (d : NormalizedFunction f)
    {ι : Type u} (P : ι → ℂ × ℂ) (q : OnePoint ℂ) (s : ℂ)
    (hvalid : ∀ i, P i ∈ physicalFiber d ((P i).1 * (P i).2) q)
    (hcapture : ∀ v, v ∈ physicalFiber d s q → ∃ i, P i = v) :
    physicalFiber d s q = P '' {i | (P i).1 * (P i).2 = s} := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, rfl⟩ := hcapture v hv
    exact ⟨i, hv.1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    change (P i).1 * (P i).2 = s at hi
    rw [← hi]
    exact hvalid i

/-- Stabilized product filters and physical equalities give constant distinct
fiber counts along a punctured branch. -/
theorem physical_counts_eq_of_stabilized_comparisons {ι : Type u}
    (P Q : ι → ℂ × ℂ) (j : ι)
    (hproduct : ∀ i, (P i).1 * (P i).2 = (P j).1 * (P j).2 ↔
      (Q i).1 * (Q i).2 = (Q j).1 * (Q j).2)
    (hpairs : ∀ i k, P i = P k ↔ Q i = Q k) :
    (P '' {i | (P i).1 * (P i).2 = (P j).1 * (P j).2}).encard =
      (Q '' {i | (Q i).1 * (Q i).2 = (Q j).1 * (Q j).2}).encard := by
  have hI : {i | (P i).1 * (P i).2 = (P j).1 * (P j).2} =
      {i | (Q i).1 * (Q i).2 = (Q j).1 * (Q j).2} := by
    ext i
    exact hproduct i
  rw [hI]
  exact encard_image_eq_of_same_kernel P Q _ fun i _ k _ => hpairs i k

end MaxModulusPoints.FiberContinuation
