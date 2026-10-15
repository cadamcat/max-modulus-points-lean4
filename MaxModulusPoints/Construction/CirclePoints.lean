import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Set.Card
import MaxModulusPoints.Construction.Maxima
/-!

# From equal slice maxima to maximum-modulus points

The last step of Pardo-Simón–Sixsmith, Corollary 4.6, compares equal maxima
on compact starred segments with the deleted endpieces and the complement of the
exponentiated tract. The resulting points are global maxima on the entire circle.
-/

namespace MaxModulusPoints.Construction

open Set Filter
open scoped Topology

universe u

noncomputable section

/-- Full vertical slices and their compact starred subsegments, as in
Proposition 4.4 and the proof of Corollary 4.6. -/
structure VerticalSlices (ι : Type u) (V : Set ℂ) (x : ℝ) where
  slice : ι → Set ℂ
  star : ι → Set ℂ
  star_compact : ∀ i, IsCompact (star i)
  star_nonempty : ∀ i, (star i).Nonempty
  star_subset : ∀ i, star i ⊆ slice i
  slice_subset : ∀ i, slice i ⊆ V
  slice_re : ∀ i z, z ∈ slice i → z.re = x
  slice_cover : ∀ z ∈ V, z.re = x → ∃ i, z ∈ slice i
  star_disjoint : Pairwise (fun i j => Disjoint (star i) (star j))

/-- The analytic estimates needed after balancing: Proposition 4.4 controls
the deleted endpieces, and Theorem 2.2 controls the complement of the tract image. -/
structure SliceControl {ι : Type u} {V : Set ℂ} {x : ℝ}
    (D : VerticalSlices ι V x) (f : C(ℂ, ℂ)) (B : ℝ) : Prop where
  endpiece : ∀ i z, z ∈ D.slice i \ D.star i → logModulus f z ≤ B
  outside : ∀ w : ℂ, ‖w‖ = Real.exp x → w ∉ Complex.exp '' V → ‖f w‖ ≤ B

/-- A strip of width one exponential period contains no two distinct
points with the same exponential, with one boundary excluded. -/
theorem exp_injOn_of_strip {V : Set ℂ}
    (hV : ∀ z ∈ V, -Real.pi < z.im ∧ z.im ≤ Real.pi) :
    InjOn Complex.exp V := by
  intro z hz w hw heq
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi (hV z hz).1 (hV z hz).2
    (hV w hw).1 (hV w hw).2 heq

/-- Equal maxima on the starred segments bound the whole circle, including
points whose logarithmic lifts lie outside every translate of the tract. -/
theorem VerticalSlices.circle_bound {ι : Type u} {V : Set ℂ} {x : ℝ}
    (D : VerticalSlices ι V x) (f : C(ℂ, ℂ)) {B L : ℝ}
    (hBL : B < L) (C : SliceControl D f B)
    (hequal : ∀ i, compactMaximum (logModulus f) (D.star i) = L) :
    ∀ w : ℂ, ‖w‖ = Real.exp x → ‖f w‖ ≤ L := by
  intro w hw
  by_cases hwV : w ∈ Complex.exp '' V
  · obtain ⟨z, hzV, rfl⟩ := hwV
    have hzre : z.re = x := Real.exp_injective (by
      simpa only [Complex.norm_exp] using hw)
    obtain ⟨i, hzi⟩ := D.slice_cover z hzV hzre
    by_cases hzstar : z ∈ D.star i
    · calc
        ‖f (Complex.exp z)‖ ≤ compactMaximum (logModulus f) (D.star i) :=
          le_compactMaximum (D.star_compact i) (continuous_logModulus f).continuousOn hzstar
        _ = L := hequal i
    · exact (C.endpiece i z ⟨hzi, hzstar⟩).trans hBL.le
  · exact (C.outside w hw hwV).trans hBL.le

/-- One point on each starred slice gives distinct global maximum-modulus
points. Injectivity of the exponential on the tract prevents identifications. -/
theorem VerticalSlices.maximum_points {ι : Type u} {V : Set ℂ} {x : ℝ}
    (D : VerticalSlices ι V x) (f : C(ℂ, ℂ)) (hinj : InjOn Complex.exp V)
    {B L : ℝ} (hBL : B < L) (C : SliceControl D f B)
    (hequal : ∀ i, compactMaximum (logModulus f) (D.star i) = L) :
    ∃ p : ι → ℂ, Function.Injective p ∧ ∀ i,
      ‖p i‖ = Real.exp x ∧ ‖f (p i)‖ = L ∧
        ∀ w : ℂ, ‖w‖ = Real.exp x → ‖f w‖ ≤ ‖f (p i)‖ := by
  classical
  have hchoose (i : ι) : ∃ z ∈ D.star i, logModulus f z = L := by
    obtain ⟨z, hz, hmax⟩ := exists_compactMaximum (D.star_compact i)
      (D.star_nonempty i) (continuous_logModulus f).continuousOn
    exact ⟨z, hz, hmax.trans (hequal i)⟩
  choose z hz hmax using hchoose
  have hzV (i : ι) : z i ∈ V := D.slice_subset i (D.star_subset i (hz i))
  refine ⟨fun i => Complex.exp (z i), ?_, ?_⟩
  · intro i j hij
    have hzij : z i = z j := hinj (hzV i) (hzV j) hij
    by_contra hne
    have hd := D.star_disjoint hne
    exact disjoint_left.mp hd (hz i) (hzij ▸ hz j)
  · intro i
    refine ⟨?_, hmax i, ?_⟩
    · rw [Complex.norm_exp, D.slice_re i (z i) (D.star_subset i (hz i))]
    · intro w hw
      change ‖f w‖ ≤ logModulus f (z i)
      rw [hmax i]
      exact D.circle_bound f hBL C hequal w hw

/-- Counting the injective family gives the number of slices as a lower
bound for the exact global maximum set, using extended natural cardinality. -/
theorem VerticalSlices.encard_maximum_points {ι : Type u} [Fintype ι]
    {V : Set ℂ} {x : ℝ} (D : VerticalSlices ι V x) (f : C(ℂ, ℂ))
    (hinj : InjOn Complex.exp V) {B L : ℝ} (hBL : B < L) (C : SliceControl D f B)
    (hequal : ∀ i, compactMaximum (logModulus f) (D.star i) = L) :
    (Fintype.card ι : ℕ∞) ≤
      {z : ℂ | ‖z‖ = Real.exp x ∧
        ∀ w : ℂ, ‖w‖ = Real.exp x → ‖f w‖ ≤ ‖f z‖}.encard := by
  obtain ⟨p, hinjective, hp⟩ := D.maximum_points f hinj hBL C hequal
  have hsubset : Set.range p ⊆ {z : ℂ | ‖z‖ = Real.exp x ∧
      ∀ w : ℂ, ‖w‖ = Real.exp x → ‖f w‖ ≤ ‖f z‖} := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(hp i).1, (hp i).2.2⟩
  calc
    (Fintype.card ι : ℕ∞) = (Set.range p).encard := by
      rw [hinjective.encard_range, ENat.card_eq_coe_fintype_card]
    _ ≤ _ := encard_le_encard hsubset

/-- The passage and `2n` chambers in Corollary 4.6 supply `2n+1` distinct
maximum-modulus points, with no finiteness assumption on the whole maximum set. -/
theorem VerticalSlices.two_mul_add_one_le {n : ℕ} {V : Set ℂ} {x : ℝ}
    (D : VerticalSlices (Fin (2 * n + 1)) V x) (f : C(ℂ, ℂ))
    (hinj : InjOn Complex.exp V) {B L : ℝ} (hBL : B < L) (C : SliceControl D f B)
    (hequal : ∀ i, compactMaximum (logModulus f) (D.star i) = L) :
    ((2 * n + 1 : ℕ) : ℕ∞) ≤
      {z : ℂ | ‖z‖ = Real.exp x ∧
        ∀ w : ℂ, ‖w‖ = Real.exp x → ‖f w‖ ≤ ‖f z‖}.encard := by
  simpa only [Fintype.card_fin] using D.encard_maximum_points f hinj hBL C hequal

/-- Escaping logarithmic radii with growing exact counts give the cofinal
unboundedness assertion in Theorem 1.1. -/
theorem unbounded_circle_counts_of_sequence (f : ℂ → ℂ) (x : ℕ → ℝ)
    (hx : Tendsto x atTop atTop)
    (hcount : ∀ n : ℕ, (n : ℕ∞) ≤
      {z : ℂ | ‖z‖ = Real.exp (x n) ∧
        ∀ w : ℂ, ‖w‖ = Real.exp (x n) → ‖f w‖ ≤ ‖f z‖}.encard) :
    ∀ (N : ℕ) (R : ℝ), ∃ r : ℝ, 0 < r ∧ R < r ∧ (N : ℕ∞) ≤
      {z : ℂ | ‖z‖ = r ∧ ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}.encard := by
  intro N R
  have hexp : Tendsto (fun n => Real.exp (x n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hx
  have hlarge : ∀ᶠ n in atTop, R < Real.exp (x n) :=
    hexp.eventually (eventually_gt_atTop R)
  obtain ⟨n, hn, hRn⟩ := (eventually_ge_atTop N |>.and hlarge).exists
  refine ⟨Real.exp (x n), Real.exp_pos _, hRn, ?_⟩
  exact (by exact_mod_cast hn : (N : ℕ∞) ≤ (n : ℕ∞)).trans (hcount n)

#print axioms VerticalSlices.circle_bound
#print axioms VerticalSlices.maximum_points
#print axioms VerticalSlices.encard_maximum_points
#print axioms VerticalSlices.two_mul_add_one_le
#print axioms unbounded_circle_counts_of_sequence

end

end MaxModulusPoints.Construction
