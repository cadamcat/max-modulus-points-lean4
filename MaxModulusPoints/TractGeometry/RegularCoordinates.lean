module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.CoordinateDensity

/-!
# Points away from the boundary coordinates

The block edges, tunnel heights, and chamber grid heights form countably many
coordinate lines. Their complement is dense and avoids all equality cases in
the decomposition into passage, tunnel, shoulder, chamber, and gap regions.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

def regularCoordinates (p : BlockParameters) : Set ℂ :=
  {z | (∀ n, z.re ≠ blockPosition p n ∧
      z.re ≠ blockPosition p n + 1 / 2 ∧ z.re ≠ blockPosition p n + 1) ∧
    (∀ n, |z.im| ≠ p.tunnelHeight n / 2) ∧
    ∀ n k : ℕ, |z.im| ≠ chamberBase + (k : ℝ) / ((n : ℝ) + 1)}

theorem regularCoordinates_dense (p : BlockParameters) : Dense (regularCoordinates p) := by
  let A : Set ℝ := range (blockPosition p) ∪
    range (fun n => blockPosition p n + 1 / 2) ∪
    range (fun n => blockPosition p n + 1)
  let B : Set ℝ :=
    range (fun i : ℕ × Bool => sideSign i.2 * (p.tunnelHeight i.1 / 2)) ∪
    range (fun i : (ℕ × ℕ) × Bool =>
      sideSign i.2 * (chamberBase + (i.1.2 : ℝ) / ((i.1.1 : ℝ) + 1)))
  have hA : A.Countable :=
    ((countable_range _).union (countable_range _)).union (countable_range _)
  have hB : B.Countable := (countable_range _).union (countable_range _)
  apply (dense_avoiding_coordinates A B hA hB).mono
  rintro z ⟨hzA, hzB⟩
  have hsign (y : ℝ) (hy : |z.im| = y) : ∃ j : Bool, sideSign j * y = z.im := by
    by_cases hz : 0 ≤ z.im
    · refine ⟨true, ?_⟩
      simpa only [sideSign, Bool.true_eq, ite_true, one_mul, abs_of_nonneg hz] using hy.symm
    · refine ⟨false, ?_⟩
      simpa only [sideSign, Bool.false_eq_true, ite_false, neg_one_mul,
        abs_of_neg (lt_of_not_ge hz), neg_neg] using congrArg Neg.neg hy.symm
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact hzA (Or.inl (Or.inl ⟨n, h.symm⟩))
    · intro h
      exact hzA (Or.inl (Or.inr ⟨n, h.symm⟩))
    · intro h
      exact hzA (Or.inr ⟨n, h.symm⟩)
  · intro n h
    obtain ⟨j, hj⟩ := hsign _ h
    exact hzB (Or.inl ⟨(n, j), hj⟩)
  · intro n k h
    obtain ⟨j, hj⟩ := hsign _ h
    exact hzB (Or.inr ⟨((n, k), j), hj⟩)

end MaxModulusPoints.TractGeometry
