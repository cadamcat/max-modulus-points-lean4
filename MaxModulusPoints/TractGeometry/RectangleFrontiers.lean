module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.OrderClosed

/-!
# Frontiers of coordinate rectangles

A point lies in the frontier of a closed coordinate rectangle exactly when
it satisfies the coordinate bounds and lies on one of the four sides. The
criterion also holds for empty or degenerate rectangles.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set

theorem rectangle_frontier_bounds (a b c d : ℝ) {z : ℂ}
    (hz : z ∈ frontier {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d}) :
    (a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d) ∧
      (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) := by
  have hclosed : IsClosed {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  refine ⟨hclosed.frontier_subset hz, ?_⟩
  have h₁ := frontier_inter_subset {w : ℂ | a ≤ w.re}
    {w : ℂ | w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} hz
  rcases h₁ with ⟨h, _⟩ | ⟨_, h⟩
  · exact Or.inl ((frontier_le_subset_eq continuous_const Complex.continuous_re h).symm)
  · have h₂ := frontier_inter_subset {w : ℂ | w.re ≤ b}
      {w : ℂ | c ≤ w.im ∧ w.im ≤ d} h
    rcases h₂ with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inr (Or.inl (frontier_le_subset_eq Complex.continuous_re continuous_const h))
    · have h₃ := frontier_inter_subset {w : ℂ | c ≤ w.im} {w : ℂ | w.im ≤ d} h
      rcases h₃ with ⟨h, _⟩ | ⟨_, h⟩
      · exact Or.inr (Or.inr (Or.inl
          ((frontier_le_subset_eq continuous_const Complex.continuous_im h).symm)))
      · exact Or.inr (Or.inr (Or.inr
          (frontier_le_subset_eq Complex.continuous_im continuous_const h)))

theorem rectangle_mem_frontier_iff (a b c d : ℝ) {z : ℂ} :
    z ∈ frontier {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} ↔
      (a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d) ∧
        (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) := by
  constructor
  · exact rectangle_frontier_bounds a b c d
  · rintro ⟨⟨hxl, hxr, hyl, hyu⟩, hside⟩
    let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
    have heq : {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} =
        e ⁻¹' (Icc a b ×ˢ Icc c d) := by
      ext w
      simp [e, and_assoc, and_left_comm]
    rw [heq, ← e.preimage_frontier]
    change (z.re, z.im) ∈ frontier (Icc a b ×ˢ Icc c d)
    simp only [frontier_prod_eq, isClosed_Icc.closure_eq,
      frontier_Icc (hxl.trans hxr), frontier_Icc (hyl.trans hyu),
      mem_union, mem_prod, mem_Icc, mem_insert_iff, mem_singleton_iff]
    rcases hside with h | h | h | h
    · exact Or.inr ⟨Or.inl h, hyl, hyu⟩
    · exact Or.inr ⟨Or.inr h, hyl, hyu⟩
    · exact Or.inl ⟨⟨hxl, hxr⟩, Or.inl h⟩
    · exact Or.inl ⟨⟨hxl, hxr⟩, Or.inr h⟩

end MaxModulusPoints.TractGeometry
