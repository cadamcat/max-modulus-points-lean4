module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Density away from countably many coordinate lines

Countable subsets of the real line have dense complements. Taking their
product gives dense complex points avoiding both prescribed coordinate sets.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set

theorem dense_avoiding_coordinates (A B : Set ℝ) (hA : A.Countable)
    (hB : B.Countable) : Dense {z : ℂ | z.re ∉ A ∧ z.im ∉ B} := by
  have hd : Dense (Aᶜ ×ˢ Bᶜ) := (hA.dense_compl ℝ).prod (hB.dense_compl ℝ)
  exact hd.preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap

end MaxModulusPoints.TractGeometry
