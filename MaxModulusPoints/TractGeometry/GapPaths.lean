module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.RealAxis
public import MaxModulusPoints.TractGeometry.Walls

/-!
# Vertical paths between the blocks

A vertical line outside all closed block intervals meets no walls. Within the
ambient strip it therefore joins each point to the real axis inside the tract.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_gap_joined (p : BlockParameters) (δ : GateIndex → ℝ) {z : ℂ}
    (hx : -2 < z.re) (hy : |z.im| < Real.pi / 2)
    (hgap : ∀ n, z.re < blockPosition p n ∨ blockPosition p n + 1 < z.re) :
    JoinedIn (tract p δ) z (z.re : ℂ) := by
  let f : ℝ → ℂ := fun t => ⟨z.re, (1 - t) * z.im⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk ((continuous_const.sub continuous_id).mul continuous_const))
  refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
  · apply Complex.ext <;> simp [f]
  · apply Complex.ext <;> simp [f]
  · rintro w ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have ht1 : 1 - t ≤ 1 := by linarith [ht.1]
    have habs : |(1 - t) * z.im| ≤ |z.im| := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    refine Or.inl (Or.inl ⟨⟨hx, lt_of_le_of_lt habs hy⟩, ?_⟩)
    intro hw
    rcases mem_iUnion.mp hw with ⟨n, hn⟩
    have hb := blockWalls_re_bounds p n hn
    change blockPosition p n ≤ z.re ∧ z.re ≤ blockPosition p n + 1 at hb
    rcases hgap n with hl | hr <;> linarith [hb.1, hb.2]

end MaxModulusPoints.TractGeometry
