module

public import Mathlib.Tactic.NormNum
public import MaxModulusPoints.Blueprint.Data

/-!
# Reflection symmetry of the chamber and gate tracts

Complex conjugation preserves the passage and tunnel and exchanges the two
chambers and gates at each height.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_star_mem (p : BlockParameters) (δ : GateIndex → ℝ)
    {z : ℂ} (hz : z ∈ tract p δ) : star z ∈ tract p δ := by
  let e : ℂ ≃ₜ ℂ := Complex.conjCLE.toHomeomorph
  have hp (n : ℕ) : e ⁻¹' passage p n = passage p n := by
    ext w
    change (star w ∈ passage p n) ↔ w ∈ passage p n
    simp [passage]
  have ht (n : ℕ) : e ⁻¹' tunnel p n = tunnel p n := by
    ext w
    change (star w ∈ tunnel p n) ↔ w ∈ tunnel p n
    simp [tunnel]
  have hc (i : GateIndex) (j : Bool) : e ⁻¹' chamber p i j = chamber p i (!j) := by
    ext w
    change (star w ∈ chamber p i j) ↔ w ∈ chamber p i (!j)
    cases j <;> simp [chamber, sideSign]
  have hw : e ⁻¹' walls p = walls p := by
    simp only [walls, preimage_iUnion, preimage_union, e.preimage_frontier, hp, ht, hc]
    refine iUnion_congr fun n => congrArg (fun s =>
      frontier (passage p n) ∪ frontier (tunnel p n) ∪ s) ?_
    refine iUnion_congr fun m => ?_
    exact iUnion_congr_of_surjective Bool.not (fun j => ⟨!j, by simp⟩) (fun _ => rfl)
  rcases hz with (hz | hz) | hz
  · refine Or.inl (Or.inl ⟨?_, ?_⟩)
    · simpa [Complex.star_def] using hz.1
    · intro hs
      have hs' : z ∈ e ⁻¹' walls p := hs
      rw [hw] at hs'
      exact hz.2 hs'
  · rcases mem_iUnion.mp hz with ⟨n, hn⟩
    refine Or.inl (Or.inr (mem_iUnion.mpr ⟨n, ?_⟩))
    simpa [openings, Complex.star_def] using hn
  · rcases mem_iUnion.mp hz with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨j, hj⟩
    refine Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨!j, ?_⟩⟩)
    constructor
    · simpa [Complex.star_def] using hj.1
    · have hs : sideSign (!j) = -sideSign j := by
        cases j <;> norm_num [sideSign]
      simpa only [Complex.star_def, Complex.conj_im, hs, neg_mul, neg_sub_neg,
        abs_sub_comm] using hj.2

end MaxModulusPoints.TractGeometry
