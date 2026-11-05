module

public import Mathlib.Analysis.Complex.OpenMapping
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.Symmetry

/-!
# Reflection symmetry of normalized chamber-tract maps

The inverse holomorphic map makes the tract open. Reflection invariance of
the concrete walls and openings then allows normalized-map uniqueness to
identify the map with its conjugate reflection.
-/


@[expose] public section

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint
open scoped ComplexConjugate

/-- Every tract-to-strip equivalence with the real positive derivative
normalization commutes with complex conjugation. -/
theorem tract_strip_equivalence_conj (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0) :
    ∀ z ∈ tract p δ, φ.toFun (star z) = star (φ.toFun z) := by
  have hSo : IsOpen strip := isOpen_lt Complex.continuous_im.abs continuous_const
  have h0S : (0 : ℂ) ∈ strip := by norm_num [strip]
  have h1S : (1 : ℂ) ∈ strip := by norm_num [strip]
  have hconv : Convex ℝ strip := by
    simpa only [strip, abs_lt, ofPred_and] using
      (convex_halfSpace_im_gt (-(1 / 2 : ℝ))).inter
        (convex_halfSpace_im_lt (1 / 2 : ℝ))
  have hnonconstant : ¬ ∃ c : ℂ, ∀ z ∈ strip, φ.invFun z = c := by
    rintro ⟨c, hc⟩
    have hh := congrArg φ.toFun ((hc 0 h0S).trans (hc 1 h1S).symm)
    simp only [φ.right_inv 0 h0S, φ.right_inv 1 h1S] at hh
    exact zero_ne_one hh
  have hopen := ((φ.inverse_holomorphic.analyticOnNhd hSo).is_constant_or_isOpen
    hconv.isPreconnected).resolve_left hnonconstant
  have himage : φ.invFun '' strip = tract p δ := by
    apply subset_antisymm
    · rintro q ⟨z, hz, rfl⟩
      exact φ.inverse_mapsTo hz
    · intro z hz
      exact ⟨φ.toFun z, φ.mapsTo hz, φ.left_inv z hz⟩
  have hUo : IsOpen (tract p δ) := by
    rw [← himage]
    exact hopen strip subset_rfl hSo
  have hposition : ∀ n, 0 ≤ blockPosition p n := by
    intro n
    unfold blockPosition
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => le_trans zero_le_one (p.gap_ge_one k))
      (Nat.cast_nonneg n)
  have hfront (S : Set ℂ) (a : ℝ) (hS : S ⊆ {z : ℂ | a ≤ z.re}) :
      frontier S ⊆ {z : ℂ | a ≤ z.re} :=
    frontier_subset_closure.trans
      (closure_minimal hS (isClosed_le continuous_const Complex.continuous_re))
  have hbase : (-1 : ℂ) ∈ tract p δ := by
    refine Or.inl (Or.inl ⟨?_, ?_⟩)
    · constructor
      · norm_num
      · simpa using half_pos Real.pi_pos
    · intro hw
      rcases mem_iUnion.mp hw with ⟨n, hn⟩
      have hle : blockPosition p n ≤ (-1 : ℂ).re := by
        rcases hn with (hn | hn) | hn
        · exact hfront (passage p n) (blockPosition p n) (fun _ hz => hz.1) hn
        · apply hfront (tunnel p n) (blockPosition p n) ?_ hn
          intro z hz
          have ht := hz.1
          change blockPosition p n ≤ z.re
          linarith
        · rcases mem_iUnion.mp hn with ⟨m, hm⟩
          rcases mem_iUnion.mp hm with ⟨j, hj⟩
          exact hfront (chamber p ⟨n, m⟩ j) (blockPosition p n) (fun _ hz => hz.1) hj
      norm_num at hle
      linarith [hposition n]
  have hU : MapsTo conj (tract p δ) (tract p δ) := by
    intro z hz
    change star z ∈ tract p δ
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
      refine iUnion_congr fun n => congrArg (fun S =>
        frontier (passage p n) ∪ frontier (tunnel p n) ∪ S) ?_
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
  simpa only [Complex.star_def] using strip_equivalence_conj hUo (-1)
    (by simpa using hbase) hU φ (by simpa using hφ0)
    (by simpa using hφre) (by simpa using hφim)

end MaxModulusPoints.CrosscutDistortion
