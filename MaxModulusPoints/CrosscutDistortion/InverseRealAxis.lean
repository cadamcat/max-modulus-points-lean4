module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.RealAxis
public import MaxModulusPoints.CrosscutDistortion.TractSymmetry

/-!
# Real-axis orientation of inverse tract maps

The inverse of a normalized strip equivalence takes the whole real axis
into the real interval to the right of `-2`, in increasing order.
-/


@[expose] public section

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint
open scoped ComplexConjugate

/-- The inverse strip map is real and strictly increasing on the whole real
axis, and its values have real part greater than the tract's left endpoint. -/
theorem tract_strip_inverse_real_axis (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0) :
    (∀ x : ℝ, (φ.invFun x).im = 0 ∧ -2 < (φ.invFun x).re) ∧
      StrictMono (fun x : ℝ => (φ.invFun x).re) := by
  have hposition (n : ℕ) : 0 ≤ blockPosition p n := by
    unfold blockPosition
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => le_trans zero_le_one (p.gap_ge_one k))
      (Nat.cast_nonneg n)
  have hbound (z : ℂ) (hz : z ∈ tract p δ) : -2 < z.re := by
    rcases hz with (hz | hz) | hz
    · exact hz.1.1
    · rcases mem_iUnion.mp hz with ⟨n, hn⟩
      rcases hn with hn | hn | hn <;> linarith [hn.1, hposition n]
    · rcases mem_iUnion.mp hz with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨j, hj⟩
      linarith [hj.1, hposition i.1]
  have hconj : MapsTo conj (tract p δ) (tract p δ) := by
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
  have hstrip (x : ℝ) : (x : ℂ) ∈ strip := by simp [strip]
  have hreal (x : ℝ) : (φ.invFun x).im = 0 ∧ -2 < (φ.invFun x).re := by
    have hmem := φ.inverse_mapsTo (hstrip x)
    have hstar : star (φ.invFun x) ∈ tract p δ := hconj hmem
    have heq : φ.toFun (star (φ.invFun x)) = φ.toFun (φ.invFun x) := by
      rw [tract_strip_equivalence_conj p δ φ hφ0 hφre hφim _ hmem,
        φ.right_inv _ (hstrip x)]
      simp
    have heqinv := congrArg φ.invFun heq
    rw [φ.left_inv _ hstar, φ.left_inv _ hmem] at heqinv
    have him := congrArg Complex.im heqinv
    simp only [Complex.star_def, Complex.conj_im] at him
    exact ⟨by linarith, hbound _ hmem⟩
  have hreal_eq (x : ℝ) : ((φ.invFun x).re : ℂ) = φ.invFun x := by
    apply Complex.ext
    · simp
    · simpa using (hreal x).1.symm
  refine ⟨hreal, ?_⟩
  have hmono := (tract_strip_real_axis p δ φ hφ0 hφre hφim).2
  intro x y hxy
  apply (hmono.lt_iff_lt (hreal x).2 (hreal y).2).mp
  simpa only [hreal_eq, φ.right_inv _ (hstrip x), φ.right_inv _ (hstrip y),
    Complex.ofReal_re] using hxy

end MaxModulusPoints.CrosscutDistortion
