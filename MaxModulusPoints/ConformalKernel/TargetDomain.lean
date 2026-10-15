import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Tactic.Linarith
/-!
# The logarithmic target domain

The fixed target used by Pardo-Simón–Sixsmith is the epigraph
`{x + y I | -14 * max 0 (log |y|) < x}`. A horizontal shear identifies
it with the right half-plane and proves simple connectivity.
-/

open Set

namespace MaxModulusPoints.ConformalKernel

/-- The real coordinate of the boundary of the logarithmic target. -/
noncomputable def targetBoundary (y : ℝ) : ℝ := -14 * max 0 (Real.log |y|)

/-- The target of the tract conformal maps. -/
def modelTarget : Set ℂ := {z | targetBoundary z.im < z.re}

private theorem log_max_one_abs (y : ℝ) :
    Real.log (max 1 |y|) = max 0 (Real.log |y|) := by
  by_cases hy : |y| ≤ 1
  · rw [max_eq_left hy, Real.log_one, max_eq_left (Real.log_nonpos (abs_nonneg y) hy)]
  · have hy' : 1 ≤ |y| := (lt_of_not_ge hy).le
    rw [max_eq_right hy', max_eq_right (Real.log_nonneg hy')]

private theorem continuous_targetBoundary : Continuous targetBoundary := by
  have hm : Continuous (fun y : ℝ => max 1 |y|) := continuous_const.max continuous_abs
  have hl : Continuous (fun y : ℝ => Real.log (max 1 |y|)) :=
    hm.log (fun y => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 |y|)))
  have heq : targetBoundary = fun y : ℝ => -14 * Real.log (max 1 |y|) := by
    funext y
    rw [log_max_one_abs]
    rfl
  rw [heq]
  exact continuous_mul.comp (continuous_const.prodMk hl)

private noncomputable def targetShear : ℂ ≃ₜ ℂ where
  toFun z := ⟨z.re + targetBoundary z.im, z.im⟩
  invFun z := ⟨z.re - targetBoundary z.im, z.im⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp
  continuous_toFun := Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_add.comp
      (Complex.continuous_re.prodMk (continuous_targetBoundary.comp Complex.continuous_im))).prodMk
      Complex.continuous_im)
  continuous_invFun := Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_sub.comp
      (Complex.continuous_re.prodMk (continuous_targetBoundary.comp Complex.continuous_im))).prodMk
      Complex.continuous_im)

/-- The logarithmic target is open. -/
theorem isOpen_modelTarget : IsOpen modelTarget :=
  isOpen_lt (continuous_targetBoundary.comp Complex.continuous_im) Complex.continuous_re

/-- The normalization point belongs to the target. -/
theorem one_mem_modelTarget : (1 : ℂ) ∈ modelTarget := by
  simp [modelTarget, targetBoundary]

/-- The target is a proper subset of the complex plane. -/
theorem modelTarget_ne_univ : modelTarget ≠ univ := by
  intro h
  have hz : (0 : ℂ) ∈ modelTarget := h ▸ mem_univ 0
  simpa [modelTarget, targetBoundary] using hz

/-- The target is simply connected. -/
theorem isSimplyConnected_modelTarget : IsSimplyConnected modelTarget := by
  have hh : IsSimplyConnected {z : ℂ | 0 < z.re} := by
    letI : ContractibleSpace {z : ℂ | 0 < z.re} :=
      (convex_halfSpace_gt Complex.reLm.isLinear 0).contractibleSpace
        ⟨1, by simp⟩
    change SimplyConnectedSpace {z : ℂ | 0 < z.re}
    infer_instance
  have heq : modelTarget = targetShear.symm ⁻¹' {z : ℂ | 0 < z.re} := by
    ext z
    change targetBoundary z.im < z.re ↔ 0 < z.re - targetBoundary z.im
    exact sub_pos.symm
  rw [heq, Homeomorph.isSimplyConnected_preimage]
  exact hh

/-- The target contains the right half-plane. -/
theorem rightHalfPlane_subset_modelTarget : {z : ℂ | 0 < z.re} ⊆ modelTarget := by
  intro z hz
  have hb : targetBoundary z.im ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (le_max_left _ _)
  exact hb.trans_lt hz

/-- The target is invariant under conjugation. -/
theorem conj_mem_modelTarget_iff (z : ℂ) :
    starRingEnd ℂ z ∈ modelTarget ↔ z ∈ modelTarget := by
  simp [modelTarget, targetBoundary]

#print axioms isOpen_modelTarget
#print axioms isSimplyConnected_modelTarget
#print axioms modelTarget_ne_univ

end MaxModulusPoints.ConformalKernel
