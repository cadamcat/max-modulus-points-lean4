module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.InverseSymmetry
public import MaxModulusPoints.TractGeometry.NormalizedSymmetry
public import MaxModulusPoints.TractGeometry.RealAxis
public import MaxModulusPoints.TractGeometry.StripContainment

/-!
# The real-axis correspondence of the conformal equivalence

Conjugation symmetry in both directions identifies the real axis of the
tract with the positive real axis of the target.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_real_axis_correspondence (p : BlockParameters) (δ : GateIndex → ℝ)
    (e : NormalizedSymmetricEquivalence (tract p δ) target (-1) 1) :
    BijOn e.toFun {z : ℂ | -2 < z.re ∧ z.im = 0}
      {w : ℂ | 0 < w.re ∧ w.im = 0} := by
  have hsource {z : ℂ} (hz : -2 < z.re ∧ z.im = 0) : z ∈ tract p δ := by
    have hcast : (z.re : ℂ) = z := by
      apply Complex.ext
      · rfl
      · exact hz.2.symm
    rw [← hcast]
    exact tract_real_mem p δ hz.1
  have hmaps : MapsTo e.toFun {z : ℂ | -2 < z.re ∧ z.im = 0}
      {w : ℂ | 0 < w.re ∧ w.im = 0} := by
    intro z hz
    have hzmem := hsource hz
    have hzstar : star z = z := by
      apply Complex.ext <;> simp [hz.2]
    have hsym := e.symmetric_map z hzmem
    rw [hzstar] at hsym
    have him : (e.toFun z).im = 0 := by
      have h := congrArg Complex.im hsym
      simp only [Complex.star_def, Complex.conj_im] at h
      linarith
    have htarget := e.mapsTo hzmem
    have hpositive : 0 < (e.toFun z).re := by
      simpa [target, him] using htarget
    exact ⟨hpositive, him⟩
  refine ⟨hmaps, ?_, ?_⟩
  · intro z hz v hv heq
    calc
      z = e.invFun (e.toFun z) := (e.left_inv z (hsource hz)).symm
      _ = e.invFun (e.toFun v) := congrArg e.invFun heq
      _ = v := e.left_inv v (hsource hv)
  · intro w hw
    have hwmem : w ∈ target := by
      simpa [target, hw.2] using hw.1
    have hu := e.inverse_mapsTo hwmem
    have hwstar : star w = w := by
      apply Complex.ext <;> simp [hw.2]
    have hsym := tract_inverse_star p δ e hwmem
    rw [hwstar] at hsym
    have him : (e.invFun w).im = 0 := by
      have h := congrArg Complex.im hsym
      simp only [Complex.star_def, Complex.conj_im] at h
      linarith
    exact ⟨e.invFun w, ⟨tract_re_gt p δ hu, him⟩, e.right_inv w hwmem⟩

end MaxModulusPoints.TractGeometry
