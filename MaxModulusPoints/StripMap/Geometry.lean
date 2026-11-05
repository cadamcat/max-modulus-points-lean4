module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Equivalence
public import MaxModulusPoints.Blueprint.Data

/-!
# The strip and the logarithmic target

The target in Pardo-Simón–Sixsmith, equation (2.1), is the region to the
right of a continuous graph. A horizontal shear straightens this graph,
which supplies the simple connectivity needed for the Riemann mapping theorem.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.StripMap

open Set
open MaxModulusPoints.Blueprint

theorem isOpen_strip : IsOpen strip :=
  isOpen_lt (Complex.continuous_im.abs) continuous_const

theorem convex_strip : Convex ℝ strip := by
  intro z hz w hw a b ha hb hab
  have hz' : z.im ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := abs_lt.mp hz
  have hw' : w.im ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := abs_lt.mp hw
  change |(a • z + b • w).im| < 1 / 2
  rw [abs_lt]
  simpa only [Complex.add_im, Complex.smul_im, smul_eq_mul, mem_Ioo] using
    (convex_Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) hz' hw' ha hb hab

theorem zero_mem_strip : (0 : ℂ) ∈ strip := by
  norm_num [strip]

theorem isSimplyConnected_strip : IsSimplyConnected strip := by
  let : ContractibleSpace strip := convex_strip.contractibleSpace ⟨0, zero_mem_strip⟩
  change SimplyConnectedSpace strip
  exact inferInstance

theorem strip_ne_univ : strip ≠ univ := by
  intro h
  have hi : Complex.I ∈ strip := h ▸ mem_univ _
  norm_num [strip] at hi

/-- A horizontal shear sending the logarithmic target to the right half-plane. -/
def targetStraightening : ℂ ≃ₜ ℂ where
  toFun z := z + ((14 * Real.posLog |z.im| : ℝ) : ℂ)
  invFun z := z - ((14 * Real.posLog |z.im| : ℝ) : ℂ)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_id.add
    (Complex.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_posLog.comp Complex.continuous_im.abs)))
  continuous_invFun := continuous_id.sub
    (Complex.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_posLog.comp Complex.continuous_im.abs)))

theorem target_eq_preimage_halfPlane :
    target = targetStraightening ⁻¹' {z : ℂ | 0 < z.re} := by
  ext z
  change -14 * max 0 (Real.log |z.im|) < z.re ↔
    0 < (z + ((14 * Real.posLog |z.im| : ℝ) : ℂ)).re
  simp only [Complex.add_re, Complex.ofReal_re, Real.posLog]
  constructor <;> intro h <;> linarith

theorem isOpen_target : IsOpen target := by
  rw [target_eq_preimage_halfPlane]
  exact (isOpen_lt continuous_const Complex.continuous_re).preimage
    targetStraightening.continuous

theorem one_mem_target : (1 : ℂ) ∈ target := by
  norm_num [target]

theorem isSimplyConnected_target : IsSimplyConnected target := by
  rw [target_eq_preimage_halfPlane, targetStraightening.isSimplyConnected_preimage]
  have hc : Convex ℝ {z : ℂ | 0 < z.re} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap
  let : ContractibleSpace {z : ℂ | 0 < z.re} :=
    hc.contractibleSpace ⟨1, by norm_num⟩
  change SimplyConnectedSpace {z : ℂ | 0 < z.re}
  exact inferInstance

theorem target_ne_univ : target ≠ univ := by
  intro h
  have hz : (0 : ℂ) ∈ target := h ▸ mem_univ _
  norm_num [target] at hz

/-- The strip and the logarithmic target are conformally equivalent. -/
theorem nonempty_conformalEquivalence : Nonempty (ConformalEquivalence strip target) := by
  obtain ⟨f, hbij, hd, hdi, hl, hr⟩ :=
    TauCeti.exists_bijOn_differentiableOn_invFunOn_of_isSimplyConnected
      isOpen_strip isSimplyConnected_strip strip_ne_univ
      isOpen_target isSimplyConnected_target target_ne_univ
  exact ⟨⟨f, Function.invFunOn f strip, hd, hdi, hbij.mapsTo,
    fun w hw => Function.invFunOn_mem (hbij.surjOn hw), hl, hr⟩⟩

end MaxModulusPoints.StripMap
