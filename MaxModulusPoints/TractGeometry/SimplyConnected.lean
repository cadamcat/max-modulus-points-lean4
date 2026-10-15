import Mathlib.Analysis.Normed.Group.Bounded
import TauCeti.Analysis.Complex.Conformal.SimplyConnected
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.ComplementPaths
import MaxModulusPoints.TractGeometry.Connectedness
import MaxModulusPoints.TractGeometry.Openness
import MaxModulusPoints.TractGeometry.StripContainment
/-!
# Simple connectivity of the chamber and gate tract

The complement is path connected and unbounded, so filling bounded
complementary components leaves the tract unchanged. The open connected
tract is therefore simply connected.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_isSimplyConnected (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (hpos : ∀ i, 0 < δ i) :
    IsSimplyConnected (tract p δ) := by
  have hbase : (-3 : ℂ) ∈ (tract p δ)ᶜ := by
    intro hmem
    have hreal := tract_re_gt p δ hmem
    norm_num at hreal
  have hpath : IsPathConnected (tract p δ)ᶜ := by
    refine ⟨(-3 : ℂ), hbase, ?_⟩
    intro z hz
    exact (tract_compl_joined p δ hδ hz).symm
  have hunbounded : ¬ Bornology.IsBounded (tract p δ)ᶜ := by
    intro hbounded
    obtain ⟨C, hC⟩ := hbounded.exists_norm_le
    let q : ℂ := ⟨-(|C| + 3), 0⟩
    have hq : q ∈ (tract p δ)ᶜ := by
      intro hmem
      have hreal := tract_re_gt p δ hmem
      change -2 < -(|C| + 3) at hreal
      linarith [abs_nonneg C]
    have hbound := hC q hq
    have hnorm := Complex.abs_re_le_norm q
    change |-(|C| + 3)| ≤ ‖q‖ at hnorm
    rw [abs_neg, abs_of_nonneg (by linarith [abs_nonneg C])] at hnorm
    linarith [le_abs_self C]
  have hfill : TauCeti.filledHull (tract p δ) = tract p δ :=
    TauCeti.filledHull_eq_self hpath.isConnected.isPreconnected hunbounded
  exact TauCeti.isSimplyConnected_of_filledHull_subset (tract_isOpen p δ hδ)
    (tract_isConnected p δ hδ hpos) hfill.le

end MaxModulusPoints.TractGeometry
