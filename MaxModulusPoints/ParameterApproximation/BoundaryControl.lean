import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import MaxModulusPoints.Blueprint.Data
/-!
# Boundary control from the inverse escape condition

The inverse escape condition bounds the conformal image of every part of
the tract with bounded real coordinate. Compact subsets of the positive
half-plane therefore have inverse images separated from each finite boundary
point. It follows that the conformal map has nonpositive real upper limit
at such a boundary point.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Blueprint
open scoped Topology

/-- The conformal image is bounded wherever the source real coordinate is
bounded above. This bound may depend on the conformal map. -/
theorem logModel_image_norm_bound {V : Set ℂ} (G : LogModel V) (R : ℝ) :
    ∃ C : ℝ, ∀ z ∈ V, z.re ≤ R → ‖G.toFun z‖ ≤ C := by
  by_contra h
  push Not at h
  choose z hz hRe hnorm using fun n : ℕ => h (n : ℝ)
  have hinfty : Tendsto (fun n => ‖G.toFun (z n)‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (hnorm n).le) tendsto_natCast_atTop_atTop
  have hes := G.escape (fun n => G.toFun (z n))
    (fun n => G.mapsTo (hz n)) hinfty
  have heq : (fun n => (G.invFun (G.toFun (z n))).re) = fun n => (z n).re :=
    funext fun n => congrArg Complex.re (G.left_inv (z n) (hz n))
  rw [heq] at hes
  obtain ⟨n, hn⟩ := (hes.eventually (eventually_gt_atTop R)).exists
  exact (not_lt_of_ge (hRe n)) hn

/-- At every finite point outside the tract, the real part of the conformal
map has upper limit at most zero when approached from within the tract. -/
theorem logModel_boundary_re_upper {V : Set ℂ} (G : LogModel V)
    {ζ : ℂ} (hζ : ζ ∉ V) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝[V] ζ, (G.toFun z).re < ε := by
  obtain ⟨C, hC⟩ := logModel_image_norm_bound G (ζ.re + 1)
  let K : Set ℂ := Metric.closedBall 0 C ∩ {w : ℂ | ε ≤ w.re}
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) C).inter_right
      (isClosed_le continuous_const Complex.continuous_re)
  have hKt : K ⊆ target := by
    intro w hw
    change -14 * max 0 (Real.log |w.im|) < w.re
    have hmax : 0 ≤ max 0 (Real.log |w.im|) := le_max_left _ _
    have hre : ε ≤ w.re := hw.2
    nlinarith
  have hL : IsCompact (G.invFun '' K) :=
    hK.image_of_continuousOn (G.inverse_holomorphic.continuousOn.mono hKt)
  have hζL : ζ ∉ G.invFun '' K := by
    rintro ⟨w, hw, rfl⟩
    exact hζ (G.inverse_mapsTo (hKt hw))
  have hnear : ∀ᶠ z in 𝓝[V] ζ, z ∉ G.invFun '' K :=
    mem_nhdsWithin_of_mem_nhds (hL.isClosed.isOpen_compl.mem_nhds hζL)
  have hreal : ∀ᶠ z in 𝓝[V] ζ, z.re < ζ.re + 1 :=
    mem_nhdsWithin_of_mem_nhds
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
        change ζ.re < ζ.re + 1
        linarith))
  filter_upwards [self_mem_nhdsWithin, hnear, hreal] with z hz hzL hzR
  by_contra h
  have hbound := hC z hz hzR.le
  have hmem : G.toFun z ∈ K := by
    exact ⟨mem_closedBall_zero_iff.mpr hbound, le_of_not_gt h⟩
  exact hzL ⟨G.toFun z, hmem, G.left_inv z hz⟩

#print axioms logModel_image_norm_bound
#print axioms logModel_boundary_re_upper

end MaxModulusPoints.ParameterApproximation
