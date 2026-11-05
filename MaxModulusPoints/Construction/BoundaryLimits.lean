module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
public import MaxModulusPoints.Construction.StripCoordinates

/-!
# Boundary upper limits of logarithmic conformal maps

The escape condition bounds the conformal map on each portion of the
tract lying to the left of a fixed vertical line. Compact subsets of the
positive half-plane have compact inverse images inside the tract. These
two facts give the nonpositive boundary upper limits used in
Pardo-Simón–Sixsmith, Propositions 4.3 and 4.4.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set Filter Metric
open scoped Topology

noncomputable section

/-- Escape at the positive end rules out unbounded conformal values on
the portion of a tract left of a fixed line. The bound here is for one map. -/
theorem logModel_norm_bounded_on_left {V : Set ℂ} (G : Blueprint.LogModel V) (T : ℝ) :
    ∃ B : ℝ, ∀ z ∈ V, z.re ≤ T → ‖G.toFun z‖ ≤ B := by
  by_contra h
  push_neg at h
  choose z hz hzT hlarge using fun n : ℕ => h (n : ℝ)
  have hnorm : Tendsto (fun n => ‖G.toFun (z n)‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (hlarge n).le) tendsto_natCast_atTop_atTop
  have hescape := G.escape (fun n => G.toFun (z n)) (fun n => G.mapsTo (hz n)) hnorm
  have heq : (fun n => (G.invFun (G.toFun (z n))).re) = fun n => (z n).re := by
    funext n
    rw [G.left_inv _ (hz n)]
  rw [heq] at hescape
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hescape.eventually (eventually_gt_atTop T))
  linarith [hN N le_rfl, hzT N]

/-- Every finite point outside the tract has nonpositive upper boundary
limit for the real part of its logarithmic conformal map. -/
theorem logModel_boundaryUpper_of_not_mem {V : Set ℂ} (G : Blueprint.LogModel V)
    {ζ : ℂ} (hζ : ζ ∉ V) : Blueprint.BoundaryUpper V G.toFun ζ 0 := by
  intro ε hε
  obtain ⟨B, hB⟩ := logModel_norm_bounded_on_left G (ζ.re + 1)
  let K : Set ℂ := closedBall 0 B ∩ {w : ℂ | ε ≤ w.re}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hKtarget : K ⊆ Blueprint.target := by
    intro w hw
    exact positive_halfPlane_subset_target (lt_of_lt_of_le hε hw.2)
  have hI : IsCompact (G.invFun '' K) :=
    hK.image_of_continuousOn (G.inverse_holomorphic.continuousOn.mono hKtarget)
  have hζI : ζ ∉ G.invFun '' K := by
    rintro ⟨w, hw, rfl⟩
    exact hζ (G.inverse_mapsTo (hKtarget hw))
  have hnear' : ∀ᶠ z in 𝓝 ζ, z.re < ζ.re + 1 :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
      change ζ.re < ζ.re + 1
      linarith)
  have hnear : ∀ᶠ z in 𝓝[V] ζ, z.re < ζ.re + 1 :=
    hnear'.filter_mono nhdsWithin_le_nhds
  have havoid' : ∀ᶠ z in 𝓝 ζ, z ∉ G.invFun '' K :=
    hI.isClosed.isOpen_compl.mem_nhds hζI
  have havoid : ∀ᶠ z in 𝓝[V] ζ, z ∉ G.invFun '' K :=
    havoid'.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear, havoid] with z hz hzre hzavoid
  change (G.toFun z).re ≤ 0 + ε
  by_contra! hfail
  apply hzavoid
  exact ⟨G.toFun z,
    ⟨mem_closedBall_zero_iff.mpr (hB z hz hzre.le),
      show ε ≤ (G.toFun z).re by linarith⟩, G.left_inv z hz⟩

theorem logModel_boundaryUpper {V : Set ℂ} (G : Blueprint.LogModel V)
    {ζ : ℂ} (hζ : ζ ∈ frontier V) : Blueprint.BoundaryUpper V G.toFun ζ 0 := by
  apply logModel_boundaryUpper_of_not_mem G
  simpa only [G.open_domain.interior_eq] using hζ.2

theorem boundaryUpper_mono {U V : Set ℂ} {G : ℂ → ℂ} {ζ : ℂ} {B : ℝ}
    (hUV : U ⊆ V) (h : Blueprint.BoundaryUpper V G ζ B) :
    Blueprint.BoundaryUpper U G ζ B := by
  intro ε hε
  exact (h ε hε).filter_mono (nhdsWithin_mono ζ hUV)

#print axioms logModel_norm_bounded_on_left
#print axioms logModel_boundaryUpper_of_not_mem
#print axioms logModel_boundaryUpper

end

end MaxModulusPoints.Construction
