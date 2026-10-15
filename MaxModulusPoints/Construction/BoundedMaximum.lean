import Mathlib.Topology.Order.LocalExtr
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
import MaxModulusPoints.Construction.BoundaryLimits
import MaxModulusPoints.Construction.StripCoordinates
/-!
# A bounded-domain maximum principle with upper boundary limits

Positive superlevel sets stay away from boundary points with smaller
upper limits. Compactness then produces an interior maximum, which a
continuous conformal inverse excludes. This is the comparison needed
for the left-portion bound in Pardo-Simón–Sixsmith, Proposition 4.2.
-/

namespace MaxModulusPoints.Construction

open Set Filter Metric
open scoped Topology

noncomputable section

/-- A conformal inverse excludes a local maximum of the real part at
every point whose image has positive real part. -/
theorem logModel_not_isLocalMax_re {V : Set ℂ} (G : Blueprint.LogModel V)
    {z : ℂ} (hz : z ∈ V) (hpos : 0 < (G.toFun z).re) :
    ¬ IsLocalMax (fun w => (G.toFun w).re) z := by
  intro hmax
  have htarget : Blueprint.target ∈ 𝓝 (G.toFun z) :=
    mem_of_superset ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos)
      positive_halfPlane_subset_target
  have hinv : ContinuousAt G.invFun (G.toFun z) :=
    ((G.inverse_holomorphic _ (G.mapsTo hz)).differentiableAt htarget).continuousAt
  have hray : Tendsto (fun t : ℝ => G.invFun (G.toFun z + (t : ℂ))) (𝓝 0) (𝓝 z) := by
    have hcont : ContinuousAt (fun t : ℝ => G.toFun z + (t : ℂ)) 0 :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    have hlim : Tendsto (fun t : ℝ => G.toFun z + (t : ℂ)) (𝓝 0) (𝓝 (G.toFun z)) := by
      simpa only [Complex.ofReal_zero, add_zero] using hcont.tendsto
    simpa only [Function.comp_def, G.left_inv z hz] using! hinv.tendsto.comp hlim
  have hev : ∀ᶠ t : ℝ in 𝓝 0,
      (G.toFun (G.invFun (G.toFun z + (t : ℂ)))).re ≤ (G.toFun z).re :=
    hray.eventually hmax
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  have ht : r / 2 ∈ ball (0 : ℝ) r := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  have htarg : G.toFun z + ((r / 2 : ℝ) : ℂ) ∈ Blueprint.target := by
    apply positive_halfPlane_subset_target
    change 0 < (G.toFun z).re + r / 2
    linarith
  have hle := hball ht
  change (G.toFun (G.invFun (G.toFun z + ((r / 2 : ℝ) : ℂ)))).re ≤ (G.toFun z).re at hle
  rw [G.right_inv _ htarg] at hle
  simp only [Complex.add_re, Complex.ofReal_re] at hle
  linarith

/-- A superlevel strictly above all boundary upper limits has closure
inside the open domain. No continuity at boundary points is required. -/
theorem closure_superlevel_subset_of_boundaryUpper {U : Set ℂ} (hU : IsOpen U)
    {G : ℂ → ℂ} {B C : ℝ} (hBC : B < C)
    (hupper : ∀ ζ ∈ frontier U, Blueprint.BoundaryUpper U G ζ B) :
    closure (U ∩ {z : ℂ | C ≤ (G z).re}) ⊆ U := by
  intro ζ hζ
  by_contra hnot
  have hζU : ζ ∈ closure U := closure_mono inter_subset_left hζ
  have hfront : ζ ∈ frontier U := ⟨hζU, by simpa only [hU.interior_eq] using hnot⟩
  have hev := hupper ζ hfront ((C - B) / 2) (by linarith)
  obtain ⟨N, hN, hbound⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
  obtain ⟨w, hwN, hwS⟩ := mem_closure_iff_nhds.mp hζ N hN
  have h := hbound ⟨hwN, hwS.1⟩
  change (G w).re ≤ B + (C - B) / 2 at h
  have hlow : C ≤ (G w).re := hwS.2
  linarith

/-- Boundary upper limits control the real part of a conformal map on
every bounded open subdomain, without a continuous boundary extension. -/
theorem logModel_re_le_of_boundaryUpper {U V : Set ℂ} (G : Blueprint.LogModel V)
    (hU : IsOpen U) (hUV : U ⊆ V) (hbounded : Bornology.IsBounded U)
    {B : ℝ} (hB : 0 ≤ B)
    (hupper : ∀ ζ ∈ frontier U, Blueprint.BoundaryUpper U G.toFun ζ B) :
    ∀ z ∈ U, (G.toFun z).re ≤ B := by
  intro z hz
  by_contra! hbad
  let C := ((G.toFun z).re + B) / 2
  have hBC : B < C := by dsimp [C]; linarith
  have hzC : C ≤ (G.toFun z).re := by dsimp [C]; linarith
  let S : Set ℂ := U ∩ {w : ℂ | C ≤ (G.toFun w).re}
  have hzS : z ∈ S := ⟨hz, hzC⟩
  have hcl : closure S ⊆ U := closure_superlevel_subset_of_boundaryUpper hU hBC hupper
  have hcompact : IsCompact (closure S) :=
    (hbounded.subset (show S ⊆ U from inter_subset_left)).isCompact_closure
  have hcont : ContinuousOn (fun w => (G.toFun w).re) (closure S) :=
    Complex.continuous_re.comp_continuousOn
      (G.holomorphic.continuousOn.mono (hcl.trans hUV))
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn ⟨z, subset_closure hzS⟩ hcont
  have hzp : (G.toFun z).re ≤ (G.toFun p).re := hmax (subset_closure hzS)
  have hpu : p ∈ U := hcl hp
  have hlocal : IsLocalMax (fun w => (G.toFun w).re) p := by
    filter_upwards [hU.mem_nhds hpu] with w hwU
    by_cases hwS : w ∈ S
    · exact hmax (subset_closure hwS)
    · have hnot : ¬ C ≤ (G.toFun w).re := fun hwC => hwS ⟨hwU, hwC⟩
      have hlt : (G.toFun w).re < C := lt_of_not_ge hnot
      linarith
  exact logModel_not_isLocalMax_re G (hUV hpu) (by linarith) hlocal

/-- For a logarithmic conformal map, only the artificial boundary inside
the tract needs a separate bound; the physical boundary has upper limit zero. -/
theorem logModel_re_le_of_frontier_bound {U V : Set ℂ} (G : Blueprint.LogModel V)
    (hU : IsOpen U) (hUV : U ⊆ V) (hbounded : Bornology.IsBounded U)
    {B : ℝ} (hB : 0 ≤ B)
    (hfront : ∀ ζ ∈ frontier U, ζ ∈ V → (G.toFun ζ).re ≤ B) :
    ∀ z ∈ U, (G.toFun z).re ≤ B := by
  apply logModel_re_le_of_boundaryUpper G hU hUV hbounded hB
  intro ζ hζ
  by_cases hζV : ζ ∈ V
  · have hcont : ContinuousAt (fun z => (G.toFun z).re) ζ :=
      Complex.continuous_re.continuousAt.comp
        (((G.holomorphic ζ hζV).differentiableAt (G.open_domain.mem_nhds hζV)).continuousAt)
    intro ε hε
    have hev : ∀ᶠ z in 𝓝 ζ, (G.toFun z).re < B + ε :=
      hcont.tendsto.eventually (eventually_lt_nhds (by linarith [hfront ζ hζ hζV]))
    exact (hev.mono (fun _ hz => hz.le)).filter_mono nhdsWithin_le_nhds
  · intro ε hε
    have hev := (boundaryUpper_mono hUV (logModel_boundaryUpper_of_not_mem G hζV)) ε hε
    filter_upwards [hev] with z hz
    linarith

#print axioms logModel_not_isLocalMax_re
#print axioms logModel_re_le_of_boundaryUpper
#print axioms logModel_re_le_of_frontier_bound

end

end MaxModulusPoints.Construction
