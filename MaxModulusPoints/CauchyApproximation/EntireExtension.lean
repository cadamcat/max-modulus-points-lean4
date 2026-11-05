module

public import MaxModulusPoints.CauchyApproximation.ContourDensity
public import MaxModulusPoints.CauchyApproximation.CoreTopology
public import MaxModulusPoints.CauchyApproximation.DetourHolomorphy
public import MaxModulusPoints.CauchyApproximation.Holomorphy
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral
public import MaxModulusPoints.CauchyApproximation.LocalAgreement
public import MaxModulusPoints.CauchyApproximation.LocalDetour
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# The entire canonical Cauchy extension

The actual local detour integrals agree with the two prescribed branches
away from the contour. The core topology gives holomorphic branches at all
other points. Since the contour complement is dense, these local functions
agree on overlaps and define a unique entire extension of the canonical
gluing. Integrability of the original density is the only extra hypothesis.
-/


@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- An integrable canonical density gives a unique entire extension agreeing
with the prescribed Cauchy gluing off the contour. -/
theorem NormalizedModel.existsUnique_entire_canonical_of_integrable (m : NormalizedModel)
    (hρ : Integrable m.density) :
    ∃! f : ℂ → ℂ, Differentiable ℂ f ∧ IsCanonicalApproximation m f := by
  classical
  let S : Set ℂ := (range m.contour)ᶜ
  let Iγ := cauchyIntegral m.contour m.density
  let G : ℂ → ℂ := fun z ↦ if z ∈ m.core then Iγ z + m.modelFunction z else Iγ z
  obtain ⟨hopen, hclosed⟩ := m.core_open_and_closed_contour_union
  obtain ⟨hfrontier, hdense⟩ := m.contour_frontier_and_dense_complement
  have hdisjoint : Disjoint m.core (range m.contour) := by
    rw [← hfrontier]
    exact (disjoint_frontier_iff_isOpen.2 hopen).symm
  have hcoreAvoid {z : ℂ} (hz : z ∈ m.core) : z ∉ range m.contour :=
    fun hzγ ↦ (disjoint_left.1 hdisjoint) hz hzγ
  have hγproper := m.proper_contour_and_localDetour_holomorphy.1
  have hI (z : ℂ) (hz : z ∉ range m.contour) : DifferentiableAt ℂ Iγ z :=
    (hasDerivAt_cauchyIntegral hγproper hρ hz).differentiableAt
  have hg : DifferentiableOn ℂ m.modelFunction m.domain := m.holomorphic_forward.cexp
  have hIcore : DifferentiableOn ℂ Iγ m.core :=
    fun z hz ↦ (hI z (hcoreAvoid hz)).differentiableWithinAt
  have hgcore : DifferentiableOn ℂ m.modelFunction m.core := hg.mono (fun _ hz ↦ hz.1)
  have hlocal (x : ℂ) : ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H U ∧
        ∀ z ∈ U, z ∈ S → H z = G z := by
    by_cases hxγ : x ∈ range m.contour
    · obtain ⟨t, rfl⟩ := hxγ
      obtain ⟨ε, hε, -, hH, hagree⟩ := m.localDetour_cauchyIntegral_agrees t hρ
      refine ⟨Metric.ball (m.contour t) ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
        cauchyIntegral (m.localDetour t)
          (fun u ↦ m.modelFunction (m.localDetour t u) * deriv (m.localDetour t) u), hH, ?_⟩
      intro z hz hzS
      by_cases hzcore : z ∈ m.core
      · simpa only [G, if_pos hzcore] using (hagree z hz hzS).1 hzcore
      · simpa only [G, if_neg hzcore] using (hagree z hz hzS).2 hzcore
    · by_cases hxcore : x ∈ m.core
      · refine ⟨m.core, hopen, hxcore, (fun z ↦ Iγ z + m.modelFunction z),
          hIcore.add hgcore, ?_⟩
        intro z hz _
        simp only [G, if_pos hz]
      · let U : Set ℂ := (m.core ∪ range m.contour)ᶜ
        have hxU : x ∈ U := fun hx ↦ hx.elim hxcore hxγ
        have hIU : DifferentiableOn ℂ Iγ U := fun z hz ↦
          (hI z (fun hzγ ↦ hz (Or.inr hzγ))).differentiableWithinAt
        refine ⟨U, hclosed.isOpen_compl, hxU, Iγ, hIU, ?_⟩
        intro z hz _
        have hzcore : z ∉ m.core := fun hc ↦ hz (Or.inl hc)
        simp only [G, if_neg hzcore]
  choose U hU hx H hH hmatch using hlocal
  let f : ℂ → ℂ := fun x ↦ H x x
  have hconsistent (x : ℂ) : EqOn f (H x) (U x) := by
    intro y hy
    have : NeBot (𝓝[S] y) := mem_closure_iff_nhdsWithin_neBot.1 (hdense y)
    have hycont : ContinuousAt (H y) y :=
      ((hH y).differentiableAt ((hU y).mem_nhds (hx y))).continuousAt
    have hxcont : ContinuousAt (H x) y :=
      ((hH x).differentiableAt ((hU x).mem_nhds hy)).continuousAt
    have hUy : U y ∈ 𝓝[S] y := mem_nhdsWithin_of_mem_nhds ((hU y).mem_nhds (hx y))
    have hUx : U x ∈ 𝓝[S] y := mem_nhdsWithin_of_mem_nhds ((hU x).mem_nhds hy)
    have heq : H y =ᶠ[𝓝[S] y] H x := by
      filter_upwards [self_mem_nhdsWithin, hUy, hUx] with z hzS hzy hzx
      exact (hmatch y z hzy hzS).trans (hmatch x z hzx hzS).symm
    exact tendsto_nhds_unique_of_eventuallyEq
      (hycont.tendsto.mono_left nhdsWithin_le_nhds)
      (hxcont.tendsto.mono_left nhdsWithin_le_nhds) heq
  have hfD : Differentiable ℂ f := by
    intro x
    have heq : f =ᶠ[𝓝 x] H x :=
      (hconsistent x).eventuallyEq_of_mem ((hU x).mem_nhds (hx x))
    exact ((hH x).differentiableAt ((hU x).mem_nhds (hx x))).congr_of_eventuallyEq heq
  have hfG : EqOn f G S := fun x hxS ↦ hmatch x x (hx x) hxS
  have hfcanonical : IsCanonicalApproximation m f := by
    intro z hz
    have heq := hfG hz
    constructor
    · intro hzcore
      simpa only [G, if_pos hzcore] using heq
    · intro hzcore
      simpa only [G, if_neg hzcore] using heq
  refine ⟨f, ⟨hfD, hfcanonical⟩, ?_⟩
  intro k hk
  apply Continuous.ext_on hdense hk.1.continuous hfD.continuous
  intro z hzS
  by_cases hzcore : z ∈ m.core
  · exact ((hk.2 z hzS).1 hzcore).trans ((hfcanonical z hzS).1 hzcore).symm
  · exact ((hk.2 z hzS).2 hzcore).trans ((hfcanonical z hzS).2 hzcore).symm

#print axioms NormalizedModel.existsUnique_entire_canonical_of_integrable

end MaxModulusPoints.CauchyApproximation
