import Mathlib.Analysis.Complex.AbsMax
import MaxModulusPoints.ConformalKernel.HolomorphicImages
import MaxModulusPoints.ConformalKernel.KernelConvergence
import MaxModulusPoints.ConformalKernel.KernelNormalFamilies
/-!
# Inverse identities for limits on a pointed kernel

Simultaneous holomorphic limits of Riemann maps and their inverses are inverse
bijections between the pointed kernel and the disc. The maximum-modulus
principle keeps the forward limit inside the disc; the inverse identities then
rule out degeneracy and identify the limiting image with the kernel.
-/

open Set Filter Function Metric
open scoped Topology Uniformity

namespace MaxModulusPoints.ConformalKernel

/-- Local uniform convergence permits evaluation along a converging family of
points, provided its limit is in the open domain and the limit map is continuous. -/
theorem tendsto_eval_of_locallyUniformlyOn {ι : Type*} {l : Filter ι}
    {S : Set ℂ} (hS : IsOpen S) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn F f l S) (hf : ContinuousOn f S)
    {u : ι → ℂ} {z : ℂ} (hz : z ∈ S) (hu : Tendsto u l (𝓝 z)) :
    Tendsto (fun i => F i (u i)) l (𝓝 (f z)) := by
  have he : Tendsto (fun i => (f (u i), F i (u i))) l (𝓤 ℂ) :=
    ((hS.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hlim) z hz).comp
      (tendsto_id.prodMk hu)
  exact ((hf.continuousAt (hS.mem_nhds hz)).tendsto.comp hu).congr_uniformity he

/-- A holomorphic map into the closed unit disc which vanishes at an interior
point of a connected domain takes all its values in the open disc. -/
theorem mapsTo_disc_of_holomorphic_base {D : Set ℂ} {a : ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hc : IsPreconnected D) (ha : a ∈ D)
    (hf : DifferentiableOn ℂ f D) (hb : MapsTo f D (closedBall 0 1)) (hfa : f a = 0) :
    MapsTo f D (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff]
  have hle : ‖f z‖ ≤ 1 := mem_closedBall_zero_iff.mp (hb hz)
  by_contra hnot
  have heq : ‖f z‖ = 1 := le_antisymm hle (le_of_not_gt hnot)
  have hm : IsMaxOn (norm ∘ f) D z := by
    intro w hw
    change ‖f w‖ ≤ ‖f z‖
    rw [heq]
    exact mem_closedBall_zero_iff.mp (hb hw)
  have he := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hc hD hf hz hm ha
  have : (0 : ℝ) = 1 := by
    simpa only [comp_apply, const_apply, hfa, norm_zero, heq] using he
  exact zero_ne_one this

/-- Simultaneous holomorphic limits of normalized Riemann maps and their inverses
give inverse bijections of the pointed kernel and the disc. In particular, the
inverse limiting image equals the kernel and neither limit degenerates. -/
theorem IsPointedKernel.bijOn_limits {a : ℂ} {D : Set ℂ} {Dseq : ℕ → Set ℂ}
    (hkernel : IsPointedKernel a D Dseq) (hopen : ∀ n, IsOpen (Dseq n))
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (Dseq n) a)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hb : MapsTo f D (closedBall 0 1))
    (hfa : f a = 0) (hga : g 0 = a)
    (hflim : TendstoLocallyUniformlyOn F f atTop D)
    (hglim : TendstoLocallyUniformlyOn
      (fun n => invFunOn (F n) (Dseq n)) g atTop (ball 0 1)) :
    BijOn f D (ball 0 1) ∧ BijOn g (ball 0 1) D ∧ InvOn g f D (ball 0 1) := by
  have hfmaps : MapsTo f D (ball 0 1) :=
    mapsTo_disc_of_holomorphic_base hkernel.isOpen hkernel.isPreconnected
      hkernel.base_mem hf hb hfa
  have hleft : LeftInvOn g f D := by
    intro z hz
    have ht := tendsto_eval_of_locallyUniformlyOn isOpen_ball hglim hg.continuousOn
      (hfmaps hz) (hflim.tendsto_at hz)
    have he : ∀ᶠ n in atTop, invFunOn (F n) (Dseq n) (F n z) = z := by
      filter_upwards [hkernel.eventuallyContainsCompacts {z} isCompact_singleton
        (singleton_subset_iff.mpr hz)] with n hn
      exact (hF n).injOn.leftInvOn_invFunOn (hn (mem_singleton z))
    exact tendsto_nhds_unique ((tendsto_congr' he).mp ht) tendsto_const_nhds
  have hgnc : ¬ ∃ c : ℂ, EqOn g (fun _ => c) (ball 0 1) := by
    rintro ⟨c, hc⟩
    have haeq : a = c := (hleft hkernel.base_mem).symm.trans (hc (hfmaps hkernel.base_mem))
    have heq : D = {a} := by
      apply Subset.antisymm
      · intro z hz
        exact mem_singleton_iff.mpr
          (((hleft hz).symm.trans (hc (hfmaps hz))).trans haeq.symm)
      · exact singleton_subset_iff.mpr hkernel.base_mem
    exact not_isOpen_singleton a (heq ▸ hkernel.isOpen)
  have hGhol : ∀ n, DifferentiableOn ℂ (invFunOn (F n) (Dseq n)) (ball 0 1) := by
    intro n
    simpa only [(hF n).image_eq] using
      DifferentiableOn.invFunOn (hF n).differentiableOn (hopen n) (hF n).injOn
  have hGmaps : ∀ n, MapsTo (invFunOn (F n) (Dseq n)) (ball 0 1) (Dseq n) := by
    intro n
    exact (BijOn.symm (hF n).bijOn.invOn_invFunOn.symm (hF n).bijOn).mapsTo
  have himage : g '' ball 0 1 ⊆ D := hkernel.holomorphic_image_subset
    isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected hGhol hGmaps hglim hgnc
      ⟨0, mem_ball_self zero_lt_one, hga⟩
  have hgmaps : MapsTo g (ball 0 1) D := fun w hw => himage ⟨w, hw, rfl⟩
  have hright : RightInvOn g f (ball 0 1) := by
    intro w hw
    have ht := tendsto_eval_of_locallyUniformlyOn hkernel.isOpen hflim hf.continuousOn
      (hgmaps hw) (hglim.tendsto_at hw)
    have he : ∀ᶠ n in atTop, F n (invFunOn (F n) (Dseq n) w) = w :=
      Eventually.of_forall fun n => (hF n).surjOn.rightInvOn_invFunOn hw
    exact tendsto_nhds_unique ((tendsto_congr' he).mp ht) tendsto_const_nhds
  exact ⟨⟨hfmaps, hleft.injOn, hright.surjOn hgmaps⟩,
    ⟨hgmaps, hright.injOn, hleft.surjOn hfmaps⟩, hleft, hright⟩

#print axioms tendsto_eval_of_locallyUniformlyOn
#print axioms mapsTo_disc_of_holomorphic_base
#print axioms IsPointedKernel.bijOn_limits

end MaxModulusPoints.ConformalKernel
