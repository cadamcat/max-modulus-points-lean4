module

public import OAI.Analysis.Crouzeix.Hurwitz
public import Mathlib.Analysis.Complex.OpenMapping
public import MaxModulusPoints.ConformalKernel.KernelConvergence

/-!
# Compact images under holomorphic limits

For a nonconstant holomorphic locally uniform limit on a fixed domain, every
compact subset of its image lies in the images of all sufficiently late maps.
Applied to converging inverse conformal maps, this gives the image-to-kernel
inclusion in the Carathéodory kernel argument.
-/


@[expose] public section

open Set Filter Function
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

/-- A compact subset of the image of a nonconstant locally uniform holomorphic
limit is eventually contained in the images of the approximating maps. -/
theorem eventuallyContainsCompacts_holomorphic_image {W : Set ℂ}
    (hW : IsOpen W) (hc : IsPreconnected W) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) W)
    (hlim : TendstoLocallyUniformlyOn F g atTop W)
    (hnc : ¬ ∃ c : ℂ, EqOn g (fun _ => c) W) :
    EventuallyContainsCompacts (g '' W) (fun n => F n '' W) := by
  classical
  intro K hK hKg
  by_contra hfail
  have hfreq : ∃ᶠ n in atTop, ¬ K ⊆ F n '' W := not_eventually.mp hfail
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose z hzK hzout using fun n => Set.not_subset.mp (hbad n)
  obtain ⟨c, hcK, ψ, hψ, hzc⟩ := hK.tendsto_subseq hzK
  have hsubseq : TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) g atTop W := by
    intro u hu w hw
    obtain ⟨S, hS, he⟩ := hlim u hu w hw
    exact ⟨S, hS, (hφ.comp hψ).tendsto_atTop he⟩
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => z (ψ n))
      (fun _ => c) atTop W :=
    (hzc.tendstoUniformlyOn_const (s := W)).tendstoLocallyUniformlyOn
  have hdiff : TendstoLocallyUniformlyOn (fun n w => F (φ (ψ n)) w - z (ψ n))
      (fun w => g w - c) atTop W :=
    (uniformContinuous_fst.sub uniformContinuous_snd).comp_tendstoLocallyUniformlyOn
      (hsubseq.prodMk hconst)
  have hhol : ∀ n, DifferentiableOn ℂ (fun w => F (φ (ψ n)) w - z (ψ n)) W :=
    fun n => (hF (φ (ψ n))).sub_const _
  have hzero : ∀ n w, w ∈ W → F (φ (ψ n)) w - z (ψ n) ≠ 0 := by
    intro n w hw he
    exact hzout (ψ n) ⟨w, hw, sub_eq_zero.mp he⟩
  rcases OAI.CrouzeixHilbert.Conformal.zero_or_ne_of_tendstoLocallyUniformlyOn
      hW hc hdiff hhol hzero with heq | hne
  · exact hnc ⟨c, fun w hw => sub_eq_zero.mp (heq hw)⟩
  · obtain ⟨w, hw, hgw⟩ := hKg hcK
    exact hne w hw (sub_eq_zero.mpr hgw)

/-- A nonconstant locally uniform holomorphic limit of maps into moving domains
has its entire image in their pointed kernel, provided the image contains the base point. -/
theorem IsPointedKernel.holomorphic_image_subset {a : ℂ} {D : Set ℂ}
    {Dseq : ℕ → Set ℂ} (hkernel : IsPointedKernel a D Dseq)
    {W : Set ℂ} (hW : IsOpen W) (hc : IsPreconnected W)
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) W)
    (hmaps : ∀ n, MapsTo (F n) W (Dseq n))
    (hlim : TendstoLocallyUniformlyOn F g atTop W)
    (hnc : ¬ ∃ c : ℂ, EqOn g (fun _ => c) W) (ha : a ∈ g '' W) :
    g '' W ⊆ D := by
  have hg : DifferentiableOn ℂ g W :=
    hlim.differentiableOn (Eventually.of_forall hF) hW
  have hopen : IsOpen (g '' W) :=
    ((hg.analyticOnNhd hW).is_constant_or_isOpen hc).resolve_left hnc W Subset.rfl hW
  apply hkernel.maximal (g '' W) hopen (hc.image g hg.continuousOn) ha
  intro K hK hKg
  filter_upwards [eventuallyContainsCompacts_holomorphic_image hW hc hF hlim hnc K hK hKg]
    with n hn
  exact hn.trans (hmaps n).image_subset

#print axioms eventuallyContainsCompacts_holomorphic_image
#print axioms IsPointedKernel.holomorphic_image_subset

end MaxModulusPoints.ConformalKernel
