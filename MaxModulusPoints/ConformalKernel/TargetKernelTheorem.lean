module

public import MaxModulusPoints.ConformalKernel.DiscKernelTheorem
public import MaxModulusPoints.ConformalKernel.KernelConvergence
public import MaxModulusPoints.ConformalKernel.KernelDerivatives
public import MaxModulusPoints.ConformalKernel.NormalizedMaps

/-!
# Kernel convergence of normalized maps to a fixed target

A fixed normalized target chart transfers the disc-map kernel theorem to
conformal maps onto any proper simply connected plane domain. Forward maps,
canonical inverses and forward derivatives converge locally uniformly.
-/


@[expose] public section

open Set Filter Function Metric
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

/-- Continuous postcomposition preserves local uniform convergence when the
limit is continuous and the outer map is continuous at each limiting value. -/
theorem locallyUniformlyOn_continuous_comp {ι : Type*} {l : Filter ι}
    {D : Set ℂ} (hD : IsOpen D) {F : ι → ℂ → ℂ} {f j : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn F f l D) (hf : ContinuousOn f D)
    (hj : ∀ x ∈ D, ContinuousAt j (f x)) :
    TendstoLocallyUniformlyOn (fun n => j ∘ F n) (j ∘ f) l D := by
  rw [hD.tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  have ht : Tendsto (fun p : ι × ℂ => f p.2) (l ×ˢ 𝓝 x) (𝓝 (f x)) :=
    ((hf.continuousAt (hD.mem_nhds hx)).tendsto).comp tendsto_snd
  have hFt : Tendsto (fun p : ι × ℂ => F p.1 p.2) (l ×ˢ 𝓝 x) (𝓝 (f x)) :=
    ht.congr_uniformity ((hD.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp hlim) x hx)
  exact (((hj x hx).tendsto.comp ht).prodMk_nhds
    ((hj x hx).tendsto.comp hFt)).mono_right (nhds_le_uniformity _)

/-- Equality on moving domains preserves local uniform limits on any open
limiting domain with eventual compact inclusion. -/
theorem locallyUniformlyOn_congr_moving_domains {D : Set ℂ} {Dseq : ℕ → Set ℂ}
    (hD : IsOpen D) (hin : EventuallyContainsCompacts D Dseq)
    {F G : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (heq : ∀ n, EqOn (F n) (G n) (Dseq n)) :
    TendstoLocallyUniformlyOn G f atTop D := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hD] at hlim ⊢
  intro K hKD hK
  apply (hlim K hKD hK).congr
  filter_upwards [hin K hK hKD] with n hn z hz
  exact heq n (hn hz)

private theorem inverse_discMap_comp {V H : Set ℂ} {F ψ : ℂ → ℂ}
    (hF : BijOn F V H) (hψ : BijOn ψ H (ball 0 1)) :
    EqOn (invFunOn (ψ ∘ F) V ∘ ψ) (invFunOn F V) H := by
  intro w hw
  have hbij : BijOn (invFunOn F V) H V :=
    BijOn.symm hF.invOn_invFunOn.symm hF
  have he := (hψ.comp hF).injOn.leftInvOn_invFunOn (hbij.mapsTo hw)
  simpa only [comp_apply, hF.surjOn.rightInvOn_invFunOn hw] using he

/-- Positively normalized conformal maps to a fixed proper simply connected
target converge under kernel convergence, together with inverses and derivatives. -/
theorem KernelConverges.conformal_maps_tendsto {a b : ℂ} {D A H : Set ℂ}
    {Dseq : ℕ → Set ℂ} (hkernel : KernelConverges a D Dseq)
    (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ)
    (hH : IsOpen H) (hsH : IsSimplyConnected H) (hpH : H ≠ univ)
    (hsource : ∀ n, Dseq n ⊆ A) (hopen : ∀ n, IsOpen (Dseq n))
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, IsNormalizedConformalMap (Dseq n) H a b (F n))
    {F₀ : ℂ → ℂ} (hF₀ : IsNormalizedConformalMap D H a b F₀) :
    TendstoLocallyUniformlyOn F F₀ atTop D ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (Dseq n))
        (invFunOn F₀ D) atTop H ∧
      TendstoLocallyUniformlyOn (fun n => deriv (F n)) (deriv F₀) atTop D := by
  have hker : IsPointedKernel a D Dseq := hkernel id strictMono_id
  obtain ⟨ψ, hψ⟩ := TauCeti.exists_isNormalizedRiemannMapOn hH hsH hpH hF₀.target_mem
  let fseq : ℕ → ℂ → ℂ := fun n => ψ ∘ F n
  have hfseq : ∀ n, TauCeti.IsNormalizedRiemannMapOn (fseq n) (Dseq n) a :=
    fun n => normalized_discMap_comp (hopen n) hH (hF n) hψ
  have hf₀ := normalized_discMap_comp hker.isOpen hH hF₀ hψ
  obtain ⟨hd, hdi, _⟩ := hkernel.normalized_maps_tendsto hA hsA hpA hsource hopen hfseq hf₀
  let j : ℂ → ℂ := invFunOn ψ H
  have hj : DifferentiableOn ℂ j (ball 0 1) := by
    simpa only [hψ.image_eq] using
      DifferentiableOn.invFunOn hψ.differentiableOn hH hψ.injOn
  have hpost := locallyUniformlyOn_continuous_comp hker.isOpen hd hf₀.differentiableOn.continuousOn
    (fun z hz => (hj.differentiableAt (isOpen_ball.mem_nhds (hf₀.mapsTo hz))).continuousAt)
  have hrecover : ∀ n, EqOn (j ∘ fseq n) (F n) (Dseq n) :=
    fun n z hz => hψ.injOn.leftInvOn_invFunOn ((hF n).bijOn.mapsTo hz)
  have hforward : TendstoLocallyUniformlyOn F F₀ atTop D :=
    (locallyUniformlyOn_congr_moving_domains hker.isOpen
      hker.eventuallyContainsCompacts hpost hrecover).congr_right
        (fun z hz => hψ.injOn.leftInvOn_invFunOn (hF₀.bijOn.mapsTo hz))
  have hi := hdi.comp ψ hψ.mapsTo hψ.differentiableOn.continuousOn
  have hinverse : TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (Dseq n))
      (invFunOn F₀ D) atTop H :=
    (hi.congr (fun n => inverse_discMap_comp (hF n).bijOn hψ.bijOn)).congr_right
      (inverse_discMap_comp hF₀.bijOn hψ.bijOn)
  exact ⟨hforward, hinverse, deriv_locallyUniformlyOn_moving_domains hker.isOpen
    hker.eventuallyContainsCompacts (fun n => (hF n).differentiableOn) hforward⟩

#print axioms locallyUniformlyOn_continuous_comp
#print axioms locallyUniformlyOn_congr_moving_domains
#print axioms KernelConverges.conformal_maps_tendsto

end MaxModulusPoints.ConformalKernel
