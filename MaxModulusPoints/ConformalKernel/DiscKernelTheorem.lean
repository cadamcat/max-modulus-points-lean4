module

public import MaxModulusPoints.ConformalKernel.KernelConvergence
public import MaxModulusPoints.ConformalKernel.KernelDerivatives

/-!
# The normalized disc-map kernel theorem

When moving domains in a common proper simply connected ambient domain converge
to a nondegenerate pointed kernel, their positively normalized Riemann maps
converge locally uniformly to the normalized map of the kernel. Their inverses
and forward derivatives converge locally uniformly as well.
-/


@[expose] public section

open Set Filter Function Metric
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

/-- Local uniform convergence follows when every strict subsequence admits a
further strict subsequence converging locally uniformly to the same limit. -/
theorem locallyUniformlyOn_of_subsequences {D : Set ℂ} (hD : IsOpen D)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f atTop D) :
    TendstoLocallyUniformlyOn F f atTop D := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hD]
  intro K hKD hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hfail
  have hfreq : ∃ᶠ n in atTop, ¬ ∀ z ∈ K, dist (f z) (F n z) < ε :=
    not_eventually.mp hfail
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, _, hlim⟩ := hsub φ hφ
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp hlim K hKD hK
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu ε hε).exists
  exact hbad (ψ n) hn

/-- The normalized Riemann maps of kernel-converging domains converge locally
uniformly, together with their canonical inverses and their derivatives. -/
theorem KernelConverges.normalized_maps_tendsto {a : ℂ} {D A : Set ℂ}
    {Dseq : ℕ → Set ℂ} (hkernel : KernelConverges a D Dseq)
    (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ)
    (hsource : ∀ n, Dseq n ⊆ A) (hopen : ∀ n, IsOpen (Dseq n))
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (Dseq n) a)
    {f₀ : ℂ → ℂ} (hf₀ : TauCeti.IsNormalizedRiemannMapOn f₀ D a) :
    TendstoLocallyUniformlyOn F f₀ atTop D ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (Dseq n))
        (invFunOn f₀ D) atTop (ball 0 1) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (F n)) (deriv f₀) atTop D := by
  have hker : IsPointedKernel a D Dseq := hkernel id strictMono_id
  have hsub : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun n => F (φ (ψ n))) f₀ atTop D ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F (φ (ψ n))) (Dseq (φ (ψ n))))
        (invFunOn f₀ D) atTop (ball 0 1) := by
    intro φ hφ
    have hkφ : KernelConverges a D (Dseq ∘ φ) :=
      fun ψ hψ => hkernel (φ ∘ ψ) (hφ.comp hψ)
    obtain ⟨ψ, hψ, hf, hg, _⟩ := hkφ.exists_normalized_subsequence hA hsA hpA
      (fun n => hsource (φ n)) (fun n => hopen (φ n)) (fun n => hF (φ n)) hf₀
    exact ⟨ψ, hψ, hf, hg⟩
  have hf : TendstoLocallyUniformlyOn F f₀ atTop D :=
    locallyUniformlyOn_of_subsequences hker.isOpen fun φ hφ => by
      obtain ⟨ψ, hψ, hf, _⟩ := hsub φ hφ
      exact ⟨ψ, hψ, hf⟩
  have hg : TendstoLocallyUniformlyOn (fun n => invFunOn (F n) (Dseq n))
      (invFunOn f₀ D) atTop (ball 0 1) :=
    locallyUniformlyOn_of_subsequences isOpen_ball fun φ hφ => by
      obtain ⟨ψ, hψ, _, hg⟩ := hsub φ hφ
      exact ⟨ψ, hψ, hg⟩
  exact ⟨hf, hg, deriv_locallyUniformlyOn_moving_domains hker.isOpen
    hker.eventuallyContainsCompacts (fun n => (hF n).differentiableOn) hf⟩

#print axioms locallyUniformlyOn_of_subsequences
#print axioms KernelConverges.normalized_maps_tendsto

end MaxModulusPoints.ConformalKernel
