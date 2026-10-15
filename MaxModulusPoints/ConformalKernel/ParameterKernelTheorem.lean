import MaxModulusPoints.ConformalKernel.KernelConvergence
import MaxModulusPoints.ConformalKernel.NormalizedMaps
import MaxModulusPoints.ConformalKernel.TargetKernelTheorem
/-!
# Parameter dependence of normalized conformal maps

For countably generated parameter filters, sequential kernel convergence implies
locally uniform convergence of the normalized maps, their inverses and derivatives.
This is the parameter form of the kernel-continuity input in
Pardo-Simón–Sixsmith, Observation 2.3.
-/

open Set Filter Function
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

universe u

/-- Local uniform convergence on an open plane domain is detected by sequences
along any countably generated filter. -/
theorem locallyUniformlyOn_of_seq_tendstoLocallyUniformlyOn
    {P : Type u} {l : Filter P} [l.IsCountablyGenerated]
    {D : Set ℂ} (hD : IsOpen D) {F : P → ℂ → ℂ} {f : ℂ → ℂ}
    (hseq : ∀ v : ℕ → P, Tendsto v atTop l →
      TendstoLocallyUniformlyOn (fun n => F (v n)) f atTop D) :
    TendstoLocallyUniformlyOn F f l D := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hD]
  intro K hKD hK
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro v hv
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).mp (hseq v hv) K hKD hK

/-- Sequential kernel convergence gives parameter-filter convergence for
positively normalized maps to a fixed target, their inverses and derivatives. -/
theorem conformal_maps_tendsto_of_seq_kernel
    {P : Type u} {l : Filter P} [l.IsCountablyGenerated]
    {a b : ℂ} {D A H : Set ℂ} {domains : P → Set ℂ}
    (hD : IsOpen D)
    (hkernel : ∀ v : ℕ → P, Tendsto v atTop l →
      KernelConverges a D (fun n => domains (v n)))
    (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ)
    (hH : IsOpen H) (hsH : IsSimplyConnected H) (hpH : H ≠ univ)
    (hsource : ∀ p, domains p ⊆ A) (hopen : ∀ p, IsOpen (domains p))
    {F : P → ℂ → ℂ} (hF : ∀ p, IsNormalizedConformalMap (domains p) H a b (F p))
    {F₀ : ℂ → ℂ} (hF₀ : IsNormalizedConformalMap D H a b F₀) :
    TendstoLocallyUniformlyOn F F₀ l D ∧
      TendstoLocallyUniformlyOn (fun p => invFunOn (F p) (domains p))
        (invFunOn F₀ D) l H ∧
      TendstoLocallyUniformlyOn (fun p => deriv (F p)) (deriv F₀) l D := by
  have hseq (v : ℕ → P) (hv : Tendsto v atTop l) :=
    (hkernel v hv).conformal_maps_tendsto hA hsA hpA hH hsH hpH
      (fun n => hsource (v n)) (fun n => hopen (v n)) (fun n => hF (v n)) hF₀
  exact ⟨locallyUniformlyOn_of_seq_tendstoLocallyUniformlyOn hD
      (fun v hv => (hseq v hv).1),
    locallyUniformlyOn_of_seq_tendstoLocallyUniformlyOn hH
      (fun v hv => (hseq v hv).2.1),
    locallyUniformlyOn_of_seq_tendstoLocallyUniformlyOn hD
      (fun v hv => (hseq v hv).2.2)⟩

#print axioms locallyUniformlyOn_of_seq_tendstoLocallyUniformlyOn
#print axioms conformal_maps_tendsto_of_seq_kernel

end MaxModulusPoints.ConformalKernel
