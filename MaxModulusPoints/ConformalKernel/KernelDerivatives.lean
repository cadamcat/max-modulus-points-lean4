module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import MaxModulusPoints.ConformalKernel.KernelConvergence
public import MaxModulusPoints.ConformalKernel.KernelLimits
public import MaxModulusPoints.ConformalKernel.KernelNormalFamilies

/-!
# Derivative convergence and normalization on a pointed kernel

Eventual local holomorphy suffices for locally uniform convergence of derivatives.
For limits of normalized Riemann maps, injectivity prevents the limiting positive
real derivative from vanishing. Normalized uniqueness then identifies every
simultaneous subsequential limit with the prescribed map of the kernel.
-/


@[expose] public section

open Set Filter Function Metric
open scoped Topology ComplexOrder

namespace MaxModulusPoints.ConformalKernel

/-- Eventual holomorphy on a neighbourhood of each point suffices to pass local
uniform convergence to the derivatives, for an arbitrary indexing filter. -/
theorem deriv_locallyUniformlyOn_of_eventual_local_holomorphy
    {ι : Type*} {l : Filter ι} {D : Set ℂ} (hD : IsOpen D)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hlim : TendstoLocallyUniformlyOn F f l D)
    (hlocal : ∀ x ∈ D, ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) :
    TendstoLocallyUniformlyOn (fun n => deriv (F n)) (deriv f) l D := by
  rw [hD.tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  obtain ⟨U, hU, hxU, hUD, hFU⟩ := hlocal x hx
  exact (hU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp
    ((hlim.mono hUD).deriv hFU hU)) x hxU

/-- Derivatives converge locally uniformly on an open limiting domain when its
compact subsets are eventually contained in the holomorphy domains. -/
theorem deriv_locallyUniformlyOn_moving_domains {D : Set ℂ} {Dseq : ℕ → Set ℂ}
    (hD : IsOpen D) (hin : EventuallyContainsCompacts D Dseq)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) (Dseq n))
    (hlim : TendstoLocallyUniformlyOn F f atTop D) :
    TendstoLocallyUniformlyOn (fun n => deriv (F n)) (deriv f) atTop D := by
  apply deriv_locallyUniformlyOn_of_eventual_local_holomorphy hD hlim
  intro x hx
  obtain ⟨R, hR, hRD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx)
  have hclosed : closedBall x (R / 2) ⊆ D :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRD
  refine ⟨ball x (R / 2), isOpen_ball, mem_ball_self (half_pos hR),
    ball_subset_closedBall.trans hclosed, ?_⟩
  filter_upwards [hin (closedBall x (R / 2)) (isCompact_closedBall _ _) hclosed] with n hn
  exact (hF n).mono (ball_subset_closedBall.trans hn)

/-- A bijective holomorphic limit of positively normalized Riemann maps retains
positive real derivative at the base point, and hence the full normalization. -/
theorem isNormalizedRiemannMapOn_of_tendsto {D : Set ℂ} {Dseq : ℕ → Set ℂ} {a : ℂ}
    (hD : IsOpen D) (ha : a ∈ D) (hin : EventuallyContainsCompacts D Dseq)
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (Dseq n) a)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hbij : BijOn f D (ball 0 1))
    (hfa : f a = 0) (hlim : TendstoLocallyUniformlyOn F f atTop D) :
    TauCeti.IsNormalizedRiemannMapOn f D a := by
  have hd : Tendsto (fun n => deriv (F n) a) atTop (𝓝 (deriv f a)) :=
    (deriv_locallyUniformlyOn_moving_domains hD hin
      (fun n => (hF n).differentiableOn) hlim).tendsto_at ha
  have hre : 0 ≤ (deriv f a).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hd)
      (Eventually.of_forall fun n => (Complex.pos_iff.mp (hF n).deriv_pos).1.le)
  have him_n : ∀ n, (deriv (F n) a).im = 0 :=
    fun n => (Complex.pos_iff.mp (hF n).deriv_pos).2.symm
  have him : (deriv f a).im = 0 := by
    have hc : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (deriv f a).im) := by
      exact (tendsto_congr' (Eventually.of_forall him_n)).mp
        ((Complex.continuous_im.tendsto _).comp hd)
    exact tendsto_nhds_unique hc tendsto_const_nhds
  have hne : deriv f a ≠ 0 := TauCeti.deriv_ne_zero_of_injOn hf hD hbij.injOn ha
  have hrne : (deriv f a).re ≠ 0 := fun he => hne (Complex.ext he him)
  exact ⟨ha, hf, hbij, hfa,
    Complex.pos_iff.mpr ⟨lt_of_le_of_ne hre hrne.symm, him.symm⟩⟩

/-- Kernel convergence gives a subsequence of normalized maps converging to the
prescribed normalized map, with simultaneous inverse and derivative convergence. -/
theorem KernelConverges.exists_normalized_subsequence {a : ℂ} {D A : Set ℂ}
    {Dseq : ℕ → Set ℂ} (hkernel : KernelConverges a D Dseq)
    (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ)
    (hsource : ∀ n, Dseq n ⊆ A) (hopen : ∀ n, IsOpen (Dseq n))
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (Dseq n) a)
    {f₀ : ℂ → ℂ} (hf₀ : TauCeti.IsNormalizedRiemannMapOn f₀ D a) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) f₀ atTop D ∧
      TendstoLocallyUniformlyOn (fun n => invFunOn (F (φ n)) (Dseq (φ n)))
        (invFunOn f₀ D) atTop (ball 0 1) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (F (φ n))) (deriv f₀) atTop D := by
  have hker : IsPointedKernel a D Dseq := hkernel id strictMono_id
  obtain ⟨f, g, hf, hg, hb, _, hfa, hga, φ, hφ, hflim, hglim⟩ :=
    exists_joint_subsequence_riemannMaps hker.isOpen hker.base_mem
      hker.eventuallyContainsCompacts hA hsA hpA hsource hopen hF
  have hkφ := hkernel φ hφ
  obtain ⟨hbijf, hbijg, hinv⟩ := hkφ.bijOn_limits (fun n => hopen (φ n))
    (fun n => hF (φ n)) hf hg hb hfa hga hflim hglim
  have hnorm := isNormalizedRiemannMapOn_of_tendsto hkφ.isOpen hkφ.base_mem
    hkφ.eventuallyContainsCompacts (fun n => hF (φ n)) hf hbijf hfa hflim
  have heq : EqOn f f₀ D := hnorm.eqOn hf₀ hkφ.isOpen
  have hgeq : EqOn g (invFunOn f₀ D) (ball 0 1) := by
    intro w hw
    calc
      g w = invFunOn f₀ D (f₀ (g w)) :=
        (hf₀.injOn.leftInvOn_invFunOn (hbijg.mapsTo hw)).symm
      _ = invFunOn f₀ D w := by rw [← heq (hbijg.mapsTo hw), hinv.2 hw]
  have hflim₀ := hflim.congr_right heq
  exact ⟨φ, hφ, hflim₀, hglim.congr_right hgeq,
    deriv_locallyUniformlyOn_moving_domains hkφ.isOpen hkφ.eventuallyContainsCompacts
      (fun n => (hF (φ n)).differentiableOn) hflim₀⟩

#print axioms deriv_locallyUniformlyOn_of_eventual_local_holomorphy
#print axioms deriv_locallyUniformlyOn_moving_domains
#print axioms isNormalizedRiemannMapOn_of_tendsto
#print axioms KernelConverges.exists_normalized_subsequence

end MaxModulusPoints.ConformalKernel
