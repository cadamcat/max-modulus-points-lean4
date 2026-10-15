import MaxModulusPoints.ConformalKernel.KernelConvergence
import MaxModulusPoints.ConformalKernel.NormalFamilies
/-!
# Simultaneous normal limits on moving domains

Eventual compact inclusion and a uniform range bound give subsequential
holomorphic limits on the limiting domain. For normalized Riemann maps whose
source domains lie in a common proper simply connected ambient domain, one can
extract the maps and their inverses along a single subsequence.
-/

open Set Filter Function Metric
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

/-- A bounded holomorphic family on moving domains has a locally uniform
subsequential limit on every open set with eventual compact inclusion. -/
theorem normalFamily_moving_domains {D : Set ℂ} {Dseq : ℕ → Set ℂ}
    (hD : IsOpen D) (hin : EventuallyContainsCompacts D Dseq)
    {F : ℕ → ℂ → ℂ} (hhol : ∀ n, DifferentiableOn ℂ (F n) (Dseq n))
    {M : ℝ} (hM : 0 < M) (hbound : ∀ n z, z ∈ Dseq n → ‖F n z‖ ≤ M) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f D ∧ (∀ z ∈ D, ‖f z‖ ≤ M) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop D := by
  have hlocal : ∀ x ∈ D, ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, 0 < B ∧
      ball x r ⊆ D ∧ ∀ᶠ n in atTop,
        DifferentiableOn ℂ (F n) (ball x r) ∧ ∀ y ∈ ball x r, ‖F n y‖ ≤ B := by
    intro x hx
    obtain ⟨R, hR, hRD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx)
    have hclosed : closedBall x (R / 2) ⊆ D :=
      (closedBall_subset_ball (half_lt_self hR)).trans hRD
    have he := hin (closedBall x (R / 2)) (isCompact_closedBall _ _) hclosed
    refine ⟨R / 2, half_pos hR, M, hM, ball_subset_closedBall.trans hclosed, ?_⟩
    filter_upwards [he] with n hn
    have hball : ball x (R / 2) ⊆ Dseq n := ball_subset_closedBall.trans hn
    exact ⟨(hhol n).mono hball, fun y hy => hbound n y (hball hy)⟩
  obtain ⟨f, hf, φ, hφ, hlim⟩ :=
    OAI.Release061.montel_expanding_domains hD F hlocal
  refine ⟨f, hf, ?_, φ, hφ, hlim⟩
  intro z hz
  have he := hφ.tendsto_atTop
    (hin {z} isCompact_singleton (singleton_subset_iff.mpr hz))
  apply le_of_tendsto (hlim.tendsto_at hz).norm
  filter_upwards [he] with n hn
  exact hbound (φ n) z (hn (mem_singleton z))

/-- Normalized Riemann maps and their canonical inverses have simultaneous
holomorphic subsequential limits. The forward limit takes values in the closed
unit disc, and the inverse limit stays in the common ambient domain. -/
theorem exists_joint_subsequence_riemannMaps {D A : Set ℂ} {Dseq : ℕ → Set ℂ}
    {a : ℂ} (hD : IsOpen D) (haD : a ∈ D)
    (hin : EventuallyContainsCompacts D Dseq)
    (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ)
    (hsource : ∀ n, Dseq n ⊆ A) (hopen : ∀ n, IsOpen (Dseq n))
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, TauCeti.IsNormalizedRiemannMapOn (F n) (Dseq n) a) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f D ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      MapsTo f D (closedBall 0 1) ∧ MapsTo g (ball 0 1) A ∧
      f a = 0 ∧ g 0 = a ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop D ∧
        TendstoLocallyUniformlyOn
          (fun n => invFunOn (F (φ n)) (Dseq (φ n))) g atTop (ball 0 1) := by
  have hb : ∀ n z, z ∈ Dseq n → ‖F n z‖ ≤ (1 : ℝ) :=
    fun n z hz => (mem_ball_zero_iff.mp ((hF n).mapsTo hz)).le
  obtain ⟨f, hf, hfb, φ, hφ, hflim⟩ :=
    normalFamily_moving_domains hD hin (fun n => (hF n).differentiableOn) zero_lt_one hb
  let G : ℕ → ℂ → ℂ := fun n => invFunOn (F (φ n)) (Dseq (φ n))
  have hGbij : ∀ n, BijOn (G n) (ball 0 1) (Dseq (φ n)) := fun n =>
    BijOn.symm (hF (φ n)).bijOn.invOn_invFunOn.symm (hF (φ n)).bijOn
  have hGhol : ∀ n, DifferentiableOn ℂ (G n) (ball 0 1) := by
    intro n
    simpa only [(hF (φ n)).image_eq] using
      DifferentiableOn.invFunOn (hF (φ n)).differentiableOn
        (hopen (φ n)) (hF (φ n)).injOn
  have hGbase : ∀ n, G n 0 = a := by
    intro n
    change invFunOn (F (φ n)) (Dseq (φ n)) 0 = a
    rw [← (hF (φ n)).map_base]
    exact (hF (φ n)).injOn.leftInvOn_invFunOn (hF (φ n)).base_mem
  have haA : a ∈ A := hsource 0 (hF 0).base_mem
  obtain ⟨g, hg, hgA, hga, ψ, hψ, hglim⟩ := normalFamily_disc_maps hA hsA hpA haA
    hGhol (fun n => (hGbij n).mapsTo.mono_right (hsource (φ n))) hGbase
  have hfa : f a = 0 := by
    have hc : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (f a)) := by
      simpa only [(hF _).map_base] using hflim.tendsto_at haD
    exact tendsto_nhds_unique hc tendsto_const_nhds
  refine ⟨f, g, hf, hg, fun z hz => mem_closedBall_zero_iff.mpr (hfb z hz),
    hgA, hfa, hga, φ ∘ ψ, hφ.comp hψ, ?_, hglim⟩
  intro u hu z hz
  obtain ⟨S, hS, he⟩ := hflim u hu z hz
  exact ⟨S, hS, hψ.tendsto_atTop he⟩

#print axioms normalFamily_moving_domains
#print axioms exists_joint_subsequence_riemannMaps

end MaxModulusPoints.ConformalKernel
