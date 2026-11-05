module

public import TauCeti.Analysis.Complex.Conformal.Inverse.Function
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Normalization
public import OAI.Analysis.SymmetricDomains.MontelExpandingDomains
public import Mathlib.Analysis.Complex.Schwarz

/-!
# Normal families in a common ambient domain

Holomorphic maps from the unit disc into a fixed proper simply connected plane
domain form a normal family when they take the origin to a common point.
Schwarz's lemma in an ambient Riemann chart traps their values on each smaller
disc in a fixed compact subset of the ambient domain.
-/


@[expose] public section

open Set Filter Function Metric
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

/-- A common base value traps every smaller closed disc in a fixed compact
subset of the proper simply connected ambient domain. -/
theorem exists_compact_trap_disc_maps {A : Set ℂ} {a : ℂ}
    (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ) (ha : a ∈ A)
    {r : ℝ} (hr : r < 1) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ A ∧
      ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) →
        MapsTo f (ball 0 1) A → f 0 = a → MapsTo f (closedBall 0 r) K := by
  obtain ⟨ψ, hψ⟩ := TauCeti.exists_isNormalizedRiemannMapOn hA hsA hpA ha
  let j : ℂ → ℂ := invFunOn ψ A
  have hjbij : BijOn j (ball 0 1) A :=
    BijOn.symm hψ.bijOn.invOn_invFunOn.symm hψ.bijOn
  have hjhol : DifferentiableOn ℂ j (ball 0 1) := by
    simpa only [hψ.image_eq] using
      DifferentiableOn.invFunOn hψ.differentiableOn hA hψ.bijOn.injOn
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hr)
  refine ⟨j '' closedBall 0 r,
    (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
      (hjhol.continuousOn.mono hsub), ?_, ?_⟩
  · exact (image_mono hsub).trans hjbij.mapsTo.image_subset
  · intro f hf hmaps hbase w hw
    have hcomp : DifferentiableOn ℂ (ψ ∘ f) (ball 0 1) :=
      hψ.differentiableOn.comp hf hmaps
    have hdisc : MapsTo (ψ ∘ f) (ball 0 1) (closedBall 0 1) :=
      (hψ.mapsTo.comp hmaps).mono_right ball_subset_closedBall
    have hzero : (ψ ∘ f) 0 = 0 := by simp only [comp_apply, hbase, hψ.map_base]
    have hnorm : ‖ψ (f w)‖ ≤ ‖w‖ :=
      Complex.norm_le_norm_of_mapsTo_ball hcomp hdisc hzero
        (mem_ball_zero_iff.mp (hsub hw))
    refine ⟨ψ (f w), mem_closedBall_zero_iff.mpr
      (hnorm.trans (mem_closedBall_zero_iff.mp hw)), ?_⟩
    exact hψ.injOn.leftInvOn_invFunOn (hmaps (hsub hw))

/-- Disc maps into a common proper simply connected ambient domain, with a
common value at zero, have a holomorphic locally uniform subsequential limit
which still takes its values in that domain and preserves the base value. -/
theorem normalFamily_disc_maps {A : Set ℂ} {a : ℂ}
    (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ) (ha : a ∈ A)
    {F : ℕ → ℂ → ℂ}
    (hhol : ∀ n, DifferentiableOn ℂ (F n) (ball 0 1))
    (hmaps : ∀ n, MapsTo (F n) (ball 0 1) A) (hbase : ∀ n, F n 0 = a) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧
      MapsTo g (ball 0 1) A ∧ g 0 = a ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop (ball 0 1) := by
  have htrap : ∀ r : ℝ, r < 1 → ∃ K : Set ℂ, IsCompact K ∧ K ⊆ A ∧
      ∀ n, MapsTo (F n) (closedBall 0 r) K := by
    intro r hr
    obtain ⟨K, hK, hKA, hF⟩ := exists_compact_trap_disc_maps hA hsA hpA ha hr
    exact ⟨K, hK, hKA, fun n => hF (F n) (hhol n) (hmaps n) (hbase n)⟩
  have hlocal : ∀ x ∈ ball (0 : ℂ) 1, ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 < M ∧
      ball x ρ ⊆ ball 0 1 ∧ ∀ᶠ n in atTop,
        DifferentiableOn ℂ (F n) (ball x ρ) ∧
          ∀ y ∈ ball x ρ, ‖F n y‖ ≤ M := by
    intro x hx
    obtain ⟨r, hxr, hr⟩ := exists_between (mem_ball_zero_iff.mp hx)
    obtain ⟨ρ, hρ, hρr⟩ := exists_ball_subset_ball (mem_ball_zero_iff.mpr hxr)
    obtain ⟨K, hK, _, hFK⟩ := htrap r hr
    obtain ⟨M, hM, hb⟩ := hK.isBounded.exists_pos_norm_le
    have hρ1 : ball x ρ ⊆ ball 0 1 := hρr.trans (ball_subset_ball hr.le)
    exact ⟨ρ, hρ, M, hM, hρ1, Eventually.of_forall fun n =>
      ⟨(hhol n).mono hρ1, fun y hy => hb _ (hFK n (ball_subset_closedBall (hρr hy)))⟩⟩
  obtain ⟨g, hg, φ, hφ, hlim⟩ :=
    OAI.Release061.montel_expanding_domains isOpen_ball F hlocal
  refine ⟨g, hg, ?_, ?_, φ, hφ, hlim⟩
  · intro x hx
    obtain ⟨r, hxr, hr⟩ := exists_between (mem_ball_zero_iff.mp hx)
    obtain ⟨K, hK, hKA, hFK⟩ := htrap r hr
    apply hKA
    exact hK.isClosed.mem_of_tendsto (hlim.tendsto_at hx)
      (Eventually.of_forall fun n => hFK (φ n)
        (mem_closedBall_zero_iff.mpr hxr.le))
  · have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
    have hc : Tendsto (fun _ : ℕ => a) atTop (𝓝 (g 0)) := by
      simpa only [hbase] using hlim.tendsto_at hz
    exact tendsto_nhds_unique hc tendsto_const_nhds

#print axioms exists_compact_trap_disc_maps
#print axioms normalFamily_disc_maps

end MaxModulusPoints.ConformalKernel
