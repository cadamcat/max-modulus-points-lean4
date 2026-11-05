module

public import MaxModulusPoints.FiberContinuation.InverseCoordinates
public import MaxModulusPoints.FiberContinuation.InverseRoots
public import MaxModulusPoints.FiberContinuation.ValueCoordinates

/-!
# Exact inverse families in spherical value charts

A finite collection of local orders has one positive common power. Each local
analytic power coordinate then gives an exact finite family of physical roots
over that common parameter in either a finite or an infinite value chart.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology

universe u

/-- A finite collection of positive orders admits a positive common power. -/
theorem exists_common_power {ι : Type u} [Finite ι] (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) : ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ k : ℕ, 0 < k ∧ N = k * n i := by
  classical
  letI := Fintype.ofFinite ι
  let N : ℕ := ∏ i, n i
  have hN : 0 < N := Finset.prod_pos (fun i _ => hn i)
  refine ⟨N, hN, ?_⟩
  intro i
  have hdvd : n i ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hNzero : N = 0 := by simpa only [hzero, mul_zero] using hk
    exact (Nat.ne_of_gt hN) hNzero
  exact ⟨k, hkpos, hk.trans (mul_comm _ _)⟩

/-- The exact local inverse-root family also enumerates the actual spherical
values when an injective value chart represents the analytic germ. -/
theorem exists_exact_spherical_inverse_family {h : ℂ → ℂ} {a : ℂ}
    (c : LocalPowerCoordinate h a) (hzero : h a = 0)
    (A : ℂ → OnePoint ℂ) (p : OnePoint ℂ)
    (hrep : ∀ᶠ z in 𝓝 a, A z = centeredValue p (h z))
    {k : ℕ} (hk : 0 < k) :
    ∃ (U : Set ℂ) (δ : ℝ), IsOpen U ∧ a ∈ U ∧ 0 < δ ∧
      ∀ t ∈ ball (0 : ℂ) δ,
        {z ∈ U | A z = centeredValue p (t ^ (k * c.order))} =
          range (fun ζ : PowerRootIndex c.order => inverseRoot c k ζ t) := by
  classical
  obtain ⟨r, hr, hrepball⟩ := nhds_basis_ball.eventually_iff.mp hrep
  obtain ⟨U₀, δ₀, hU₀, haU₀, hδ₀, hexact⟩ := exists_exact_inverse_root_family c hk
  have hrootrep : ∀ ζ : PowerRootIndex c.order, ∀ᶠ t in 𝓝 (0 : ℂ),
      inverseRoot c k ζ t ∈ ball a r := by
    intro ζ
    apply (analyticAt_inverseRoot c hk ζ).continuousAt.eventually
    rw [inverseRoot_center c hk ζ]
    exact ball_mem_nhds a hr
  have hparams : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ ball 0 δ₀ ∧
      ∀ ζ : PowerRootIndex c.order, inverseRoot c k ζ t ∈ ball a r :=
    Filter.Eventually.and (ball_mem_nhds 0 hδ₀) (eventually_all.mpr hrootrep)
  obtain ⟨δ, hδ, hsmall⟩ := nhds_basis_ball.eventually_iff.mp hparams
  refine ⟨U₀ ∩ ball a r, δ, hU₀.inter isOpen_ball,
    ⟨haU₀, mem_ball_self hr⟩, hδ, ?_⟩
  intro t ht
  have hexactt := hexact t (hsmall ht).1
  ext z
  constructor
  · rintro ⟨⟨hzU₀, hzrep⟩, hzvalue⟩
    have hcoord : h z = t ^ (k * c.order) := centeredValue_injective p
      ((hrepball hzrep).symm.trans hzvalue)
    rw [← hexactt]
    exact ⟨hzU₀, by simpa only [hzero, zero_add] using hcoord⟩
  · rintro ⟨ζ, rfl⟩
    have hzbase : inverseRoot c k ζ t ∈ {z ∈ U₀ | h z = h a + t ^ (k * c.order)} := by
      rw [hexactt]
      exact mem_range_self ζ
    have hzrep := (hsmall ht).2 ζ
    refine ⟨⟨hzbase.1, hzrep⟩, ?_⟩
    exact (hrepball hzrep).trans (congrArg (centeredValue p)
      (by simpa only [hzero, zero_add] using hzbase.2))

end MaxModulusPoints.FiberContinuation
