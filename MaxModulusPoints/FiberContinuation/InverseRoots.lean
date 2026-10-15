import MaxModulusPoints.FiberContinuation.InverseCoordinates
/-!
# Exact finite inverse-root families

Local power coordinates enumerate physical inverse roots by roots of unity.
The enumeration is exact on a fixed neighborhood of the physical root.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology

/-- Equal powers differ by a root of unity, including when both bases vanish. -/
theorem exists_root_of_unity_mul {n : ℕ} (hn : 0 < n) {x y : ℂ}
    (hxy : x ^ n = y ^ n) :
    ∃ ζ : ℂ, ζ ^ n = 1 ∧ x = ζ * y := by
  by_cases hy : y = 0
  · have hx : x = 0 := by
      by_contra hx
      exact pow_ne_zero n hx (by simpa only [hy, zero_pow (Nat.ne_of_gt hn)] using hxy)
    exact ⟨1, one_pow n, by simp [hx, hy]⟩
  · refine ⟨x / y, ?_, ?_⟩
    · rw [div_pow, hxy, div_self (pow_ne_zero n hy)]
    · exact (div_mul_cancel₀ x hy).symm

/-- The finite root-of-unity index set for a local power coordinate. -/
abbrev PowerRootIndex (n : ℕ) :=
  {ζ : ℂ // ζ ∈ Polynomial.nthRootsFinset n (1 : ℂ)}

/-- The inverse roots over a common power parameter. -/
def inverseRoot {h : ℂ → ℂ} {a : ℂ} (c : LocalPowerCoordinate h a)
    (k : ℕ) (ζ : PowerRootIndex c.order) (t : ℂ) : ℂ :=
  c.inverse (ζ.val * t ^ k)

theorem inverseRoot_center {h : ℂ → ℂ} {a : ℂ} (c : LocalPowerCoordinate h a)
    {k : ℕ} (hk : 0 < k) (ζ : PowerRootIndex c.order) :
    inverseRoot c k ζ 0 = a := by
  simp [inverseRoot, Nat.ne_of_gt hk, c.inverse_center]

theorem analyticAt_inverseRoot {h : ℂ → ℂ} {a : ℂ}
    (c : LocalPowerCoordinate h a) {k : ℕ} (hk : 0 < k)
    (ζ : PowerRootIndex c.order) : AnalyticAt ℂ (inverseRoot c k ζ) 0 := by
  have hparam : AnalyticAt ℂ (fun t : ℂ => ζ.val * t ^ k) 0 :=
    analyticAt_const.mul (analyticAt_id.pow k)
  have hc : AnalyticAt ℂ c.inverse (ζ.val * (0 : ℂ) ^ k) := by
    simpa [Nat.ne_of_gt hk] using c.analytic_inverse
  exact AnalyticAt.comp (f := fun t : ℂ => ζ.val * t ^ k) (g := c.inverse) hc hparam

/-- On one fixed source neighborhood, every nearby inverse root is represented
by the finite family at that same parameter. -/
theorem exists_exact_inverse_root_family {h : ℂ → ℂ} {a : ℂ}
    (c : LocalPowerCoordinate h a) {k : ℕ} (hk : 0 < k) :
    ∃ (U : Set ℂ) (δ : ℝ), IsOpen U ∧ a ∈ U ∧ 0 < δ ∧
      ∀ t ∈ ball (0 : ℂ) δ,
        {z ∈ U | h z = h a + t ^ (k * c.order)} =
          range (fun ζ : PowerRootIndex c.order => inverseRoot c k ζ t) := by
  classical
  obtain ⟨r, hr, hsource⟩ := nhds_basis_ball.eventually_iff.mp
    (c.left_inverse.and c.normal_form)
  let U : Set ℂ := ball a r
  have ha : a ∈ U := mem_ball_self hr
  have hforward : ∀ ζ : PowerRootIndex c.order, ∀ᶠ t in 𝓝 (0 : ℂ),
      inverseRoot c k ζ t ∈ U ∧
        h (inverseRoot c k ζ t) = h a + t ^ (k * c.order) := by
    intro ζ
    have hζ : ζ.val ^ c.order = 1 :=
      (Polynomial.mem_nthRootsFinset c.order_pos 1).mp ζ.property
    have hcont := (analyticAt_inverseRoot c hk ζ).continuousAt
    have hUevent : ∀ᶠ t in 𝓝 (0 : ℂ), inverseRoot c k ζ t ∈ U := by
      apply hcont.eventually
      rw [inverseRoot_center c hk ζ]
      exact isOpen_ball.mem_nhds ha
    have hpcont : ContinuousAt (fun t : ℂ => ζ.val * t ^ k) 0 := by fun_prop
    have hptendsto : Tendsto (fun t : ℂ => ζ.val * t ^ k) (𝓝 0) (𝓝 0) := by
      simpa [Nat.ne_of_gt hk] using hpcont.tendsto
    filter_upwards [hUevent, hptendsto.eventually c.inverse_normal_form]
      with t ht hform
    refine ⟨ht, ?_⟩
    simpa only [inverseRoot, mul_pow, hζ, one_mul, ← pow_mul] using hform
  obtain ⟨δ, hδ, hforwardδ⟩ := nhds_basis_ball.eventually_iff.mp
    (eventually_all.mpr hforward)
  refine ⟨U, δ, isOpen_ball, ha, hδ, ?_⟩
  intro t ht
  ext z
  constructor
  · rintro ⟨hzU, hvalue⟩
    obtain ⟨hleft, hform⟩ := hsource hzU
    have hpower : c.coordinate z ^ c.order = (t ^ k) ^ c.order := by
      rw [← pow_mul]
      exact add_left_cancel (hform.symm.trans hvalue)
    obtain ⟨ζ, hζ, heq⟩ := exists_root_of_unity_mul c.order_pos hpower
    let i : PowerRootIndex c.order :=
      ⟨ζ, (Polynomial.mem_nthRootsFinset c.order_pos 1).mpr hζ⟩
    refine ⟨i, ?_⟩
    change c.inverse (ζ * t ^ k) = z
    rw [← heq]
    exact hleft
  · rintro ⟨ζ, rfl⟩
    exact hforwardδ ht ζ

end MaxModulusPoints.FiberContinuation
