module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Separation.Connected

/-!
# `MaxModulusPoints.Liminf.Basic`
-/

@[expose] public section

open scoped Filter Topology
open scoped ComplexConjugate

/-! Basic facts about exact maximum-modulus points on circles. -/

namespace MaxModulusPoints.Liminf

/-- The exact maximum points on a circle. -/
def maxPoints (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | ‖z‖ = r ∧ ∀ w, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖}

/-- Monomials include every constant function. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, ∃ n : ℕ, f = fun z => c * z ^ n

/-- A continuous function attains its maximum modulus on every circle of positive radius. -/
theorem exists_maximum_on_circle (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) : ∃ z, z ∈ maxPoints f r := by
  let s : Set ℂ := Metric.sphere 0 r
  have hne : s.Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp [s, hr.le]
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn hne
    (continuous_norm.comp hf.continuous).continuousOn
  refine ⟨z, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [s] using hz
  · intro w hw
    apply hmax
    simpa [s] using hw

/-- A nonzero entire function factors as a power at the origin times an entire function
nonvanishing there. -/
theorem exists_factorization_at_origin (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hfnz : ∃ z, f z ≠ 0) :
    ∃ m : ℕ, ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
      ∀ z, f z = z ^ m * g z := by
  have hfA : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hf0A : AnalyticAt ℂ f 0 := hfA 0 (Set.mem_univ 0)
  have hnot : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := by
    intro h
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 :=
      (h.filter_mono nhdsWithin_le_nhds).frequently
    have hzero := hfA.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ (0 : ℂ)) hfreq
    obtain ⟨z, hz⟩ := hfnz
    exact hz (hzero (Set.mem_univ z))
  have hfinite : analyticOrderAt f 0 ≠ ⊤ := by
    intro h
    exact hnot (analyticOrderAt_eq_top.mp h)
  let m : ℕ := analyticOrderNatAt f 0
  have horder : analyticOrderAt f 0 = m := by
    simpa [m] using (Nat.cast_analyticOrderNatAt hfinite).symm
  obtain ⟨u, hu, hu0, hfactor⟩ :=
    hf0A.analyticOrderAt_eq_natCast.mp horder
  have hfactor' : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ m * u z := by
    filter_upwards [hfactor] with z hz
    simpa [smul_eq_mul] using hz
  let g : ℂ → ℂ := fun z => if z = 0 then u 0 else f z / z ^ m
  have hgu : g =ᶠ[𝓝 (0 : ℂ)] u := by
    filter_upwards [hfactor'] with z hz
    by_cases hz0 : z = 0
    · subst z
      simp [g]
    · have hz' : f z = z ^ m * u z := hz
      simp [g, hz0, hz', pow_ne_zero m hz0]
  have hgd : Differentiable ℂ g := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact hu.differentiableAt.congr_of_eventuallyEq hgu
    · have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ m) z := by fun_prop
      have hd : DifferentiableAt ℂ (fun w : ℂ => f w / w ^ m) z :=
        hf.differentiableAt.div hpow (pow_ne_zero m hz)
      apply hd.congr_of_eventuallyEq
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      simp [g, hw]
  refine ⟨m, g, hgd, ?_, ?_⟩
  · simpa [g] using hu0
  · intro z
    by_cases hz : z = 0
    · subst z
      simpa [g] using hfactor'.self_of_nhds
    · simp only [g, if_neg hz]
      field_simp [pow_ne_zero m hz]

/-- If an entire function has constant modulus on a positive circle, it is a monomial. -/
theorem constant_modulus_on_circle_is_monomial (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r)
    (hmod : ∀ z, ‖z‖ = r → ‖f z‖ = ‖f (r : ℂ)‖) :
    IsMonomial f := by
  by_cases hfnz : ∃ z, f z ≠ 0
  · obtain ⟨m, g, hg, hg0, hfg⟩ := exists_factorization_at_origin f hf hfnz
    have hrComplex : ‖(r : ℂ)‖ = r := by
      simp [Real.norm_eq_abs, abs_of_pos hr]
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      norm_num
    have hSpherePre : IsPreconnected (Metric.sphere (0 : ℂ) r) :=
      isPreconnected_sphere hrank 0 r
    have hSphereNontrivial : (Metric.sphere (0 : ℂ) r).Nontrivial := by
      have hne : (r : ℂ) ≠ -(r : ℂ) := by
        intro h
        have h' : r = -r := by exact_mod_cast h
        linarith
      refine ⟨(r : ℂ), ?_, -(r : ℂ), ?_, hne⟩ <;>
        simp [Metric.mem_sphere, dist_eq_norm, hrComplex] <;> positivity
    have hSphereInf : (Metric.sphere (0 : ℂ) r).Infinite :=
      hSpherePre.infinite_of_nontrivial hSphereNontrivial
    obtain ⟨z₀, hz₀, hacc⟩ := hSphereInf.exists_accPt_of_subset_isCompact
      (isCompact_sphere (0 : ℂ) r) subset_rfl
    have hz₀norm : ‖z₀‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz₀
    have hz₀ne : z₀ ≠ 0 := by
      intro hz
      subst z₀
      have hr0 : r = 0 := by simpa using hz₀norm.symm
      linarith
    have hfA : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
    have hanchor : f (r : ℂ) ≠ 0 := by
      intro hzero
      have hfreq : ∃ᶠ z in 𝓝[≠] z₀, f z = 0 := by
        apply (accPt_iff_frequently_nhdsNE.mp hacc).mono
        intro z hz
        have hznorm : ‖z‖ = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz
        have hnorm : ‖f z‖ = 0 := by simpa [hzero] using hmod z hznorm
        exact norm_eq_zero.mp hnorm
      have hallzero := hfA.eqOn_zero_of_preconnected_of_frequently_eq_zero
        isPreconnected_univ (Set.mem_univ z₀) hfreq
      obtain ⟨w, hw⟩ := hfnz
      exact hw (hallzero (Set.mem_univ w))
    have hgr : g (r : ℂ) ≠ 0 := by
      intro hzero
      apply hanchor
      rw [hfg]
      simp [hzero]
    let C : ℝ := ‖g (r : ℂ)‖
    have hCpos : 0 < C := by
      exact norm_pos_iff.mpr hgr
    have hrpowpos : 0 < r ^ m := pow_pos hr m
    have hrpowne : r ^ m ≠ 0 := hrpowpos.ne'
    have hnormfactor (z : ℂ) (hz : ‖z‖ = r) : ‖f z‖ = r ^ m * ‖g z‖ := by
      calc
        ‖f z‖ = ‖z ^ m * g z‖ := by rw [hfg z]
        _ = ‖z ^ m‖ * ‖g z‖ := norm_mul _ _
        _ = ‖z‖ ^ m * ‖g z‖ := by rw [norm_pow]
        _ = r ^ m * ‖g z‖ := by rw [hz]
    have hgnorm (z : ℂ) (hz : ‖z‖ = r) : ‖g z‖ = C := by
      have hzval := hnormfactor z hz
      have hrval := hnormfactor (r : ℂ) hrComplex
      have heq : r ^ m * ‖g z‖ = r ^ m * C :=
        hzval.symm.trans ((hmod z hz).trans hrval)
      exact mul_left_cancel₀ hrpowne heq
    let q : ℂ → ℂ := fun z => g z * conj (g (conj (((r : ℂ) ^ 2) / z)))
    have hsharp : Differentiable ℂ (fun z : ℂ => conj (g (conj z))) := by
      intro z
      have hz : DifferentiableAt ℂ g (conj z) := hg (conj z)
      simpa [Function.comp_def] using hz.conj_conj
    have hdiv : DifferentiableOn ℂ (fun z : ℂ => (r : ℂ) ^ 2 / z)
        ({(0 : ℂ)}ᶜ) := by
      intro z hz
      have hz0 : z ≠ 0 := by simpa using hz
      have hnum : DifferentiableAt ℂ (fun _ : ℂ => (r : ℂ) ^ 2) z := by fun_prop
      have hden : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
      exact (hnum.div hden hz0).differentiableWithinAt
    have hqDiff : DifferentiableOn ℂ q ({(0 : ℂ)}ᶜ) := by
      dsimp [q]
      exact hg.differentiableOn.mul
        (hsharp.differentiableOn.comp hdiv (Set.mapsTo_univ _ _))
    have hqAnalytic : AnalyticOnNhd ℂ q ({(0 : ℂ)}ᶜ) :=
      hqDiff.analyticOnNhd isOpen_compl_singleton
    have hcomplPre : IsPreconnected ({(0 : ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank hrank (0 : ℂ)).isPreconnected
    let c : ℂ := (C ^ 2 : ℂ)
    have hqcircle (z : ℂ) (hz : ‖z‖ = r) : q z = c := by
      have hzne : z ≠ 0 := by
        intro h
        subst z
        simp at hz
        linarith
      have hmul : z * conj z = (r : ℂ) ^ 2 := by
        rw [Complex.mul_conj', hz]
      have hinv : (r : ℂ) ^ 2 / z = conj z := by
        rw [← hmul]
        field_simp [hzne]
      dsimp [q, c]
      rw [hinv]
      simp only [Complex.conj_conj]
      rw [Complex.mul_conj', hgnorm z hz]
    have hcne : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast (pow_ne_zero 2 hCpos.ne')
    have hfreq : ∃ᶠ z in 𝓝[≠] z₀, q z = c := by
      apply (accPt_iff_frequently_nhdsNE.mp hacc).mono
      intro z hz
      have hznorm : ‖z‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      exact hqcircle z hznorm
    have hqeq := hqAnalytic.eqOn_of_preconnected_of_frequently_eq
      analyticOnNhd_const hcomplPre (by simpa using hz₀ne) hfreq
    have hgNonzero : ∀ z, g z ≠ 0 := by
      intro z
      by_cases hz : z = 0
      · simpa [hz] using hg0
      · have hqz := hqeq (by simpa using hz)
        dsimp [q] at hqz
        intro hzero
        rw [hzero, zero_mul] at hqz
        exact hcne hqz.symm
    have hfront (z : ℂ) (hz : z ∈ frontier (Metric.ball 0 r)) : ‖g z‖ ≤ C := by
      rw [frontier_ball 0 hr.ne'] at hz
      have hz' : ‖z‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      exact (hgnorm z hz').le
    have hupper (z : ℂ) (hz : z ∈ Metric.ball 0 r) : ‖g z‖ ≤ C :=
      Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        hg.diffContOnCl hfront (subset_closure hz)
    have hinvDiff : Differentiable ℂ (fun z : ℂ => (g z)⁻¹) := hg.inv hgNonzero
    have hinvFront (z : ℂ) (hz : z ∈ frontier (Metric.ball 0 r)) :
        ‖(g z)⁻¹‖ ≤ C⁻¹ := by
      rw [frontier_ball 0 hr.ne'] at hz
      have hz' : ‖z‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      rw [norm_inv, hgnorm z hz']
    have hinvUpper (z : ℂ) (hz : z ∈ Metric.ball 0 r) : ‖(g z)⁻¹‖ ≤ C⁻¹ :=
      Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        hinvDiff.diffContOnCl hinvFront (subset_closure hz)
    have hcenterUpper : ‖g 0‖ ≤ C := hupper 0 (by simpa [Metric.mem_ball] using hr)
    have hcenterInv : ‖(g 0)⁻¹‖ ≤ C⁻¹ := hinvUpper 0 (by simpa [Metric.mem_ball] using hr)
    have hcenterPos : 0 < ‖g 0‖ := norm_pos_iff.mpr (hgNonzero 0)
    have hcenterLower : C ≤ ‖g 0‖ := by
      rw [norm_inv] at hcenterInv
      exact (inv_le_inv₀ hcenterPos hCpos).mp hcenterInv
    have hcenter : ‖g 0‖ = C := le_antisymm hcenterUpper hcenterLower
    have hmax : IsMaxOn (norm ∘ g) (Metric.ball 0 r) 0 := by
      intro z hz
      change ‖g z‖ ≤ ‖g 0‖
      exact (hupper z hz).trans_eq hcenter.symm
    have hgBall : ∀ z ∈ Metric.ball 0 r, g z = g 0 :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 r).isPreconnected
        Metric.isOpen_ball hg.differentiableOn (by simpa [Metric.mem_ball] using hr) hmax
    have hgA : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
    have hballN : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Metric.ball 0 r :=
      Metric.ball_mem_nhds (0 : ℂ) hr
    have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball 0 r :=
      hballN.filter_mono nhdsWithin_le_nhds
    have hfreqG : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = g 0 :=
      hball.frequently.mono fun z hz => hgBall z hz
    have hallG := hgA.eqOn_of_preconnected_of_frequently_eq
      analyticOnNhd_const isPreconnected_univ (Set.mem_univ (0 : ℂ)) hfreqG
    refine ⟨g 0, m, ?_⟩
    funext z
    rw [hfg z, hallG (Set.mem_univ z)]
    ring
  · have hfzero (z : ℂ) : f z = 0 := by
      by_contra hz
      exact hfnz ⟨z, hz⟩
    refine ⟨0, 0, ?_⟩
    funext w
    simp [hfzero w]

/-- A non-monomial entire function has only finitely many maximum points on each
positive circle. -/
theorem maxPoints_finite (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hnm : ¬ IsMonomial f) {r : ℝ} (hr : 0 < r) : (maxPoints f r).Finite := by
  by_contra hnotfinite
  have hinf : (maxPoints f r).Infinite := hnotfinite
  have hsubset : maxPoints f r ⊆ Metric.sphere (0 : ℂ) r := by
    intro z hz
    simpa [Metric.mem_sphere, dist_eq_norm] using hz.1
  obtain ⟨z₀, hz₀, hacc⟩ := hinf.exists_accPt_of_subset_isCompact
    (isCompact_sphere (0 : ℂ) r) hsubset
  have hz₀norm : ‖z₀‖ = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz₀
  have hz₀ne : z₀ ≠ 0 := by
    intro hz
    subst z₀
    have hr0 : r = 0 := by simpa using hz₀norm.symm
    linarith
  obtain ⟨zM, hzM⟩ := exists_maximum_on_circle f hf hr
  have hmaxvalue (z : ℂ) (hz : z ∈ maxPoints f r) :
      ‖f z‖ = ‖f zM‖ := by
    apply le_antisymm
    · exact hzM.2 z hz.1
    · exact hz.2 zM hzM.1
  let q : ℂ → ℂ := fun z => f z * conj (f (conj (((r : ℂ) ^ 2) / z)))
  have hsharp : Differentiable ℂ (fun z : ℂ => conj (f (conj z))) := by
    intro z
    have hz : DifferentiableAt ℂ f (conj z) := hf (conj z)
    simpa [Function.comp_def] using hz.conj_conj
  have hdiv : DifferentiableOn ℂ (fun z : ℂ => (r : ℂ) ^ 2 / z)
      ({(0 : ℂ)}ᶜ) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hnum : DifferentiableAt ℂ (fun _ : ℂ => (r : ℂ) ^ 2) z := by fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    exact (hnum.div hden hz0).differentiableWithinAt
  have hqDiff : DifferentiableOn ℂ q ({(0 : ℂ)}ᶜ) := by
    dsimp [q]
    exact hf.differentiableOn.mul
      (hsharp.differentiableOn.comp hdiv (Set.mapsTo_univ _ _))
  have hqAnalytic : AnalyticOnNhd ℂ q ({(0 : ℂ)}ᶜ) :=
    hqDiff.analyticOnNhd isOpen_compl_singleton
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hcomplPre : IsPreconnected ({(0 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank hrank (0 : ℂ)).isPreconnected
  let C : ℝ := ‖f zM‖
  let c : ℂ := (C ^ 2 : ℂ)
  have hqcircle (z : ℂ) (hz : ‖z‖ = r) :
      q z = ((‖f z‖ ^ 2 : ℝ) : ℂ) := by
    have hzne : z ≠ 0 := by
      intro h
      subst z
      simp at hz
      linarith
    have hmul : z * conj z = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj', hz]
    have hinv : (r : ℂ) ^ 2 / z = conj z := by
      rw [← hmul]
      field_simp [hzne]
    dsimp [q]
    rw [hinv]
    simp only [Complex.conj_conj]
    rw [Complex.mul_conj']
    simp [Complex.normSq_eq_norm_sq]
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, q z = c := by
    apply (accPt_iff_frequently_nhdsNE.mp hacc).mono
    intro z hz
    have hzmax : z ∈ maxPoints f r := hz
    have hznorm : ‖z‖ = r := hzmax.1
    have hqz := hqcircle z hznorm
    have hvalue := hmaxvalue z hzmax
    calc
      q z = ((‖f z‖ ^ 2 : ℝ) : ℂ) := hqz
      _ = ((‖f zM‖ ^ 2 : ℝ) : ℂ) := by rw [hvalue]
      _ = c := by simp [c, C]
  have hqeq := hqAnalytic.eqOn_of_preconnected_of_frequently_eq
    analyticOnNhd_const hcomplPre (by simpa using hz₀ne) hfreq
  have hmod : ∀ z, ‖z‖ = r → ‖f z‖ = ‖f (r : ℂ)‖ := by
    intro z hz
    have hqz := hqcircle z hz
    have hz0 : z ≠ 0 := by
      intro h
      have hz0 : z = 0 := by simpa using h
      subst z
      simp at hz
      linarith
    have hqconst := hqeq (x := z) (by simpa using hz0)
    have hsquare : ‖f z‖ ^ 2 = ‖f zM‖ ^ 2 := by
      have hcast : ((‖f z‖ ^ 2 : ℝ) : ℂ) = ((‖f zM‖ ^ 2 : ℝ) : ℂ) := by
        calc
          ((‖f z‖ ^ 2 : ℝ) : ℂ) = q z := hqz.symm
          _ = c := hqconst
          _ = ((‖f zM‖ ^ 2 : ℝ) : ℂ) := by simp [c, C]
      exact_mod_cast hcast
    have hrComplex : ‖(r : ℂ)‖ = r := by
      simp [Real.norm_eq_abs, abs_of_pos hr]
    have hqr := hqcircle (r : ℂ) hrComplex
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hqcr := hqeq (x := (r : ℂ)) (by simpa using hrne)
    have hsquareR : ‖f (r : ℂ)‖ ^ 2 = ‖f zM‖ ^ 2 := by
      have hcast : ((‖f (r : ℂ)‖ ^ 2 : ℝ) : ℂ) = ((‖f zM‖ ^ 2 : ℝ) : ℂ) := by
        calc
          ((‖f (r : ℂ)‖ ^ 2 : ℝ) : ℂ) = q (r : ℂ) := hqr.symm
          _ = c := hqcr
          _ = ((‖f zM‖ ^ 2 : ℝ) : ℂ) := by simp [c, C]
      exact_mod_cast hcast
    nlinarith [norm_nonneg (f z), norm_nonneg (f (r : ℂ)), norm_nonneg (f zM)]
  exact hnm (constant_modulus_on_circle_is_monomial f hf hr hmod)

end MaxModulusPoints.Liminf
