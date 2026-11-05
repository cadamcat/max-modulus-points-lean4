module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.DiscreteSubset
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.Liminf.Basic
public import MaxModulusPoints.Liminf.Products
public import MaxModulusPoints.Liminf.Radial

/-!
# `MaxModulusPoints.Liminf.Packages`
-/

@[expose] public section

open Filter
open Set
open scoped ComplexConjugate Topology

namespace MaxModulusPoints.Blueprint.Packages

private lemma norm_factor_on_circle {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r : ℝ} (z : ℂ) (hz : ‖z‖ = r) :
    ‖f z‖ = r ^ d.multiplicity * ‖d.g z‖ := by
  rw [d.factorization z, norm_mul, norm_pow, hz]

private lemma radial_ratio_realpart_identity {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hgz : d.g z ≠ 0) :
    (star (d.g z) * (deriv d.g z * (z / (r : ℂ)))).re =
      Complex.normSq (d.g z) * ((z * deriv d.g z / d.g z).re / r) := by
  let A : ℂ := z * deriv d.g z / d.g z
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcomplex :
      star (d.g z) * (deriv d.g z * (z / (r : ℂ))) =
        (Complex.normSq (d.g z) : ℂ) * (A / (r : ℂ)) := by
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp [A]
    field_simp [hgz, hrC]
  have hdiv : (A / (r : ℂ)).re = A.re / r := by
    rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
    field_simp [hr.ne']
    ring
  calc
    _ = ((Complex.normSq (d.g z) : ℂ) * (A / (r : ℂ))).re := congrArg Complex.re hcomplex
    _ = Complex.normSq (d.g z) * (A.re / r) := by simp [Complex.mul_re, hdiv]

private noncomputable def angularSupportValue {f : ℂ → ℂ} (d : NormalizedFunction f) (z : ℂ)
    (t : ℝ) : ℝ := Complex.normSq (d.g (z * Complex.exp ((t : ℂ) * Complex.I)))

private lemma angular_logarithmic_value_real {f : ℂ → ℂ} (d : NormalizedFunction f)
    (z : ℂ) (hz : ‖z‖ ≠ 0) (hmax : ∀ w, ‖w‖ = ‖z‖ → ‖d.g w‖ ≤ ‖d.g z‖)
    (hgz : d.g z ≠ 0) :
    (z * deriv d.g z / d.g z).im = 0 := by
  let A : ℂ := z * deriv d.g z / d.g z
  have hnorm (t : ℝ) : ‖z * Complex.exp ((t : ℂ) * Complex.I)‖ = ‖z‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hle (t : ℝ) : angularSupportValue d z t ≤ angularSupportValue d z 0 := by
    have hval : ‖d.g (z * Complex.exp ((t : ℂ) * Complex.I))‖ ≤ ‖d.g z‖ :=
      hmax _ (hnorm t)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hval
    change Complex.normSq (d.g (z * Complex.exp ((t : ℂ) * Complex.I))) ≤
      Complex.normSq (d.g (z * Complex.exp ((0 : ℂ) * Complex.I)))
    rw [zero_mul, Complex.exp_zero, mul_one]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact hsq
  have hlocal : IsLocalMax (angularSupportValue d z) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0, angularSupportValue d z t ≤ angularSupportValue d z 0
    exact Filter.Eventually.of_forall hle
  have hangle : HasDerivAt (angularSupportValue d z)
      (2 * (star (d.g z) * (deriv d.g z * (z * Complex.I))).re) 0 := by
    change HasDerivAt
      (fun t : ℝ => Complex.normSq (d.g (z * Complex.exp ((t : ℂ) * Complex.I))))
      (2 * (star (d.g z) * (deriv d.g z * (z * Complex.I))).re) 0
    exact MaxModulusPoints.Liminf.angularSupport_hasDerivAt d z
  have hderiv := hlocal.hasDerivAt_eq_zero hangle
  have hcomplex :
      star (d.g z) * (deriv d.g z * (z * Complex.I)) =
        (Complex.normSq (d.g z) : ℂ) * (A * Complex.I) := by
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp [A]
    field_simp [hgz]
  have hreal :
      (star (d.g z) * (deriv d.g z * (z * Complex.I))).re =
        -Complex.normSq (d.g z) * A.im := by
    calc
      _ = ((Complex.normSq (d.g z) : ℂ) * (A * Complex.I)).re := congrArg Complex.re hcomplex
      _ = -Complex.normSq (d.g z) * A.im := by simp [Complex.mul_re]
  rw [hreal] at hderiv
  have hpos : 0 < Complex.normSq (d.g z) := Complex.normSq_pos.mpr hgz
  have hzero : A.im = 0 := by nlinarith
  simpa [A] using hzero

private lemma zeroSet_isDiscrete_of_entire_nonzero {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hn : ¬ ∀ z, h z = 0) : IsDiscrete {z | h z = 0} := by
  let S : Set ℂ := {z | h z = 0}
  have hdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro z hz
    have hnot : ¬∀ᶠ w : ℂ in 𝓝 z, h w = 0 := by
      intro he
      have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] z, h w = 0 :=
        (he.filter_mono nhdsWithin_le_nhds).frequently
      have hA : AnalyticOnNhd ℂ h Set.univ := hh.differentiableOn.analyticOnNhd isOpen_univ
      have hall := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero
        isPreconnected_univ (Set.mem_univ z) hfreq
      exact hn (fun w => hall (Set.mem_univ w))
    have hne : ∀ᶠ w : ℂ in 𝓝[≠] z, h w ≠ 0 :=
      (hh.analyticAt z).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
    have hev : ∀ᶠ w : ℂ in 𝓝 z, w ≠ z → h w ≠ 0 :=
      eventually_nhdsWithin_iff.mp hne
    obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hev
    refine ⟨U, hUopen, ?_⟩
    ext w
    constructor
    · rintro ⟨hwU, hwS⟩
      have hwz : w = z := by
        by_contra hwz
        exact (hUsub hwU hwz) hwS
      simpa [hwz, S] using hz
    · intro hw
      have hwz : w = z := by simpa using hw
      subst w
      exact ⟨hzU, hz⟩
  simpa [S] using hdiscrete

private lemma isDiscrete_inter_left {S T : Set ℂ} (hS : IsDiscrete S) : IsDiscrete (S ∩ T) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen] at hS ⊢
  intro z hz
  obtain ⟨U, hUopen, hUeq⟩ := hS z hz.1
  refine ⟨U, hUopen, ?_⟩
  ext w
  constructor
  · rintro ⟨hwU, hwST⟩
    have hmem : w ∈ U ∩ S := ⟨hwU, hwST.1⟩
    rw [hUeq] at hmem
    have : w = z := by simpa using hmem
    simpa [this]
  · intro hw
    have hwz : w = z := by simpa using hw
    subst w
    have hzU : z ∈ U := by
      have : z ∈ ({z} : Set ℂ) := by simp
      rw [← hUeq] at this
      exact this.1
    exact ⟨hzU, hz⟩

private lemma countable_zeros_of_entire_nonzero {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hn : ¬ ∀ z, h z = 0) : {z | h z = 0}.Countable := by
  let S : Set ℂ := {z | h z = 0}
  have hdiscrete : IsDiscrete S := by
    simpa [S] using zeroSet_isDiscrete_of_entire_nonzero hh hn
  have hL : IsLindelof S := isLindelof_iff_lindelofSpace.mpr inferInstance
  simpa [S] using hL.countable_of_isDiscrete hdiscrete

private noncomputable def isolatedZerosIn (U : Set ℂ) (h : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ U ∧ h z = 0 ∧ ¬ ∀ᶠ w : ℂ in 𝓝 z, h w = 0}

private lemma isolatedZerosIn_countable (U : Set ℂ) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h U) : (isolatedZerosIn U h).Countable := by
  let S := isolatedZerosIn U h
  have hdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro z hz
    rcases hz with ⟨hzU, hzero, hnot⟩
    have hne : ∀ᶠ w : ℂ in 𝓝[≠] z, h w ≠ 0 :=
      (hh z hzU).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
    have hev : ∀ᶠ w : ℂ in 𝓝 z, w ≠ z → h w ≠ 0 :=
      eventually_nhdsWithin_iff.mp hne
    obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hev
    refine ⟨V, hVopen, ?_⟩
    ext w
    constructor
    · rintro ⟨hwV, hwS⟩
      have hwz : w = z := by
        by_contra hwz
        exact (hVsub hwV hwz) hwS.2.1
      simpa [hwz]
    · intro hw
      have hwz : w = z := by simpa using hw
      subst w
      exact ⟨hzV, ⟨hzU, hzero, hnot⟩⟩
  have hL : IsLindelof S := isLindelof_iff_lindelofSpace.mpr inferInstance
  simpa [S] using hL.countable_of_isDiscrete hdiscrete

private noncomputable def finiteLogDerivative {f : ℂ → ℂ}
    (d : NormalizedFunction f) (z : ℂ) : ℂ :=
  (d.multiplicity : ℂ) + z * deriv d.g z / d.g z

private noncomputable def finiteLogDerivativeNumerator {f : ℂ → ℂ}
    (d : NormalizedFunction f) (z : ℂ) : ℂ :=
  d.g z * deriv d.g z + z * d.g z * deriv (deriv d.g) z - z * (deriv d.g z) ^ 2

private lemma finiteLogDerivative_differentiableAt {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hgz : d.g z ≠ 0) :
    DifferentiableAt ℂ (finiteLogDerivative d) z := by
  have hdg : Differentiable ℂ (deriv d.g) := d.entire.deriv
  change DifferentiableAt ℂ
    (fun w : ℂ => (d.multiplicity : ℂ) + (w * deriv d.g w) / d.g w) z
  have hconst : DifferentiableAt ℂ (fun _ : ℂ => (d.multiplicity : ℂ)) z :=
    differentiableAt_const _
  have hmul : DifferentiableAt ℂ (fun w : ℂ => w * deriv d.g w) z :=
    differentiableAt_id.mul (hdg z)
  exact hconst.add (hmul.div (d.entire z) hgz)

private lemma finiteLogDerivative_analyticAt {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hgz : d.g z ≠ 0) :
    AnalyticAt ℂ (finiteLogDerivative d) z := by
  have hderiv : AnalyticAt ℂ (deriv d.g) z := d.entire.deriv.analyticAt z
  have hquot : AnalyticAt ℂ (fun w : ℂ => w * deriv d.g w / d.g w) z :=
    (analyticAt_id.mul hderiv).div (d.entire.analyticAt z) hgz
  change AnalyticAt ℂ (fun w : ℂ => (d.multiplicity : ℂ) +
    w * deriv d.g w / d.g w) z
  exact analyticAt_const.add hquot

private lemma finiteLogDerivative_tendsto_cobounded_of_zero {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hz : z ≠ 0) (hgz : d.g z = 0) :
    Tendsto (finiteLogDerivative d) (𝓝[≠] z) (Bornology.cobounded ℂ) := by
  have hgAt : AnalyticAt ℂ d.g z := d.entire.analyticAt z
  have hnotEventual : ¬∀ᶠ w : ℂ in 𝓝 z, d.g w = 0 := by
    intro he
    have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] z, d.g w = 0 :=
      (he.filter_mono nhdsWithin_le_nhds).frequently
    have hgAnalytic : AnalyticOnNhd ℂ d.g Set.univ :=
      d.entire.differentiableOn.analyticOnNhd isOpen_univ
    have hall := hgAnalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ z) hfreq
    exact d.at_zero (hall (Set.mem_univ (0 : ℂ)))
  have horderNZ : analyticOrderAt d.g z ≠ 0 :=
    hgAt.analyticOrderAt_ne_zero.mpr hgz
  have horderTop : analyticOrderAt d.g z ≠ ⊤ := by
    intro h
    exact hnotEventual (analyticOrderAt_eq_top.mp h)
  lift analyticOrderAt d.g z to ℕ using horderTop with n hn
  have hnz : n ≠ 0 := by exact_mod_cast horderNZ
  have horderMer : meromorphicOrderAt d.g z = (n : ℤ) := by
    rw [hgAt.meromorphicOrderAt_eq, ← hn]
    simp
  have horderMerNZ : meromorphicOrderAt d.g z ≠ 0 := by
    rw [horderMer]
    exact_mod_cast hnz
  have horderMerTop : meromorphicOrderAt d.g z ≠ ⊤ := by
    rw [horderMer]
    simp
  have hlogOrder : meromorphicOrderAt (logDeriv d.g) z = -1 :=
    meromorphicOrderAt_logDeriv_eq_neg_one hgAt.meromorphicAt horderMerNZ horderMerTop
  have hproductOrder :
      meromorphicOrderAt (fun w : ℂ => w * logDeriv d.g w) z = -1 := by
    calc
      _ = meromorphicOrderAt ((fun w : ℂ => w) * logDeriv d.g) z := rfl
      _ = meromorphicOrderAt (logDeriv d.g) z :=
        meromorphicOrderAt_mul_of_ne_zero analyticAt_id hz
      _ = -1 := hlogOrder
  have hconstantMer : MeromorphicAt (fun _ : ℂ => (d.multiplicity : ℂ)) z :=
    analyticAt_const.meromorphicAt
  have horderLt : meromorphicOrderAt (fun w : ℂ => w * logDeriv d.g w) z <
      meromorphicOrderAt (fun _ : ℂ => (d.multiplicity : ℂ)) z := by
    by_cases hm : (d.multiplicity : ℂ) = 0
    · have hconstTop : meromorphicOrderAt (fun _ : ℂ => (0 : ℂ)) z = ⊤ := by
        rw [meromorphicOrderAt_eq_top_iff]
        exact Filter.Eventually.of_forall (fun _ => rfl)
      rw [hproductOrder, hm, hconstTop]
      exact WithTop.coe_lt_top (-1 : ℤ)
    · have hconstOrd : meromorphicOrderAt (fun _ : ℂ => (d.multiplicity : ℂ)) z = 0 := by
        have hconstAnalytic : AnalyticAt ℂ (fun _ : ℂ => (d.multiplicity : ℂ)) z :=
          analyticAt_const
        rw [hconstAnalytic.meromorphicOrderAt_eq,
          hconstAnalytic.analyticOrderAt_eq_zero.mpr hm]
        rfl
      rw [hproductOrder, hconstOrd]
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0)
  have hAeq : finiteLogDerivative d =
      (fun w : ℂ => (d.multiplicity : ℂ) + w * logDeriv d.g w) := by
    funext w
    simp [finiteLogDerivative, logDeriv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have horderA : meromorphicOrderAt (finiteLogDerivative d) z = -1 := by
    rw [hAeq]
    change meromorphicOrderAt
      ((fun _ : ℂ => (d.multiplicity : ℂ)) +
        (fun w : ℂ => w * logDeriv d.g w)) z = -1
    rw [meromorphicOrderAt_add_eq_right_of_lt hconstantMer horderLt]
    exact hproductOrder
  exact tendsto_cobounded_of_meromorphicOrderAt_neg (by
    rw [horderA]
    exact WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < 0))

private lemma exists_open_neighborhood_blowup {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hz : z ≠ 0) (hgz : d.g z = 0)
    (C : ℝ) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, w ≠ z → C < ‖finiteLogDerivative d w‖ := by
  have htop := finiteLogDerivative_tendsto_cobounded_of_zero d hz hgz
  have hnorm : Tendsto (fun w : ℂ => ‖finiteLogDerivative d w‖)
      (𝓝[≠] z) atTop := (tendsto_norm_atTop_iff_cobounded).2 htop
  have hev : ∀ᶠ w : ℂ in 𝓝[≠] z, C < ‖finiteLogDerivative d w‖ :=
    hnorm.eventually (Ioi_mem_atTop C)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hev
  exact ⟨U, hUopen, hzU, fun w hw hwne => hUsub hw hwne⟩

private lemma finiteLogDerivative_localInverse_chart {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hgz : d.g z ≠ 0)
    (hderiv : deriv (finiteLogDerivative d) z ≠ 0) :
    ∃ U W : Set ℂ, ∃ ψ : ℂ → ℂ,
      IsOpen U ∧ IsOpen W ∧ z ∈ U ∧ finiteLogDerivative d z ∈ W ∧
      MapsTo (finiteLogDerivative d) U W ∧ MapsTo ψ W U ∧
      (∀ x ∈ U, ψ (finiteLogDerivative d x) = x) ∧
      (∀ y ∈ W, finiteLogDerivative d (ψ y) = y) ∧ DifferentiableOn ℂ ψ W := by
  let hA : AnalyticAt ℂ (finiteLogDerivative d) z := finiteLogDerivative_analyticAt d hgz
  let hstrict := hA.hasStrictDerivAt
  let hstrictF := hstrict.hasStrictFDerivAt_equiv hderiv
  let R := hstrictF.toOpenPartialHomeomorph (finiteLogDerivative d)
  have hderivAnalytic : AnalyticAt ℂ (deriv (finiteLogDerivative d)) z := hA.deriv
  have hderivContinuous : ContinuousAt (deriv (finiteLogDerivative d)) z :=
    hderivAnalytic.continuousAt
  have hnearDeriv : ∀ᶠ w : ℂ in 𝓝 z, deriv (finiteLogDerivative d) w ≠ 0 :=
    hderivContinuous.eventually (isOpen_ne.mem_nhds hderiv)
  have hnearG : ∀ᶠ w : ℂ in 𝓝 z, d.g w ≠ 0 :=
    d.entire.continuous.continuousAt.eventually_ne hgz
  obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp (hnearDeriv.and hnearG)
  let U : Set ℂ := R.source ∩ V
  let W : Set ℂ := R '' U
  let ψ : ℂ → ℂ := R.symm
  have hzSource : z ∈ R.source := hstrictF.mem_toOpenPartialHomeomorph_source
  have hzU : z ∈ U := ⟨hzSource, hzV⟩
  have hUopen : IsOpen U := R.open_source.inter hVopen
  have hWopen : IsOpen W := by
    exact R.isOpen_image_source_inter hVopen
  have hqW : finiteLogDerivative d z ∈ W := by
    exact ⟨z, hzU, rfl⟩
  have hAmap : MapsTo (finiteLogDerivative d) U W := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hWtarget : W ⊆ R.target := by
    rintro y ⟨x, hx, rfl⟩
    exact R.map_source hx.1
  have hmaps : MapsTo ψ W U := by
    intro y hy
    rcases hy with ⟨x, hxU, rfl⟩
    change R.symm (R x) ∈ U
    rw [R.left_inv hxU.1]
    exact hxU
  have hleft (x : ℂ) (hx : x ∈ U) : ψ (finiteLogDerivative d x) = x := by
    change R.symm (R x) = x
    exact R.left_inv hx.1
  have hright (y : ℂ) (hy : y ∈ W) : finiteLogDerivative d (ψ y) = y := by
    have hyTarget : y ∈ R.target := hWtarget hy
    change R (R.symm y) = y
    exact R.right_inv hyTarget
  have hψdiff : DifferentiableOn ℂ ψ W := by
    intro y hy
    have hyTarget : y ∈ R.target := hWtarget hy
    have hxU : ψ y ∈ U := hmaps hy
    have hxV : ψ y ∈ V := hxU.2
    have hlocal := hVsub hxV
    have hgz' : d.g (ψ y) ≠ 0 := hlocal.2
    have hderiv' : deriv (finiteLogDerivative d) (ψ y) ≠ 0 := hlocal.1
    have hA' : AnalyticAt ℂ (finiteLogDerivative d) (ψ y) :=
      finiteLogDerivative_analyticAt d hgz'
    have hstrict' := hA'.hasStrictDerivAt
    have hcont : ContinuousAt ψ y := R.continuousAt_symm hyTarget
    have hcomp : ∀ᶠ y' : ℂ in 𝓝 y, finiteLogDerivative d (ψ y') = y' := by
      have hevent := R.eventually_right_inverse hyTarget
      change ∀ᶠ y' : ℂ in 𝓝 y, finiteLogDerivative d (R.symm y') = y' at hevent
      exact hevent
    have hdiffAt : DifferentiableAt ℂ ψ y :=
      (HasStrictDerivAt.of_local_left_inverse hcont hstrict' hderiv' hcomp).hasDerivAt.differentiableAt
    exact hdiffAt.differentiableWithinAt
  exact ⟨U, W, ψ, hUopen, hWopen, hzU, hqW, hAmap, hmaps, hleft, hright, hψdiff⟩

private lemma finiteLogDerivative_deriv_identity {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hgz : d.g z ≠ 0) :
    (d.g z) ^ 2 * deriv (finiteLogDerivative d) z = finiteLogDerivativeNumerator d z := by
  have hdg : Differentiable ℂ (deriv d.g) := d.entire.deriv
  have hNdiff : DifferentiableAt ℂ (fun w : ℂ => w * deriv d.g w) z :=
    differentiableAt_id.mul (hdg z)
  have hNderiv : deriv (fun w : ℂ => w * deriv d.g w) z =
      deriv d.g z + z * deriv (deriv d.g) z := by
    simpa [Function.id_def] using
      (deriv_fun_mul (c := id) (d := deriv d.g) differentiableAt_id (hdg z))
  have hAderiv : deriv (finiteLogDerivative d) z =
      ((deriv d.g z + z * deriv (deriv d.g) z) * d.g z -
        z * deriv d.g z * deriv d.g z) / (d.g z) ^ 2 := by
    change deriv (fun w : ℂ => (d.multiplicity : ℂ) +
      (w * deriv d.g w) / d.g w) z = _
    rw [deriv_const_add, deriv_fun_div hNdiff (d.entire z) hgz, hNderiv]
  rw [hAderiv]
  dsimp [finiteLogDerivativeNumerator]
  field_simp [hgz]

private lemma finiteLogDerivativeNumerator_not_zero {f : ℂ → ℂ}
    (d : NormalizedFunction f) :
    ¬ ∀ z, finiteLogDerivativeNumerator d z = 0 := by
  intro hnum
  have hnear : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), d.g z ≠ 0 :=
    d.entire.continuous.continuousAt.eventually_ne d.at_zero
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  have hAprime (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) ρ) :
      deriv (finiteLogDerivative d) z = 0 := by
    have hidentity := finiteLogDerivative_deriv_identity d (hball hz)
    rw [hnum z] at hidentity
    have hpow : (d.g z) ^ 2 ≠ 0 := pow_ne_zero 2 (hball hz)
    exact (mul_eq_zero.mp hidentity).resolve_left hpow
  have hAon : DifferentiableOn ℂ (finiteLogDerivative d) (Metric.ball (0 : ℂ) ρ) := by
    intro z hz
    exact (finiteLogDerivative_differentiableAt d (hball hz)).differentiableWithinAt
  have hA0 : finiteLogDerivative d 0 = (d.multiplicity : ℂ) := by
    simp [finiteLogDerivative]
  have hAconstant (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) ρ) :
      finiteLogDerivative d z = (d.multiplicity : ℂ) := by
    have hEq := IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball
      (convex_ball (0 : ℂ) ρ).isPreconnected hAon hAprime
      (Metric.mem_ball_self hρ) hz
    rw [hA0] at hEq
    exact hEq.symm
  have hderivZero (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) ρ) (hzne : z ≠ 0) :
      deriv d.g z = 0 := by
    have hA := hAconstant z hz
    rw [finiteLogDerivative] at hA
    have hratio : z * deriv d.g z / d.g z = 0 := by
      have hA' : (d.multiplicity : ℂ) + z * deriv d.g z / d.g z =
          (d.multiplicity : ℂ) + 0 := by simpa using hA
      exact add_left_cancel hA'
    have hmult : z * deriv d.g z = 0 := by
      have hzero := (div_eq_zero_iff).mp hratio
      exact hzero.resolve_right (hball hz)
    exact (mul_eq_zero.mp hmult).resolve_left hzne
  have hderivEventual : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), deriv d.g z = 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with z hz hzne
    exact hderivZero z hz hzne
  have hderivFreq : ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), deriv d.g z = 0 :=
    hderivEventual.frequently
  have hanalytic : AnalyticOnNhd ℂ (deriv d.g) Set.univ :=
    d.entire.deriv.differentiableOn.analyticOnNhd isOpen_univ
  have hderivAll := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ (0 : ℂ)) hderivFreq
  have hconst : ∀ z, d.g z = d.g 0 := by
    intro z
    exact is_const_of_deriv_eq_zero d.entire (fun w => hderivAll (Set.mem_univ w)) z 0
  exact d.nonconstant ⟨d.g 0, fun z => hconst z⟩

private lemma finiteLogDerivativeNumerator_differentiable {f : ℂ → ℂ}
    (d : NormalizedFunction f) :
    Differentiable ℂ (finiteLogDerivativeNumerator d) := by
  have hdg : Differentiable ℂ (deriv d.g) := d.entire.deriv
  have hddg : Differentiable ℂ (deriv (deriv d.g)) := hdg.deriv
  change Differentiable ℂ
    (fun z : ℂ => d.g z * deriv d.g z + z * d.g z * deriv (deriv d.g) z -
      z * (deriv d.g z) ^ 2)
  have hfirst : Differentiable ℂ (fun z : ℂ => d.g z * deriv d.g z) := d.entire.mul hdg
  have hsecond : Differentiable ℂ
      (fun z : ℂ => z * d.g z * deriv (deriv d.g) z) :=
    (differentiable_id.mul d.entire).mul hddg
  have hthird : Differentiable ℂ (fun z : ℂ => z * (deriv d.g z) ^ 2) :=
    differentiable_id.mul (hdg.pow 2)
  exact (hfirst.add hsecond).sub hthird

private noncomputable def finiteCriticalValues {f : ℂ → ℂ}
    (d : NormalizedFunction f) : Set ℂ :=
  finiteLogDerivative d '' {z | finiteLogDerivativeNumerator d z = 0}

private lemma finiteCriticalValues_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) : (finiteCriticalValues d).Countable := by
  have hzeros := countable_zeros_of_entire_nonzero
    (finiteLogDerivativeNumerator_differentiable d) (finiteLogDerivativeNumerator_not_zero d)
  simpa [finiteCriticalValues] using hzeros.image (finiteLogDerivative d)

private lemma finiteLogDerivative_deriv_ne_zero_of_not_critical {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hgz : d.g z ≠ 0)
    (hq : finiteLogDerivative d z ∉ finiteCriticalValues d) :
    deriv (finiteLogDerivative d) z ≠ 0 := by
  intro hderiv
  have hnum : finiteLogDerivativeNumerator d z = 0 := by
    have h := finiteLogDerivative_deriv_identity d hgz
    rw [hderiv, mul_zero] at h
    exact h.symm
  apply hq
  exact ⟨z, hnum, rfl⟩

private def reflectedNormalized {f : ℂ → ℂ} (d : NormalizedFunction f) :
    NormalizedFunction (fun z : ℂ => z ^ d.multiplicity * reflected d.g z) := by
  have hreflect : Differentiable ℂ (reflected d.g) := by
    change Differentiable ℂ (fun z : ℂ => conj (d.g (conj z)))
    intro z
    have hz : DifferentiableAt ℂ d.g (conj z) := d.entire (conj z)
    simpa [Function.comp_def] using hz.conj_conj
  have hreflectZero : reflected d.g 0 ≠ 0 := by
    simpa [reflected] using star_ne_zero.mpr d.at_zero
  have hreflectNonconstant : ¬∃ c : ℂ, ∀ z, reflected d.g z = c := by
    rintro ⟨c, hc⟩
    apply d.nonconstant
    refine ⟨star c, ?_⟩
    intro z
    simpa [reflected] using congrArg star (hc (star z))
  exact
    { multiplicity := d.multiplicity
      g := reflected d.g
      entire := hreflect
      at_zero := hreflectZero
      nonconstant := hreflectNonconstant
      factorization := fun _ => rfl }

private noncomputable def commonFiniteCriticalValues {f : ℂ → ℂ}
    (d : NormalizedFunction f) : Set ℂ :=
  finiteCriticalValues d ∪ finiteCriticalValues (reflectedNormalized d)

private lemma commonFiniteCriticalValues_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) : (commonFiniteCriticalValues d).Countable := by
  exact (finiteCriticalValues_countable d).union
    (finiteCriticalValues_countable (reflectedNormalized d))

private lemma finiteLogDerivative_deriv_ne_zero_of_not_common_critical
    {f : ℂ → ℂ} (d : NormalizedFunction f) {z : ℂ} (hgz : d.g z ≠ 0)
    (hnot : finiteLogDerivative d z ∉ commonFiniteCriticalValues d) :
    deriv (finiteLogDerivative d) z ≠ 0 := by
  apply finiteLogDerivative_deriv_ne_zero_of_not_critical d hgz
  intro hmem
  apply hnot
  exact Or.inl hmem

private lemma reflectedLogDerivative_deriv_ne_zero_of_not_common_critical
    {f : ℂ → ℂ} (d : NormalizedFunction f) {z : ℂ}
    (hgz : reflected d.g z ≠ 0)
    (hnot : finiteLogDerivative (reflectedNormalized d) z ∉ commonFiniteCriticalValues d) :
    deriv (finiteLogDerivative (reflectedNormalized d)) z ≠ 0 := by
  apply finiteLogDerivative_deriv_ne_zero_of_not_critical (reflectedNormalized d) hgz
  intro hmem
  apply hnot
  exact Or.inr hmem

private lemma logarithmicValue_eq_coe_finiteLogDerivative {f : ℂ → ℂ}
    (d : NormalizedFunction f) {z : ℂ} (hgz : d.g z ≠ 0) :
    logarithmicValue d.multiplicity d.g z = (finiteLogDerivative d z : OnePoint ℂ) := by
  simp [logarithmicValue, finiteLogDerivative, hgz]

private noncomputable def finiteLogDerivativeLevelNumerator {f : ℂ → ℂ}
    (d : NormalizedFunction f) (q z : ℂ) : ℂ :=
  z * deriv d.g z + ((d.multiplicity : ℂ) - q) * d.g z

private noncomputable def finiteLogDerivativeLevelSet {f : ℂ → ℂ}
    (d : NormalizedFunction f) (q : ℂ) : Set ℂ :=
  {z | finiteLogDerivative d z = q ∧ d.g z ≠ 0}

private lemma finiteLogDerivativeLevelNumerator_differentiable {f : ℂ → ℂ}
    (d : NormalizedFunction f) (q : ℂ) :
    Differentiable ℂ (finiteLogDerivativeLevelNumerator d q) := by
  have hfirst : Differentiable ℂ (fun z : ℂ => z * deriv d.g z) :=
    differentiable_id.mul d.entire.deriv
  have hsecond : Differentiable ℂ
      (fun z : ℂ => ((d.multiplicity : ℂ) - q) * d.g z) :=
    (differentiable_const _).mul d.entire
  exact hfirst.add hsecond

private lemma finiteLogDerivativeLevelNumerator_not_zero {f : ℂ → ℂ}
    (d : NormalizedFunction f) {q : ℂ} (hq : q ≠ (d.multiplicity : ℂ)) :
    ¬ ∀ z, finiteLogDerivativeLevelNumerator d q z = 0 := by
  intro h
  have hzero : ((d.multiplicity : ℂ) - q) * d.g 0 = 0 := by
    simpa [finiteLogDerivativeLevelNumerator] using h 0
  rcases mul_eq_zero.mp hzero with hmq | hg0
  · exact hq ((sub_eq_zero.mp hmq).symm)
  · exact d.at_zero hg0

private lemma finiteLogDerivativeLevelSet_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) {q : ℂ} (hq : q ≠ (d.multiplicity : ℂ)) :
    (finiteLogDerivativeLevelSet d q).Countable := by
  have hzeros := countable_zeros_of_entire_nonzero
    (finiteLogDerivativeLevelNumerator_differentiable d q)
    (finiteLogDerivativeLevelNumerator_not_zero d hq)
  apply hzeros.mono
  intro z hz
  rcases hz with ⟨hval, hgz⟩
  have hratio : z * deriv d.g z / d.g z = q - (d.multiplicity : ℂ) := by
    dsimp [finiteLogDerivative] at hval
    linear_combination hval
  have hmul := (div_eq_iff hgz).mp hratio
  dsimp [finiteLogDerivativeLevelNumerator]
  rw [hmul]
  ring

private lemma logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet
    {f : ℂ → ℂ} (d : NormalizedFunction f) {q z : ℂ} :
    logarithmicValue d.multiplicity d.g z = (q : OnePoint ℂ) ↔
      z ∈ finiteLogDerivativeLevelSet d q := by
  constructor
  · intro h
    have hgz : d.g z ≠ 0 := by
      intro hzero
      have hbad : OnePoint.infty = (q : OnePoint ℂ) := by
        simpa [logarithmicValue, hzero] using h
      exact (OnePoint.infty_ne_coe q) hbad
    change finiteLogDerivative d z = q ∧ d.g z ≠ 0
    refine ⟨?_, hgz⟩
    have hfinite := logarithmicValue_eq_coe_finiteLogDerivative d hgz
    have heq : (finiteLogDerivative d z : OnePoint ℂ) = (q : OnePoint ℂ) := by
      rw [← hfinite]
      exact h
    exact OnePoint.coe_eq_coe.mp heq
  · change finiteLogDerivative d z = q ∧ d.g z ≠ 0 → _
    rintro ⟨hval, hgz⟩
    rw [logarithmicValue_eq_coe_finiteLogDerivative d hgz, OnePoint.coe_eq_coe]
    exact hval

private lemma exists_ball_avoiding_level_value {f : ℂ → ℂ}
    (d : NormalizedFunction f) {q : ℂ} (hq : q ≠ (d.multiplicity : ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (0 : ℂ) δ, finiteLogDerivative d z ≠ q := by
  have hA0 : finiteLogDerivative d 0 = (d.multiplicity : ℂ) := by
    simp [finiteLogDerivative]
  have hA0q : finiteLogDerivative d 0 ≠ q := by
    rw [hA0]
    exact hq.symm
  have hnear : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), finiteLogDerivative d z ≠ q :=
    (finiteLogDerivative_analyticAt d d.at_zero).continuousAt.eventually
      (isOpen_ne.mem_nhds hA0q)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  exact ⟨δ, hδ, fun z hz => hball hz⟩

private lemma exists_ball_avoiding_value_window {f : ℂ → ℂ}
    (d : NormalizedFunction f) {q : ℂ} (r : ℝ) (hr : 0 < r)
    (hsep : 2 * r < ‖q - (d.multiplicity : ℂ)‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (0 : ℂ) δ, ∀ q' ∈ Metric.ball q r,
      finiteLogDerivative d z ≠ q' := by
  have hA0 : finiteLogDerivative d 0 = (d.multiplicity : ℂ) := by
    simp [finiteLogDerivative]
  have hballNhds : Metric.ball (d.multiplicity : ℂ) r ∈
      𝓝 (finiteLogDerivative d 0) := by
    rw [hA0]
    exact Metric.ball_mem_nhds _ hr
  have hnear : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      finiteLogDerivative d z ∈ Metric.ball (d.multiplicity : ℂ) r :=
    (finiteLogDerivative_analyticAt d d.at_zero).continuousAt.eventually hballNhds
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  refine ⟨δ, hδ, fun z hz q' hq' heq => ?_⟩
  have hzimage : finiteLogDerivative d z ∈ Metric.ball (d.multiplicity : ℂ) r := hball hz
  have htriangle : dist q (d.multiplicity : ℂ) ≤
      dist q q' + dist q' (d.multiplicity : ℂ) := dist_triangle q q' _
  have hleft : dist q q' < r := by
    simpa [Metric.mem_ball, dist_comm] using hq'
  have hq'image : q' ∈ Metric.ball (d.multiplicity : ℂ) r := by
    simpa [heq] using hzimage
  have hright : dist q' (d.multiplicity : ℂ) < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq'image
  have hdist : dist q (d.multiplicity : ℂ) = ‖q - (d.multiplicity : ℂ)‖ := dist_eq_norm _ _
  rw [hdist] at htriangle
  linarith

private lemma exists_compact_nonvanishing_level_window {f : ℂ → ℂ}
    (d : NormalizedFunction f) {q : ℂ} (r δ : ℝ)
    (havoid : ∀ z ∈ Metric.ball (0 : ℂ) δ, ∀ q' ∈ Metric.ball q r,
      finiteLogDerivative d z ≠ q') (R : ℝ) :
    ∃ X : Set ℂ, IsCompact X ∧ (∀ z ∈ X, d.g z ≠ 0) ∧
      ∀ z q', ‖z‖ ≤ R → d.g z ≠ 0 → q' ∈ Metric.ball q r →
        finiteLogDerivative d z = q' → z ∈ X ∧ δ ≤ ‖z‖ := by
  let Z : Set ℂ := {z | d.g z = 0} ∩ Metric.closedBall (0 : ℂ) R
  have hzeroClosed : IsClosed {z | d.g z = 0} :=
    isClosed_eq d.entire.continuous continuous_const
  have hZcompact : IsCompact Z := by
    exact (isCompact_closedBall (0 : ℂ) R).inter_left hzeroClosed
  have hZdiscrete : IsDiscrete Z :=
    isDiscrete_inter_left (zeroSet_isDiscrete_of_entire_nonzero d.entire
      (fun h => d.at_zero (h 0)))
  have hZfinite : Z.Finite := hZcompact.finite hZdiscrete
  let Qbound : ℝ := ‖q‖ + r
  choose N hNopen hNcenter hNlarge using
    (fun a : {a // a ∈ Z} =>
      exists_open_neighborhood_blowup d (by
        intro ha0
        have hga : d.g a.1 = 0 := a.2.1
        rw [ha0] at hga
        exact d.at_zero hga) a.2.1 Qbound)
  let O : Set ℂ := ⋃ a : {a // a ∈ Z}, N a
  have hOopen : IsOpen O := isOpen_iUnion fun a => hNopen a
  let X : Set ℂ := Metric.closedBall (0 : ℂ) R \ O
  have hXclosed : IsClosed X := by
    change IsClosed (Metric.closedBall (0 : ℂ) R ∩ Oᶜ)
    exact Metric.isClosed_closedBall.inter (isClosed_compl_iff.mpr hOopen)
  have hXcompact : IsCompact X := by
    exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
      hXclosed Set.diff_subset
  have hXnonzero : ∀ z ∈ X, d.g z ≠ 0 := by
    intro z hz hzero
    have hzZ : z ∈ Z := ⟨hzero, hz.1⟩
    have hzO : z ∈ O := by
      exact mem_iUnion.2 ⟨⟨z, hzZ⟩, hNcenter ⟨z, hzZ⟩⟩
    exact hz.2 hzO
  refine ⟨X, hXcompact, hXnonzero, ?_⟩
  intro z q' hnorm hgz hq' hvalue
  have hzball : z ∈ Metric.closedBall (0 : ℂ) R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  have hqbound : ‖q'‖ ≤ Qbound := by
    have hdist : dist q' q < r := by
      simpa [Metric.mem_ball, dist_comm] using hq'
    have htriangle : ‖q'‖ ≤ dist q' q + ‖q‖ := by
      calc
        ‖q'‖ = ‖(q' - q) + q‖ := by congr 1; abel
        _ ≤ ‖q' - q‖ + ‖q‖ := norm_add_le _ _
        _ = dist q' q + ‖q‖ := by rw [dist_eq_norm]
    dsimp [Qbound]
    linarith
  have hzO : z ∉ O := by
    intro hzO
    rcases mem_iUnion.mp hzO with ⟨a, haz⟩
    have ha0 : d.g a.1 = 0 := a.2.1
    have hazne : z ≠ a.1 := by
      intro hza
      subst z
      exact hgz ha0
    have hlarge := hNlarge a z haz hazne
    rw [hvalue] at hlarge
    exact (not_lt_of_ge hqbound) hlarge
  have hzX : z ∈ X := ⟨hzball, hzO⟩
  have hnormlarge : ¬ ‖z‖ < δ := by
    intro hlt
    have hzsmall : z ∈ Metric.ball (0 : ℂ) δ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hlt
    exact (havoid z hzsmall q' hq') hvalue
  exact ⟨hzX, le_of_not_gt hnormlarge⟩

private lemma physicalFiber_locally_in_source {f : ℂ → ℂ}
    (d : NormalizedFunction f) (s q : ℂ) (hs : s ≠ 0)
    (hq : q ≠ (d.multiplicity : ℂ)) (V : Set (ℂ × ℂ)) (hVopen : IsOpen V)
    (hVfiber : physicalFiber d s (q : OnePoint ℂ) ⊆ V) :
    ∃ U W : Set ℂ, IsOpen U ∧ IsOpen W ∧ s ∈ U ∧ q ∈ W ∧
      (∀ s' ∈ U, s' ≠ 0) ∧
      (∀ q' ∈ W, q' ≠ (d.multiplicity : ℂ)) ∧
      ∀ s' ∈ U, ∀ q' ∈ W, physicalFiber d s' (q' : OnePoint ℂ) ⊆ V := by
  let e := reflectedNormalized d
  let A := finiteLogDerivative d
  let B := finiteLogDerivative e
  have hqDiff : q - (d.multiplicity : ℂ) ≠ 0 := sub_ne_zero.mpr hq
  have hqDist : 0 < ‖q - (d.multiplicity : ℂ)‖ := norm_pos_iff.mpr hqDiff
  let r : ℝ := ‖q - (d.multiplicity : ℂ)‖ / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hsep : 2 * r < ‖q - (d.multiplicity : ℂ)‖ := by
    dsimp [r]
    linarith
  let rs : ℝ := ‖s‖ / 2
  have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hrs : 0 < rs := by dsimp [rs]; positivity
  let U₀ : Set ℂ := Metric.ball s rs
  let W₀ : Set ℂ := Metric.ball q r
  have hsU₀ : s ∈ U₀ := Metric.mem_ball_self hrs
  have hqW₀ : q ∈ W₀ := Metric.mem_ball_self hr
  obtain ⟨δA, hδA, havoidA⟩ := exists_ball_avoiding_value_window d r hr hsep
  obtain ⟨δB, hδB, havoidB⟩ := exists_ball_avoiding_value_window e r hr hsep
  let Sbound : ℝ := ‖s‖ + rs
  let Rz : ℝ := Sbound / δB + 1
  let Rw : ℝ := Sbound / δA + 1
  obtain ⟨Xz, hXzcompact, hXznonzero, hXzmem⟩ :=
    exists_compact_nonvanishing_level_window d r δA havoidA Rz
  obtain ⟨Xw, hXwcompact, hXwnonzero, hXwmem⟩ :=
    exists_compact_nonvanishing_level_window e r δB havoidB Rw
  let D : Set (ℂ × ℂ) := Xz ×ˢ Xw
  have hDcompact : IsCompact D := hXzcompact.prod hXwcompact
  have hDclosed : IsClosed D := hDcompact.isClosed
  have hAcontX : ContinuousOn A Xz := by
    intro z hz
    exact (finiteLogDerivative_differentiableAt d (hXznonzero z hz)).continuousAt.continuousWithinAt
  have hBcontX : ContinuousOn B Xw := by
    intro w hw
    exact (finiteLogDerivative_differentiableAt e (hXwnonzero w hw)).continuousAt.continuousWithinAt
  have hAcomp : ContinuousOn (fun v : ℂ × ℂ => A v.1) D := by
    exact hAcontX.comp continuous_fst.continuousOn (fun _ hv => hv.1)
  have hBcomp : ContinuousOn (fun v : ℂ × ℂ => B v.2) D := by
    exact hBcontX.comp continuous_snd.continuousOn (fun _ hv => hv.2)
  let G : ℂ × ℂ → ℂ := fun v => A v.1 - B v.2
  have hGcont : ContinuousOn G D := by
    exact hAcomp.sub hBcomp
  let C : Set (ℂ × ℂ) := D ∩ G ⁻¹' {0}
  have hCclosed : IsClosed C := by
    change IsClosed (D ∩ G ⁻¹' {0})
    exact hGcont.preimage_isClosed_of_isClosed hDclosed isClosed_singleton
  have hCcompact : IsCompact C := hDcompact.of_isClosed_subset hCclosed inter_subset_left
  let Φ : ℂ × ℂ → ℂ × ℂ := fun v => (v.1 * v.2, A v.1)
  have hprodCont : ContinuousOn (fun v : ℂ × ℂ => v.1 * v.2) D := by
    fun_prop
  have hΦcont : ContinuousOn Φ D := by
    exact hprodCont.prodMk hAcomp
  have hwindow : ∀ s' ∈ U₀, ∀ q' ∈ W₀, ∀ v ∈ physicalFiber d s' (q' : OnePoint ℂ),
      v ∈ D ∧ A v.1 = q' ∧ B v.2 = q' := by
    intro s' hs' q' hq' v hv
    rcases v with ⟨z, w⟩
    rcases hv with ⟨hprod, hzval, hwval⟩
    have hzlevel := (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet d).mp hzval
    have hwlevel := (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet e).mp hwval
    rcases hzlevel with ⟨hAz, hgz⟩
    rcases hwlevel with ⟨hBw, hgw⟩
    have hsDist : dist s' s < rs := by simpa [U₀] using hs'
    have hsBound : ‖s'‖ ≤ Sbound := by
      have htriangle : ‖s'‖ ≤ dist s' s + ‖s‖ := by
        calc
          ‖s'‖ = ‖(s' - s) + s‖ := by congr 1; abel
          _ ≤ ‖s' - s‖ + ‖s‖ := norm_add_le _ _
          _ = dist s' s + ‖s‖ := by rw [dist_eq_norm]
      dsimp [Sbound]
      linarith
    have hzLower : δA ≤ ‖z‖ := by
      apply le_of_not_gt
      intro hlt
      have hzball : z ∈ Metric.ball (0 : ℂ) δA := by
        simpa [Metric.mem_ball, dist_eq_norm] using hlt
      exact (havoidA z hzball q' hq') hAz
    have hwLower : δB ≤ ‖w‖ := by
      apply le_of_not_gt
      intro hlt
      have hwball : w ∈ Metric.ball (0 : ℂ) δB := by
        simpa [Metric.mem_ball, dist_eq_norm] using hlt
      exact (havoidB w hwball q' hq') hBw
    have hnormProd : ‖z‖ * ‖w‖ = ‖s'‖ := by rw [← norm_mul, hprod]
    have hzUpper : ‖z‖ ≤ Rz := by
      have hmul : ‖z‖ * δB ≤ ‖s'‖ := by
        calc
          ‖z‖ * δB ≤ ‖z‖ * ‖w‖ := mul_le_mul_of_nonneg_left hwLower (norm_nonneg _)
          _ = ‖s'‖ := hnormProd
      have hdiv := (le_div_iff₀ hδB).2 hmul
      have hdivBound : ‖s'‖ / δB ≤ (‖s‖ + rs) / δB := by
        rw [div_le_div_iff₀ hδB hδB]
        exact mul_le_mul_of_nonneg_right hsBound hδB.le
      calc
        ‖z‖ ≤ ‖s'‖ / δB := hdiv
        _ ≤ (‖s‖ + rs) / δB := hdivBound
        _ ≤ Rz := by dsimp [Rz, Sbound]; linarith
    have hwUpper : ‖w‖ ≤ Rw := by
      have hmul : ‖w‖ * δA ≤ ‖s'‖ := by
        calc
          ‖w‖ * δA ≤ ‖w‖ * ‖z‖ := mul_le_mul_of_nonneg_left hzLower (norm_nonneg _)
          _ = ‖s'‖ := by rw [mul_comm, hnormProd]
      have hdiv := (le_div_iff₀ hδA).2 hmul
      have hdivBound : ‖s'‖ / δA ≤ (‖s‖ + rs) / δA := by
        rw [div_le_div_iff₀ hδA hδA]
        exact mul_le_mul_of_nonneg_right hsBound hδA.le
      calc
        ‖w‖ ≤ ‖s'‖ / δA := hdiv
        _ ≤ (‖s‖ + rs) / δA := hdivBound
        _ ≤ Rw := by dsimp [Rw, Sbound]; linarith
    obtain ⟨hzX, _⟩ := hXzmem z q' hzUpper hgz hq' hAz
    obtain ⟨hwX, _⟩ := hXwmem w q' hwUpper hgw hq' hBw
    exact ⟨⟨hzX, hwX⟩, hAz, hBw⟩
  let Bad : Set (ℂ × ℂ) := C \ V
  have hBadclosed : IsClosed Bad := by
    change IsClosed (C ∩ Vᶜ)
    exact hCclosed.inter (isClosed_compl_iff.mpr hVopen)
  have hBadcompact : IsCompact Bad :=
    hDcompact.of_isClosed_subset hBadclosed (by
      intro v hv
      exact hv.1.1)
  have hΦBad : ContinuousOn Φ Bad :=
    hΦcont.mono (by intro v hv; exact hv.1.1)
  have hΦBadCompact : IsCompact (Φ '' Bad) := hBadcompact.image_of_continuousOn hΦBad
  have hcenterNot : (s, q) ∉ Φ '' Bad := by
    rintro ⟨v, hv, hΦv⟩
    rcases hv with ⟨hvC, hvNotV⟩
    have hvD : v ∈ D := hvC.1
    have hGzero : G v = 0 := by
      change v ∈ D ∧ G v = 0 at hvC
      exact hvC.2
    have hΦeq : v.1 * v.2 = s ∧ A v.1 = q := by simpa [Φ] using hΦv
    have hBq : B v.2 = q := by
      have hbal : A v.1 = B v.2 := sub_eq_zero.mp hGzero
      exact hbal.symm.trans hΦeq.2
    have hznonzero : d.g v.1 ≠ 0 := hXznonzero v.1 hvD.1
    have hwnonzero : e.g v.2 ≠ 0 := hXwnonzero v.2 hvD.2
    have hzlog : logarithmicValue d.multiplicity d.g v.1 = (q : OnePoint ℂ) := by
      rw [logarithmicValue_eq_coe_finiteLogDerivative d hznonzero]
      exact congrArg (fun x : ℂ => (x : OnePoint ℂ)) hΦeq.2
    have hwlog : logarithmicValue d.multiplicity (reflected d.g) v.2 = (q : OnePoint ℂ) := by
      change logarithmicValue e.multiplicity e.g v.2 = (q : OnePoint ℂ)
      rw [logarithmicValue_eq_coe_finiteLogDerivative e hwnonzero]
      exact congrArg (fun x : ℂ => (x : OnePoint ℂ)) hBq
    have hvfiber : v ∈ physicalFiber d s (q : OnePoint ℂ) :=
      ⟨hΦeq.1, hzlog, hwlog⟩
    exact hvNotV (hVfiber hvfiber)
  have hcomplementNhds : (Φ '' Bad)ᶜ ∈ 𝓝 (s, q) :=
    hΦBadCompact.isClosed.isOpen_compl.mem_nhds hcenterNot
  obtain ⟨U, W, hUopen, hsU, hWopen, hqW, hUW⟩ :=
    mem_nhds_prod_iff'.mp hcomplementNhds
  let U' : Set ℂ := U ∩ U₀
  let W' : Set ℂ := W ∩ W₀
  have hU'open : IsOpen U' := by
    exact hUopen.inter (by dsimp [U₀]; exact Metric.isOpen_ball)
  have hW'open : IsOpen W' := by
    exact hWopen.inter (by dsimp [W₀]; exact Metric.isOpen_ball)
  have hsU' : s ∈ U' := ⟨hsU, hsU₀⟩
  have hqW' : q ∈ W' := ⟨hqW, hqW₀⟩
  have hU'nonzero : ∀ s' ∈ U', s' ≠ 0 := by
    intro s' hs' hzero
    have hdist : dist s 0 < rs := by
      simpa [hzero, U₀, Metric.mem_ball, dist_comm] using hs'.2
    dsimp [rs] at hdist
    have : dist s 0 = ‖s‖ := by rw [dist_eq_norm]; simp
    rw [this] at hdist
    linarith
  have hW'neMultiplicity : ∀ q' ∈ W', q' ≠ (d.multiplicity : ℂ) := by
    intro q' hq' heq
    have hdist : dist q (d.multiplicity : ℂ) < r := by
      simpa [heq, W₀, Metric.mem_ball, dist_comm] using hq'.2
    dsimp [r] at hdist
    have hdist' : dist q (d.multiplicity : ℂ) = ‖q - (d.multiplicity : ℂ)‖ := dist_eq_norm _ _
    rw [hdist'] at hdist
    linarith [hqDist]
  have hU'W'sub : U' ×ˢ W' ⊆ (Φ '' Bad)ᶜ := by
    intro v hv
    exact hUW ⟨hv.1.1, hv.2.1⟩
  refine ⟨U', W', hU'open, hW'open, hsU', hqW', hU'nonzero, hW'neMultiplicity, ?_⟩
  intro s' hs' q' hq' v hv
  have hcoords := hwindow s' hs'.2 q' hq'.2 v hv
  have hvC : v ∈ C := by
    refine ⟨hcoords.1, ?_⟩
    change A v.1 - B v.2 = 0
    rw [hcoords.2.1, hcoords.2.2]
    ring
  by_contra hvV
  have hvBad : v ∈ Bad := ⟨hvC, hvV⟩
  have hΦeq : Φ v = (s', q') := by
    rcases hv with ⟨hprod, _, _⟩
    exact Prod.ext hprod hcoords.2.1
  exact (hU'W'sub ⟨hs', hq'⟩) ⟨v, hvBad, hΦeq⟩

private lemma physicalFiber_countable_of_value_ne_multiplicity {f : ℂ → ℂ}
    (d : NormalizedFunction f) (s q : ℂ) (hq : q ≠ (d.multiplicity : ℂ)) :
    (physicalFiber d s (q : OnePoint ℂ)).Countable := by
  have hleft := finiteLogDerivativeLevelSet_countable d hq
  have hright := finiteLogDerivativeLevelSet_countable (reflectedNormalized d) hq
  have hprod : (finiteLogDerivativeLevelSet d q ×ˢ
      finiteLogDerivativeLevelSet (reflectedNormalized d) q).Countable := hleft.prod hright
  apply hprod.mono
  rintro ⟨z, w⟩ ⟨_, hz, hw⟩
  change z ∈ finiteLogDerivativeLevelSet d q ∧
    w ∈ finiteLogDerivativeLevelSet (reflectedNormalized d) q
  · exact ⟨(logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet d).mp hz,
      (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet (reflectedNormalized d)).mp hw⟩

private noncomputable def criticalFiberProductsAt {f : ℂ → ℂ}
    (d : NormalizedFunction f) (q : ℂ) : Set ℂ :=
  (fun v : ℂ × ℂ => v.1 * v.2) ''
    (finiteLogDerivativeLevelSet d q ×ˢ finiteLogDerivativeLevelSet (reflectedNormalized d) q)

private noncomputable def criticalFiniteProducts {f : ℂ → ℂ}
    (d : NormalizedFunction f) : Set ℂ :=
  ⋃ q ∈ commonFiniteCriticalValues d \ {(d.multiplicity : ℂ)},
    criticalFiberProductsAt d q

private lemma criticalFiniteProducts_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) : (criticalFiniteProducts d).Countable := by
  have hvalues :
      (commonFiniteCriticalValues d \ {(d.multiplicity : ℂ)}).Countable :=
    (commonFiniteCriticalValues_countable d).mono (by
      intro q hq
      exact hq.1)
  apply hvalues.biUnion
  intro q hq
  have hqne : q ≠ (d.multiplicity : ℂ) := by
    intro heq
    apply hq.2
    simpa [heq]
  simpa [criticalFiberProductsAt] using
    ((finiteLogDerivativeLevelSet_countable d hqne).prod
      (finiteLogDerivativeLevelSet_countable (reflectedNormalized d) hqne)).image
      (fun v : ℂ × ℂ => v.1 * v.2)

private lemma finiteLogDerivativeLevelNumerator_eq_zero_of_mem_levelSet {f : ℂ → ℂ}
    (d : NormalizedFunction f) {q z : ℂ}
    (hz : z ∈ finiteLogDerivativeLevelSet d q) :
    finiteLogDerivativeLevelNumerator d q z = 0 := by
  rcases hz with ⟨hval, hgz⟩
  have hratio : z * deriv d.g z / d.g z = q - (d.multiplicity : ℂ) := by
    dsimp [finiteLogDerivative] at hval
    linear_combination hval
  have hmul := (div_eq_iff hgz).mp hratio
  dsimp [finiteLogDerivativeLevelNumerator]
  rw [hmul]
  ring

private lemma physicalFiber_finite_of_value_ne_multiplicity {f : ℂ → ℂ}
    (d : NormalizedFunction f) (s q : ℂ) (hs : s ≠ 0)
    (hq : q ≠ (d.multiplicity : ℂ)) :
    (physicalFiber d s (q : OnePoint ℂ)).Finite := by
  obtain ⟨δA, hδA, hAavoid⟩ := exists_ball_avoiding_level_value d hq
  obtain ⟨δB, hδB, hBavoid⟩ :=
    exists_ball_avoiding_level_value (reflectedNormalized d) hq
  let M : ℝ := ‖s‖ / δB + 1
  let K : Set ℂ :=
    Metric.closedBall (0 : ℂ) M ∩ (Metric.ball (0 : ℂ) δA)ᶜ
  have hKcompact : IsCompact K := by
    exact (isCompact_closedBall (0 : ℂ) M).inter_right
      (isClosed_compl_iff.mpr Metric.isOpen_ball)
  let T : Set ℂ := K ∩ {z | finiteLogDerivativeLevelNumerator d q z = 0}
  have hTdiscrete : IsDiscrete T := by
    have hzeros := zeroSet_isDiscrete_of_entire_nonzero
      (finiteLogDerivativeLevelNumerator_differentiable d q)
      (finiteLogDerivativeLevelNumerator_not_zero d hq)
    rw [isDiscrete_iff_forall_mem_exists_isOpen] at hzeros ⊢
    intro z hz
    obtain ⟨U, hUopen, hUeq⟩ := hzeros z hz.2
    refine ⟨U, hUopen, ?_⟩
    ext w
    constructor
    · rintro ⟨hwU, hwT⟩
      have hmem : w ∈ U ∩ {z | finiteLogDerivativeLevelNumerator d q z = 0} :=
        ⟨hwU, hwT.2⟩
      rw [hUeq] at hmem
      simpa using hmem
    · intro hw
      have hwz : w = z := by simpa using hw
      subst w
      have hzSingle : z ∈ ({z} : Set ℂ) := by simp
      rw [← hUeq] at hzSingle
      exact ⟨hzSingle.1, hz⟩
  have hzerosClosed : IsClosed {z | finiteLogDerivativeLevelNumerator d q z = 0} :=
    isClosed_eq (finiteLogDerivativeLevelNumerator_differentiable d q).continuous continuous_const
  have hTcompact : IsCompact T := by
    exact hKcompact.inter_right hzerosClosed
  have hTfinite : T.Finite := hTcompact.finite hTdiscrete
  let Z : Set ℂ := Prod.fst '' physicalFiber d s (q : OnePoint ℂ)
  have hZsubset : Z ⊆ T := by
    rintro x ⟨⟨z, w⟩, hv, rfl⟩
    rcases hv with ⟨hprod, hzval, hwval⟩
    have hzlevel : z ∈ finiteLogDerivativeLevelSet d q :=
      (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet d).mp hzval
    have hwlevel : w ∈ finiteLogDerivativeLevelSet (reflectedNormalized d) q :=
      (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet (reflectedNormalized d)).mp hwval
    have hznot : z ∉ Metric.ball (0 : ℂ) δA := by
      intro hzball
      exact (hAavoid z hzball) hzlevel.1
    have hwnot : w ∉ Metric.ball (0 : ℂ) δB := by
      intro hwball
      exact (hBavoid w hwball) hwlevel.1
    have hzlower : δA ≤ ‖z‖ := by
      apply le_of_not_gt
      intro hlt
      apply hznot
      simpa [Metric.mem_ball, dist_eq_norm] using hlt
    have hwlower : δB ≤ ‖w‖ := by
      apply le_of_not_gt
      intro hlt
      apply hwnot
      simpa [Metric.mem_ball, dist_eq_norm] using hlt
    have hnormProd : ‖z‖ * ‖w‖ = ‖s‖ := by
      rw [← norm_mul, hprod]
    have hmulBound : ‖z‖ * δB ≤ ‖s‖ := by
      calc
        ‖z‖ * δB ≤ ‖z‖ * ‖w‖ := mul_le_mul_of_nonneg_left hwlower (norm_nonneg _)
        _ = ‖s‖ := hnormProd
    have hzupper : ‖z‖ ≤ M := by
      have hdiv := (le_div_iff₀ hδB).2 hmulBound
      dsimp [M]
      linarith
    change z ∈ K ∩ {z | finiteLogDerivativeLevelNumerator d q z = 0}
    constructor
    · constructor
      · simpa [Metric.mem_closedBall, dist_eq_norm] using hzupper
      · simpa [Metric.mem_ball, dist_eq_norm] using hzlower
    · exact finiteLogDerivativeLevelNumerator_eq_zero_of_mem_levelSet d hzlevel
  have hZfinite : Z.Finite := hTfinite.subset hZsubset
  have hmaps : MapsTo Prod.fst (physicalFiber d s (q : OnePoint ℂ)) Z := by
    intro v hv
    exact ⟨v, hv, rfl⟩
  have hinj : InjOn Prod.fst (physicalFiber d s (q : OnePoint ℂ)) := by
    intro v hv v' hv' hfirst
    rcases v with ⟨z, w⟩
    rcases v' with ⟨z', w'⟩
    change z = z' at hfirst
    subst z'
    rcases hv with ⟨hprod, _, _⟩
    rcases hv' with ⟨hprod', _, _⟩
    change z * w = s at hprod
    change z * w' = s at hprod'
    have hz : z ≠ 0 := by
      intro hz0
      apply hs
      rw [← hprod, hz0]
      simp
    have hww : w = w' := mul_left_cancel₀ hz (hprod.trans hprod'.symm)
    subst w'
    rfl
  exact Set.Finite.of_injOn hmaps hinj hZfinite

private structure InverseChart (A : ℂ → ℂ) (center : ℂ) where
  U : Set ℂ
  W : Set ℂ
  ψ : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_W : IsOpen W
  center_mem : center ∈ U
  value_mem : A center ∈ W
  mapsToFunction : MapsTo A U W
  mapsTo : MapsTo ψ W U
  leftInverse : ∀ z ∈ U, ψ (A z) = z
  rightInverse : ∀ q ∈ W, A (ψ q) = q
  differentiable : DifferentiableOn ℂ ψ W

private def forwardRegularDomain {f : ℂ → ℂ} (d : NormalizedFunction f) : Set ℂ :=
  {z | d.g z ≠ 0 ∧ deriv (finiteLogDerivative d) z ≠ 0}

private def reflectedRegularDomain {f : ℂ → ℂ} (d : NormalizedFunction f) : Set ℂ :=
  {z | reflected d.g z ≠ 0 ∧
    deriv (finiteLogDerivative (reflectedNormalized d)) z ≠ 0}

private noncomputable def forwardInverseChartAt {f : ℂ → ℂ} (d : NormalizedFunction f)
    (z : {z // z ∈ forwardRegularDomain d}) :
    InverseChart (finiteLogDerivative d) z.1 := by
  classical
  have hExists : ∃ c : InverseChart (finiteLogDerivative d) z.1, True := by
    obtain ⟨U, W, ψ, hU, hW, hz, hq, hAmap, hmaps, hleft, hright, hdiff⟩ :=
      finiteLogDerivative_localInverse_chart d z.2.1 z.2.2
    exact ⟨⟨U, W, ψ, hU, hW, hz, hq, hAmap, hmaps, hleft, hright, hdiff⟩, trivial⟩
  exact Classical.choose hExists

private noncomputable def reflectedInverseChartAt {f : ℂ → ℂ}
    (d : NormalizedFunction f)
    (z : {z // z ∈ reflectedRegularDomain d}) :
    InverseChart (finiteLogDerivative (reflectedNormalized d)) z.1 := by
  classical
  have hExists : ∃ c : InverseChart (finiteLogDerivative (reflectedNormalized d)) z.1, True := by
    obtain ⟨U, W, ψ, hU, hW, hz, hq, hAmap, hmaps, hleft, hright, hdiff⟩ :=
      finiteLogDerivative_localInverse_chart (reflectedNormalized d) z.2.1 z.2.2
    exact ⟨⟨U, W, ψ, hU, hW, hz, hq, hAmap, hmaps, hleft, hright, hdiff⟩, trivial⟩
  exact Classical.choose hExists

private lemma countable_forward_inverse_chart_cover {f : ℂ → ℂ}
    (d : NormalizedFunction f) :
    ∃ C : Set {z // z ∈ forwardRegularDomain d}, C.Countable ∧
      forwardRegularDomain d ⊆ ⋃ z ∈ C, (forwardInverseChartAt d z).U := by
  have hL : IsLindelof (forwardRegularDomain d) :=
    isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨C, hcount, hcover⟩ := hL.elim_countable_subcover
    (fun z => (forwardInverseChartAt d z).U)
    (fun z => (forwardInverseChartAt d z).isOpen_U)
    (by
      intro z hz
      exact mem_iUnion.2 ⟨⟨z, hz⟩, (forwardInverseChartAt d ⟨z, hz⟩).center_mem⟩)
  exact ⟨C, hcount, hcover⟩

private lemma countable_reflected_inverse_chart_cover {f : ℂ → ℂ}
    (d : NormalizedFunction f) :
    ∃ C : Set {z // z ∈ reflectedRegularDomain d}, C.Countable ∧
      reflectedRegularDomain d ⊆ ⋃ z ∈ C, (reflectedInverseChartAt d z).U := by
  have hL : IsLindelof (reflectedRegularDomain d) :=
    isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨C, hcount, hcover⟩ := hL.elim_countable_subcover
    (fun z => (reflectedInverseChartAt d z).U)
    (fun z => (reflectedInverseChartAt d z).isOpen_U)
    (by
      intro z hz
      exact mem_iUnion.2 ⟨⟨z, hz⟩, (reflectedInverseChartAt d ⟨z, hz⟩).center_mem⟩)
  exact ⟨C, hcount, hcover⟩

private noncomputable def forwardChartCenters {f : ℂ → ℂ} (d : NormalizedFunction f) :
    Set {z // z ∈ forwardRegularDomain d} :=
  Classical.choose (countable_forward_inverse_chart_cover d)

private lemma forwardChartCenters_countable {f : ℂ → ℂ} (d : NormalizedFunction f) :
    (forwardChartCenters d).Countable := (Classical.choose_spec
      (countable_forward_inverse_chart_cover d)).1

private lemma forwardChartCenters_cover {f : ℂ → ℂ} (d : NormalizedFunction f) :
    forwardRegularDomain d ⊆
      ⋃ z ∈ forwardChartCenters d, (forwardInverseChartAt d z).U :=
  (Classical.choose_spec (countable_forward_inverse_chart_cover d)).2

private noncomputable def reflectedChartCenters {f : ℂ → ℂ}
    (d : NormalizedFunction f) : Set {z // z ∈ reflectedRegularDomain d} :=
  Classical.choose (countable_reflected_inverse_chart_cover d)

private lemma reflectedChartCenters_countable {f : ℂ → ℂ} (d : NormalizedFunction f) :
    (reflectedChartCenters d).Countable := (Classical.choose_spec
      (countable_reflected_inverse_chart_cover d)).1

private lemma reflectedChartCenters_cover {f : ℂ → ℂ} (d : NormalizedFunction f) :
    reflectedRegularDomain d ⊆
      ⋃ z ∈ reflectedChartCenters d, (reflectedInverseChartAt d z).U :=
  (Classical.choose_spec (countable_reflected_inverse_chart_cover d)).2

private noncomputable def productChartDomain {f : ℂ → ℂ} (d : NormalizedFunction f)
    (i : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) : Set ℂ :=
  (forwardInverseChartAt d i.1).W ∩ (reflectedInverseChartAt d i.2).W

private noncomputable def productChartValue {f : ℂ → ℂ} (d : NormalizedFunction f)
    (i : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d})
    (q : ℂ) : ℂ :=
  (forwardInverseChartAt d i.1).ψ q * (reflectedInverseChartAt d i.2).ψ q

private lemma exists_selected_product_chart_at_fiber_point {f : ℂ → ℂ}
    (d : NormalizedFunction f) (s q : ℂ)
    (hqnot : q ∉ commonFiniteCriticalValues d) (v : ℂ × ℂ)
    (hv : v ∈ physicalFiber d s (q : OnePoint ℂ)) :
    ∃ i : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d},
      i.1 ∈ forwardChartCenters d ∧ i.2 ∈ reflectedChartCenters d ∧
      v.1 ∈ (forwardInverseChartAt d i.1).U ∧
      v.2 ∈ (reflectedInverseChartAt d i.2).U ∧ q ∈ productChartDomain d i ∧
      productChartValue d i q = s := by
  rcases hv with ⟨hprod, hzval, hwval⟩
  have hzlevel := (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet d).mp hzval
  have hwlevel := (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet
    (reflectedNormalized d)).mp hwval
  rcases hzlevel with ⟨hAq, hgz⟩
  rcases hwlevel with ⟨hBq, hgw⟩
  have hAnot : finiteLogDerivative d v.1 ∉ commonFiniteCriticalValues d := by
    intro hmem
    exact hqnot (by simpa [hAq] using hmem)
  have hBnot : finiteLogDerivative (reflectedNormalized d) v.2 ∉
      commonFiniteCriticalValues d := by
    intro hmem
    exact hqnot (by simpa [hBq] using hmem)
  have hAderiv := finiteLogDerivative_deriv_ne_zero_of_not_common_critical d hgz hAnot
  have hBderiv := reflectedLogDerivative_deriv_ne_zero_of_not_common_critical d hgw hBnot
  let zReg : {z // z ∈ forwardRegularDomain d} := ⟨v.1, hgz, hAderiv⟩
  let wReg : {z // z ∈ reflectedRegularDomain d} := ⟨v.2, hgw, hBderiv⟩
  have hzcover := forwardChartCenters_cover d zReg.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzcover
  obtain ⟨hiCenter, hiSource⟩ := Set.mem_iUnion.mp hi
  have hwcover := reflectedChartCenters_cover d wReg.2
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hwcover
  obtain ⟨hjCenter, hjSource⟩ := Set.mem_iUnion.mp hj
  let ij : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d} :=
    (i, j)
  have hiSource' : v.1 ∈ (forwardInverseChartAt d i).U := by
    simpa [zReg] using hiSource
  have hjSource' : v.2 ∈ (reflectedInverseChartAt d j).U := by
    simpa [wReg] using hjSource
  have hqA : q ∈ (forwardInverseChartAt d i).W := by
    have := (forwardInverseChartAt d i).mapsToFunction hiSource'
    simpa [hAq] using this
  have hqB : q ∈ (reflectedInverseChartAt d j).W := by
    have := (reflectedInverseChartAt d j).mapsToFunction hjSource'
    simpa [hBq] using this
  have hψA : (forwardInverseChartAt d i).ψ q = v.1 := by
    have h := (forwardInverseChartAt d i).leftInverse v.1 hiSource'
    rw [hAq] at h
    exact h
  have hψB : (reflectedInverseChartAt d j).ψ q = v.2 := by
    have h := (reflectedInverseChartAt d j).leftInverse v.2 hjSource'
    rw [hBq] at h
    exact h
  refine ⟨ij, hiCenter, hjCenter, hiSource', hjSource', ⟨hqA, hqB⟩, ?_⟩
  simp [productChartValue, ij, hψA, hψB, hprod]

private noncomputable def productChartOverlap {f : ℂ → ℂ} (d : NormalizedFunction f)
    (i j : {z // z ∈ forwardRegularDomain d} ×
      {z // z ∈ reflectedRegularDomain d}) : Set ℂ :=
  productChartDomain d i ∩ productChartDomain d j

private noncomputable def productChartDifference {f : ℂ → ℂ} (d : NormalizedFunction f)
    (i j : {z // z ∈ forwardRegularDomain d} ×
      {z // z ∈ reflectedRegularDomain d}) (q : ℂ) : ℂ :=
  productChartValue d i q - productChartValue d j q

private lemma productChartValue_differentiableOn {f : ℂ → ℂ}
    (d : NormalizedFunction f)
    (i : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) :
    DifferentiableOn ℂ (productChartValue d i) (productChartDomain d i) := by
  exact (forwardInverseChartAt d i.1).differentiable.mono inter_subset_left |>.mul
    ((reflectedInverseChartAt d i.2).differentiable.mono inter_subset_right)

private lemma productChartDifference_analyticOnNhd {f : ℂ → ℂ}
    (d : NormalizedFunction f)
    (i j : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) :
    AnalyticOnNhd ℂ (productChartDifference d i j) (productChartOverlap d i j) := by
  have hi := (productChartValue_differentiableOn d i).mono (by
    intro q hq
    change q ∈ productChartDomain d i ∩ productChartDomain d j at hq
    exact hq.1)
  have hj := (productChartValue_differentiableOn d j).mono (by
    intro q hq
    change q ∈ productChartDomain d i ∩ productChartDomain d j at hq
    exact hq.2)
  have hdiff : DifferentiableOn ℂ (productChartDifference d i j)
      (productChartOverlap d i j) := by
    exact hi.sub hj
  have hopen : IsOpen (productChartOverlap d i j) := by
    exact ((forwardInverseChartAt d i.1).isOpen_W.inter
      (reflectedInverseChartAt d i.2).isOpen_W).inter
        ((forwardInverseChartAt d j.1).isOpen_W.inter
          (reflectedInverseChartAt d j.2).isOpen_W)
  exact hdiff.analyticOnNhd hopen

private noncomputable def productBranchCrossings {f : ℂ → ℂ}
    (d : NormalizedFunction f)
    (i j : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) :
    Set ℂ := isolatedZerosIn (productChartOverlap d i j) (productChartDifference d i j)

private lemma productBranchCrossings_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f)
    (i j : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) :
    (productBranchCrossings d i j).Countable := by
  exact isolatedZerosIn_countable _ _ (productChartDifference_analyticOnNhd d i j)

private noncomputable def productChartCenters {f : ℂ → ℂ}
    (d : NormalizedFunction f) :
    Set ({z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) :=
  forwardChartCenters d ×ˢ reflectedChartCenters d

private lemma productChartCenters_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) : (productChartCenters d).Countable :=
  (forwardChartCenters_countable d).prod (reflectedChartCenters_countable d)

private noncomputable def productBranchCrossingProductsAt {f : ℂ → ℂ}
    (d : NormalizedFunction f)
    (i j : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) :
    Set ℂ := (productChartValue d i) '' productBranchCrossings d i j

private noncomputable def productBranchCrossingProducts {f : ℂ → ℂ}
    (d : NormalizedFunction f) : Set ℂ :=
  ⋃ i ∈ productChartCenters d, ⋃ j ∈ productChartCenters d,
    productBranchCrossingProductsAt d i j

private lemma productBranchCrossingProducts_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) : (productBranchCrossingProducts d).Countable := by
  apply (productChartCenters_countable d).biUnion
  intro i hi
  apply (productChartCenters_countable d).biUnion
  intro j hj
  exact (productBranchCrossings_countable d i j).image (productChartValue d i)

private lemma exists_neighborhood_product_branches_equal {f : ℂ → ℂ}
    (d : NormalizedFunction f) (s q : ℂ)
    (hnot : s ∉ productBranchCrossingProducts d)
    (i j : {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d})
    (hi : i ∈ productChartCenters d) (hj : j ∈ productChartCenters d)
    (hq : q ∈ productChartOverlap d i j)
    (hpi : productChartValue d i q = s) (hpj : productChartValue d j q = s) :
    ∃ W : Set ℂ, IsOpen W ∧ q ∈ W ∧
      ∀ q' ∈ W, productChartValue d i q' = productChartValue d j q' := by
  have hnotZeros : q ∉ productBranchCrossings d i j := by
    intro hmem
    have hAt : s ∈ productBranchCrossingProductsAt d i j := by
      rw [← hpi]
      exact ⟨q, hmem, rfl⟩
    have hglobal : s ∈ productBranchCrossingProducts d := by
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      refine Set.mem_iUnion.2 ⟨hi, ?_⟩
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      exact Set.mem_iUnion.2 ⟨hj, hAt⟩
    exact hnot hglobal
  have hdiffzero : productChartDifference d i j q = 0 := by
    simp [productChartDifference, hpi, hpj]
  have hevent : ∀ᶠ q' : ℂ in 𝓝 q,
      productChartDifference d i j q' = 0 := by
    by_contra h
    apply hnotZeros
    exact ⟨hq, hdiffzero, h⟩
  obtain ⟨W, hWsub, hWopen, hqW⟩ := mem_nhds_iff.mp hevent
  refine ⟨W, hWopen, hqW, ?_⟩
  intro q' hq'
  exact sub_eq_zero.mp (hWsub hq')

private lemma regularTarget_of_product_not_exceptional {f : ℂ → ℂ}
    (d : NormalizedFunction f) (s q : ℂ) (hs : s ≠ 0)
    (hq : q ≠ (d.multiplicity : ℂ))
    (hqnot : q ∉ commonFiniteCriticalValues d)
    (hcross : s ∉ productBranchCrossingProducts d)
    (hfiber : (physicalFiber d s (q : OnePoint ℂ)).Nonempty) :
    RegularTarget d s q := by
  classical
  let e := reflectedNormalized d
  let A := finiteLogDerivative d
  let B := finiteLogDerivative e
  let FiberSet : Set (ℂ × ℂ) := physicalFiber d s (q : OnePoint ℂ)
  have hFiberFinite : FiberSet.Finite := by
    exact physicalFiber_finite_of_value_ne_multiplicity d s q hs hq
  let FiberPoint := {v // v ∈ FiberSet}
  letI : Finite FiberPoint := finite_coe_iff.mpr hFiberFinite
  letI : Fintype FiberPoint := Fintype.ofFinite FiberPoint
  rcases hfiber with ⟨v₀, hv₀⟩
  let p₀ : FiberPoint := ⟨v₀, hv₀⟩
  let pick : FiberPoint →
      {z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d} :=
    fun p => Classical.choose
      (exists_selected_product_chart_at_fiber_point d s q hqnot p.1 p.2)
  have hpick (p : FiberPoint) :=
    Classical.choose_spec (exists_selected_product_chart_at_fiber_point d s q hqnot p.1 p.2)
  let I : Finset
      ({z // z ∈ forwardRegularDomain d} × {z // z ∈ reflectedRegularDomain d}) :=
    Finset.univ.image pick
  let i₀ := pick p₀
  have hi₀ : i₀ ∈ I := Finset.mem_image.mpr ⟨p₀, Finset.mem_univ _, rfl⟩
  obtain ⟨hi₀F, hi₀R, hi₀z, hi₀w, hqdom₀, hp₀q⟩ := hpick p₀
  let V : Set (ℂ × ℂ) :=
    ⋃ i ∈ (I : Set ({z // z ∈ forwardRegularDomain d} ×
      {z // z ∈ reflectedRegularDomain d})),
        (forwardInverseChartAt d i.1).U ×ˢ (reflectedInverseChartAt d i.2).U
  have hVopen : IsOpen V := by
    exact isOpen_biUnion (fun i hi =>
      (forwardInverseChartAt d i.1).isOpen_U.prod
        (reflectedInverseChartAt d i.2).isOpen_U)
  have hVfiber : FiberSet ⊆ V := by
    intro v hv
    let p : FiberPoint := ⟨v, hv⟩
    let i := pick p
    obtain ⟨_, _, hzU, hwU, _, _⟩ := hpick p
    have hi : i ∈ I := Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, ⟨hzU, hwU⟩⟩⟩
  obtain ⟨Ubase, Wbase, hUbaseOpen, hWbaseOpen, hsUbase, hqWbase,
      hUbaseNonzero, hWbaseNeMultiplicity, hproper⟩ :=
    physicalFiber_locally_in_source d s q hs hq V hVopen hVfiber
  have hEqExists (i : {z // z ∈ forwardRegularDomain d} ×
      {z // z ∈ reflectedRegularDomain d}) (hi : i ∈ (I : Set _)) :
      ∃ N : Set ℂ, IsOpen N ∧ q ∈ N ∧
        ∀ q' ∈ N, productChartValue d i q' = productChartValue d i₀ q' := by
    have hi' : i ∈ I := by simpa using hi
    rcases Finset.mem_image.mp hi' with ⟨p, hp, rfl⟩
    obtain ⟨hiF, hiR, _, _, hqdom, hpiq⟩ := hpick p
    have hipair : pick p ∈ productChartCenters d := ⟨hiF, hiR⟩
    have hi₀pair : i₀ ∈ productChartCenters d := ⟨hi₀F, hi₀R⟩
    exact exists_neighborhood_product_branches_equal d s q hcross (pick p) i₀
      hipair hi₀pair ⟨hqdom, hqdom₀⟩ hpiq hp₀q
  choose N hNopen hNq hNeq using hEqExists
  let Index := {i : {z // z ∈ forwardRegularDomain d} ×
      {z // z ∈ reflectedRegularDomain d} // i ∈ (I : Set _)}
  letI : Finite Index := finite_coe_iff.mpr I.finite_toSet
  letI : Fintype Index := Fintype.ofFinite Index
  let Wbranches : Set ℂ := ⋂ k : Index, N k.1 k.2
  have hWbranchesOpen : IsOpen Wbranches :=
    isOpen_iInter_of_finite fun k => hNopen k.1 k.2
  have hqWbranches : q ∈ Wbranches :=
    Set.mem_iInter.mpr fun k => hNq k.1 k.2
  have hbranchEq (i : {z // z ∈ forwardRegularDomain d} ×
      {z // z ∈ reflectedRegularDomain d}) (hi : i ∈ (I : Set _))
      (q' : ℂ) (hq' : q' ∈ Wbranches) :
      productChartValue d i q' = productChartValue d i₀ q' :=
    hNeq i hi q' (Set.mem_iInter.mp hq' ⟨i, hi⟩)
  have hbaseDomainOpen : IsOpen (productChartDomain d i₀) := by
    exact (forwardInverseChartAt d i₀.1).isOpen_W.inter
      (reflectedInverseChartAt d i₀.2).isOpen_W
  have hbaseValueCont : ContinuousOn (productChartValue d i₀) (productChartDomain d i₀) :=
    (productChartValue_differentiableOn d i₀).continuousOn
  let Wimage : Set ℂ := productChartDomain d i₀ ∩
    (productChartValue d i₀) ⁻¹' Ubase
  have hWimageOpen : IsOpen Wimage :=
    hbaseValueCont.isOpen_inter_preimage hbaseDomainOpen hUbaseOpen
  have hqWimage : q ∈ Wimage := by
    constructor
    · exact hqdom₀
    · change productChartValue d i₀ q ∈ Ubase
      rw [hp₀q]
      exact hsUbase
  let Wfinal : Set ℂ := Wbase ∩ Wbranches ∩ Wimage
  have hWfinalOpen : IsOpen Wfinal := by
    exact (hWbaseOpen.inter hWbranchesOpen).inter hWimageOpen
  have hqWfinal : q ∈ Wfinal := ⟨⟨hqWbase, hqWbranches⟩, hqWimage⟩
  let ψ : ℂ → ℂ := productChartValue d i₀
  have hψdiff : DifferentiableOn ℂ ψ Wfinal := by
    exact (productChartValue_differentiableOn d i₀).mono (by
      intro q' hq'
      change q' ∈ (Wbase ∩ Wbranches) ∩ Wimage at hq'
      exact hq'.2.1)
  have hψmaps : MapsTo ψ Wfinal Ubase := by
    intro q' hq'
    change q' ∈ (Wbase ∩ Wbranches) ∩ Wimage at hq'
    exact hq'.2.2
  refine ⟨Ubase, Wfinal, ψ, hUbaseOpen, hWfinalOpen, hsUbase, hqWfinal,
    hUbaseNonzero, ?_, hψdiff, hψmaps, ?_⟩
  · intro q' hq'
    exact hWbaseNeMultiplicity q' hq'.1.1
  · intro s' hs' q' hq'
    constructor
    · intro hfiber
      rcases hfiber with ⟨v, hv⟩
      have hvV : v ∈ V := hproper s' hs' q' hq'.1.1 hv
      rcases Set.mem_iUnion.mp hvV with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨hiI, hvU⟩
      rcases hvU with ⟨hzUi, hwUi⟩
      rcases hv with ⟨hprod, hzval, hwval⟩
      have hAz : A v.1 = q' := by
        simpa [A] using
          ((logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet d).mp hzval).1
      have hBw : B v.2 = q' := by
        simpa [B] using
          ((logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet e).mp hwval).1
      have hqdom : q' ∈ productChartDomain d i := by
        have hqA : q' ∈ (forwardInverseChartAt d i.1).W := by
          have h := (forwardInverseChartAt d i.1).mapsToFunction hzUi
          change A v.1 ∈ (forwardInverseChartAt d i.1).W at h
          rw [hAz] at h
          exact h
        have hqB : q' ∈ (reflectedInverseChartAt d i.2).W := by
          have h := (reflectedInverseChartAt d i.2).mapsToFunction hwUi
          change B v.2 ∈ (reflectedInverseChartAt d i.2).W at h
          rw [hBw] at h
          exact h
        exact ⟨hqA, hqB⟩
      have hψA : (forwardInverseChartAt d i.1).ψ q' = v.1 := by
        have h := (forwardInverseChartAt d i.1).leftInverse v.1 hzUi
        change (forwardInverseChartAt d i.1).ψ (A v.1) = v.1 at h
        rw [hAz] at h
        exact h
      have hψB : (reflectedInverseChartAt d i.2).ψ q' = v.2 := by
        have h := (reflectedInverseChartAt d i.2).leftInverse v.2 hwUi
        change (reflectedInverseChartAt d i.2).ψ (B v.2) = v.2 at h
        rw [hBw] at h
        exact h
      have hbranch : productChartValue d i q' = s' := by
        simp [productChartValue, hψA, hψB, hprod]
      have heq : productChartValue d i q' = productChartValue d i₀ q' :=
        hbranchEq i hiI q' hq'.1.2
      calc
        s' = productChartValue d i q' := hbranch.symm
        _ = productChartValue d i₀ q' := heq
    · intro hsequal
      let z : ℂ := (forwardInverseChartAt d i₀.1).ψ q'
      let w : ℂ := (reflectedInverseChartAt d i₀.2).ψ q'
      have hqdom : q' ∈ productChartDomain d i₀ := hq'.2.1
      have hAz : A z = q' := (forwardInverseChartAt d i₀.1).rightInverse q' hqdom.1
      have hBw : B w = q' := (reflectedInverseChartAt d i₀.2).rightInverse q' hqdom.2
      have hznonzero : d.g z ≠ 0 := by
        intro hzero
        have hAm : A z = (d.multiplicity : ℂ) := by simp [A, finiteLogDerivative, hzero]
        exact (hWbaseNeMultiplicity q' hq'.1.1) (hAz.symm.trans hAm)
      have hwnonzero : e.g w ≠ 0 := by
        intro hzero
        have heMultiplicity : e.multiplicity = d.multiplicity := rfl
        have hBm : B w = (d.multiplicity : ℂ) := by
          simp [B, finiteLogDerivative, hzero, heMultiplicity]
        exact (hWbaseNeMultiplicity q' hq'.1.1) (hBw.symm.trans hBm)
      have hzlog : logarithmicValue d.multiplicity d.g z = (q' : OnePoint ℂ) := by
        rw [logarithmicValue_eq_coe_finiteLogDerivative d hznonzero]
        exact congrArg (fun x : ℂ => (x : OnePoint ℂ)) hAz
      have hwlog : logarithmicValue d.multiplicity (reflected d.g) w = (q' : OnePoint ℂ) := by
        change logarithmicValue e.multiplicity e.g w = (q' : OnePoint ℂ)
        rw [logarithmicValue_eq_coe_finiteLogDerivative e hwnonzero]
        exact congrArg (fun x : ℂ => (x : OnePoint ℂ)) hBw
      have hprod : z * w = s' := by
        calc
          z * w = productChartValue d i₀ q' := by simp [z, w, productChartValue]
          _ = s' := hsequal.symm
      exact ⟨⟨z, w⟩, hprod, hzlog, hwlog⟩

private noncomputable def nonregularProductValues {f : ℂ → ℂ}
    (d : NormalizedFunction f) : Set ℂ :=
  criticalFiniteProducts d ∪ productBranchCrossingProducts d

private lemma nonregularProductValues_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) : (nonregularProductValues d).Countable :=
  (criticalFiniteProducts_countable d).union (productBranchCrossingProducts_countable d)

private noncomputable def exceptionalRadiusSet {f : ℂ → ℂ}
    (d : NormalizedFunction f) : Set ℝ :=
  {r | 0 < r ∧ ((r : ℂ) ^ 2) ∈ nonregularProductValues d}

private lemma exceptionalRadiusSet_countable {f : ℂ → ℂ}
    (d : NormalizedFunction f) : (exceptionalRadiusSet d).Countable := by
  apply countable_of_injective_of_countable_image
    (f := fun r : ℝ => (r : ℂ) ^ 2)
  · intro r hr s hs hrs
    have hrsSq : r ^ 2 = s ^ 2 := by
      have h := congrArg Complex.re hrs
      simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using h
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hrsSq with hrs | hrs
    · exact hrs
    · rcases hr with ⟨hrpos, _⟩
      rcases hs with ⟨hspos, _⟩
      linarith
  · apply (nonregularProductValues_countable d).mono
    rintro s ⟨r, ⟨_, hs⟩, rfl⟩
    exact hs

theorem exceptional_radii_proof {f : ℂ → ℂ} (d : NormalizedFunction f) :
    ∃ Q : Set ℝ, ExceptionalRadii d Q := by
  refine ⟨exceptionalRadiusSet d, exceptionalRadiusSet_countable d, ?_⟩
  intro r hr hrnot q hmq hfiber
  have hs : ((r : ℂ) ^ 2) ≠ 0 := by
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact pow_ne_zero 2 hrC
  have qCne : (q : ℂ) ≠ (d.multiplicity : ℂ) := by
    exact_mod_cast (ne_of_gt hmq)
  have hsnot : ((r : ℂ) ^ 2) ∉ nonregularProductValues d := by
    intro hmem
    apply hrnot
    exact ⟨hr, hmem⟩
  have hqnot : (q : ℂ) ∉ commonFiniteCriticalValues d := by
    intro hqmem
    rcases hfiber with ⟨v, hv⟩
    rcases hv with ⟨hprod, hzval, hwval⟩
    have hzlevel :=
      (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet d).mp hzval
    have hwlevel :=
      (logarithmicValue_eq_coe_iff_finiteLogDerivativeLevelSet (reflectedNormalized d)).mp hwval
    have hpairs : v ∈
        finiteLogDerivativeLevelSet d (q : ℂ) ×ˢ
          finiteLogDerivativeLevelSet (reflectedNormalized d) (q : ℂ) :=
      ⟨hzlevel, hwlevel⟩
    have hsCriticalAt : (r : ℂ) ^ 2 ∈ criticalFiberProductsAt d (q : ℂ) := by
      exact ⟨v, hpairs, hprod⟩
    have hqSet : (q : ℂ) ∈
        commonFiniteCriticalValues d \ {(d.multiplicity : ℂ)} := ⟨hqmem, qCne⟩
    have hsCritical : (r : ℂ) ^ 2 ∈ criticalFiniteProducts d := by
      exact Set.mem_iUnion.2 ⟨(q : ℂ), Set.mem_iUnion.2 ⟨hqSet, hsCriticalAt⟩⟩
    exact hsnot (Or.inl hsCritical)
  have hcross : (r : ℂ) ^ 2 ∉ productBranchCrossingProducts d := by
    intro hmem
    exact hsnot (Or.inr hmem)
  exact regularTarget_of_product_not_exceptional d ((r : ℂ) ^ 2) (q : ℂ)
    hs qCne hqnot hcross hfiber 

theorem radial_envelope_proof {f : ℂ → ℂ} (d : NormalizedFunction f) (Q : Set ℝ)
    (hQ : Q.Countable) : GoodRadii d Q := by
  intro a b ha hab
  obtain ⟨K, hLip⟩ := MaxModulusPoints.Liminf.radialEnvelope_lipschitzOn d ha hab.le
  have hLipU : LipschitzOnWith K (MaxModulusPoints.Liminf.radialEnvelope d) (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact hLip
  have hF : AbsolutelyContinuousOnInterval (MaxModulusPoints.Liminf.radialEnvelope d) a b :=
    hLipU.absolutelyContinuousOnInterval
  have hinc := MaxModulusPoints.Liminf.radialEnvelope_strictMono d ha hab
  obtain ⟨r, har, hrb, hrnotQ, hderivPos⟩ :=
    MaxModulusPoints.Liminf.exists_deriv_pos_away_countable hF hab hinc hQ
  have hrpos : 0 < r := lt_trans ha har
  have hFdiff := MaxModulusPoints.Liminf.radialEnvelope_differentiableAt_of_deriv_pos d hderivPos
  obtain ⟨z₀, hz₀, hz₀val, hz₀max⟩ := MaxModulusPoints.Liminf.radialEnvelope_spec d hrpos
  have hhalf : 0 < r / 2 := by linarith
  have hhalf_lt : r / 2 < r := by linarith
  obtain ⟨w₀, hw₀, hw₀val, _⟩ := MaxModulusPoints.Liminf.radialEnvelope_spec d hhalf
  have hFhalf : 0 ≤ MaxModulusPoints.Liminf.radialEnvelope d (r / 2) := by
    rw [← hw₀val]
    exact Complex.normSq_nonneg _
  have hFpos : 0 < MaxModulusPoints.Liminf.radialEnvelope d r :=
    lt_of_le_of_lt hFhalf (MaxModulusPoints.Liminf.radialEnvelope_strictMono d hhalf hhalf_lt)
  have hg₀ : d.g z₀ ≠ 0 := by
    intro hz
    rw [hz] at hz₀val
    simp at hz₀val
    linarith
  have hmax₀ (w : ℂ) (hw : ‖w‖ = r) : ‖d.g w‖ ≤ ‖d.g z₀‖ := by
    have hsq := hz₀max w hw
    rw [Complex.normSq_eq_norm_sq] at hsq hz₀val
    exact le_of_sq_le_sq (hsq.trans_eq hz₀val.symm) (norm_nonneg _)
  have hz₀f : z₀ ∈ MaxModulusPoints.maximumPoints f r := by
    refine ⟨hz₀, ?_⟩
    intro w hw
    calc
      ‖f w‖ = r ^ d.multiplicity * ‖d.g w‖ := norm_factor_on_circle d w hw
      _ ≤ r ^ d.multiplicity * ‖d.g z₀‖ :=
        mul_le_mul_of_nonneg_left (hmax₀ w hw) (by positivity)
      _ = ‖f z₀‖ := (norm_factor_on_circle d z₀ hz₀).symm
  let A₀ : ℂ := z₀ * deriv d.g z₀ / d.g z₀
  have hA₀im : A₀.im = 0 :=
    angular_logarithmic_value_real d z₀ (by rw [hz₀]; exact hrpos.ne')
      (fun w hw => hmax₀ w (by simpa [hz₀] using hw)) hg₀
  have hrad₀ :
      deriv (MaxModulusPoints.Liminf.radialEnvelope d) r =
        2 * MaxModulusPoints.Liminf.radialEnvelope d r * (A₀.re / r) := by
    have hsupp := MaxModulusPoints.Liminf.radialSupport_deriv_eq_envelope_deriv
      d hrpos z₀ hz₀ hz₀val hFdiff
    rw [(MaxModulusPoints.Liminf.radialSupport_hasDerivAt d hrpos z₀).deriv] at hsupp
    calc
      _ = 2 * (star (d.g z₀) * (deriv d.g z₀ * (z₀ / (r : ℂ)))).re := hsupp.symm
      _ = 2 * MaxModulusPoints.Liminf.radialEnvelope d r * (A₀.re / r) := by
        rw [radial_ratio_realpart_identity d hrpos z₀ hg₀, hz₀val]
        simp [A₀]
        ring
  have hscaled₀ : r * deriv (MaxModulusPoints.Liminf.radialEnvelope d) r =
      2 * MaxModulusPoints.Liminf.radialEnvelope d r * A₀.re := by
    rw [hrad₀]
    field_simp [hrpos.ne']
  have hA₀value : A₀.re =
      r * deriv (MaxModulusPoints.Liminf.radialEnvelope d) r /
        (2 * MaxModulusPoints.Liminf.radialEnvelope d r) := by
    rw [hscaled₀]
    field_simp [hFpos.ne']
  have hA₀pos : 0 < A₀.re := by rw [hA₀value]; positivity
  let q : ℝ := (d.multiplicity : ℝ) + A₀.re
  have hmq : (d.multiplicity : ℝ) < q := by
    dsimp [q]
    linarith
  refine ⟨r, q, har, hrb, hrnotQ, hmq, ?_⟩
  intro x hx
  change ‖x‖ = r ∧ (∀ w, ‖w‖ = r → ‖f w‖ ≤ ‖f x‖) at hx
  rcases hx with ⟨hxnorm, hxmax⟩
  have hxgmax (w : ℂ) (hw : ‖w‖ = r) : ‖d.g w‖ ≤ ‖d.g x‖ := by
    have hfw := hxmax w hw
    rw [norm_factor_on_circle d w hw, norm_factor_on_circle d x hxnorm] at hfw
    exact (mul_le_mul_iff_of_pos_left (pow_pos hrpos d.multiplicity)).1 hfw
  have hxgEq : ‖d.g x‖ = ‖d.g z₀‖ := le_antisymm (hmax₀ x hxnorm) (hxgmax z₀ hz₀)
  have hxval : Complex.normSq (d.g x) = MaxModulusPoints.Liminf.radialEnvelope d r := by
    calc
      Complex.normSq (d.g x) = ‖d.g x‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ = ‖d.g z₀‖ ^ 2 := by rw [hxgEq]
      _ = Complex.normSq (d.g z₀) := (Complex.normSq_eq_norm_sq _).symm
      _ = MaxModulusPoints.Liminf.radialEnvelope d r := hz₀val
  have hxg : d.g x ≠ 0 := by
    intro hxzero
    rw [hxzero] at hxval
    simp at hxval
    linarith
  let Ax : ℂ := x * deriv d.g x / d.g x
  have hAxIm : Ax.im = 0 := by
    apply angular_logarithmic_value_real d x (by rw [hxnorm]; exact hrpos.ne')
      (fun w hw => hxgmax w (by simpa [hxnorm] using hw)) hxg
  have hradx :
      deriv (MaxModulusPoints.Liminf.radialEnvelope d) r =
        2 * MaxModulusPoints.Liminf.radialEnvelope d r * (Ax.re / r) := by
    have hsupp := MaxModulusPoints.Liminf.radialSupport_deriv_eq_envelope_deriv
      d hrpos x hxnorm hxval hFdiff
    rw [(MaxModulusPoints.Liminf.radialSupport_hasDerivAt d hrpos x).deriv] at hsupp
    calc
      _ = 2 * (star (d.g x) * (deriv d.g x * (x / (r : ℂ)))).re := hsupp.symm
      _ = 2 * MaxModulusPoints.Liminf.radialEnvelope d r * (Ax.re / r) := by
        rw [radial_ratio_realpart_identity d hrpos x hxg, hxval]
        simp [Ax]
        ring
  have hscaledx : r * deriv (MaxModulusPoints.Liminf.radialEnvelope d) r =
      2 * MaxModulusPoints.Liminf.radialEnvelope d r * Ax.re := by
    rw [hradx]
    field_simp [hrpos.ne']
  have hAxValue : Ax.re =
      r * deriv (MaxModulusPoints.Liminf.radialEnvelope d) r /
        (2 * MaxModulusPoints.Liminf.radialEnvelope d r) := by
    rw [hscaledx]
    field_simp [hFpos.ne']
  have hAxRe : Ax.re = A₀.re := by rw [hAxValue, hA₀value]
  have hAxEq : Ax = (A₀.re : ℂ) := by
    apply Complex.ext
    · simpa [hAxRe]
    · simpa [hAxIm]
  have hfirstComplex : (d.multiplicity : ℂ) + Ax = (q : ℂ) := by
    rw [hAxEq]
    simp [q]
  have hfirst : logarithmicValue d.multiplicity d.g x = (q : ℂ) := by
    simpa only [logarithmicValue, if_neg hxg] using
      congrArg (fun c : ℂ => (c : OnePoint ℂ)) hfirstComplex
  have hrefval : MaxModulusPoints.Liminf.reflected d.g (star x) = star (d.g x) := by
    simp [MaxModulusPoints.Liminf.reflected]
  have hrefderiv :
      deriv (MaxModulusPoints.Liminf.reflected d.g) (star x) = star (deriv d.g x) := by
    unfold MaxModulusPoints.Liminf.reflected
    simpa [Function.comp_def] using
      congrFun (deriv_conj_conj (f := d.g)) (star x)
  have hrefnonzero : MaxModulusPoints.Liminf.reflected d.g (star x) ≠ 0 := by
    rw [hrefval]
    exact star_ne_zero.mpr hxg
  have hrefRatio :
      star x * deriv (MaxModulusPoints.Liminf.reflected d.g) (star x) /
        MaxModulusPoints.Liminf.reflected d.g (star x) = star Ax := by
    rw [hrefval, hrefderiv]
    simp [Ax, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  have hsecondComplex : (d.multiplicity : ℂ) + star Ax = (q : ℂ) := by
    rw [hAxEq]
    simp [q]
  have hsecond :
      logarithmicValue d.multiplicity (MaxModulusPoints.Liminf.reflected d.g) (star x) = (q : ℂ) := by
    simpa only [logarithmicValue, if_neg hrefnonzero, hrefRatio] using
      congrArg (fun c : ℂ => (c : OnePoint ℂ)) hsecondComplex
  have hprod : x * star x = (r : ℂ) ^ 2 := by
    calc
      x * star x = star x * x := mul_comm _ _
      _ = (Complex.normSq x : ℂ) := Complex.normSq_eq_conj_mul_self.symm
      _ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.normSq_eq_norm_sq]
      _ = (r : ℂ) ^ 2 := by rw [hxnorm]; norm_cast
  exact ⟨hprod, hfirst, hsecond⟩

theorem normalize_proof (f : ℂ → ℂ) (hf : MaxModulusPoints.Entire f)
    (hn : ¬ MaxModulusPoints.IsMonomial f) :
    Nonempty (MaxModulusPoints.Blueprint.NormalizedFunction f) := by
  have hfnz : ∃ z, f z ≠ 0 := by
    by_contra hfnz
    have hfzero (z : ℂ) : f z = 0 := by
      by_contra hz
      exact hfnz ⟨z, hz⟩
    apply hn
    refine ⟨0, 0, ?_⟩
    funext z
    simp [hfzero z]
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    MaxModulusPoints.Liminf.exists_factorization_at_origin f hf hfnz
  have hgnc : ¬ ∃ c : ℂ, ∀ z, g z = c := by
    rintro ⟨c, hc⟩
    apply hn
    refine ⟨c, m, ?_⟩
    funext z
    rw [hfactor z, hc z]
    ring
  exact ⟨⟨m, g, hg, hg0, hgnc, hfactor⟩⟩

theorem nonconstant_products_proof {f : ℂ → ℂ} (d : NormalizedFunction f) :
    NonconstantProducts d := by
  intro s hs
  simpa [MaxModulusPoints.Blueprint.reflected, MaxModulusPoints.Liminf.reflected] using
    (MaxModulusPoints.Liminf.reflected_product_nonconstant
      d.g d.entire d.at_zero d.nonconstant s)

private lemma encard_pow_fiber_le (k : ℕ) (hk : 0 < k) (c : ℂ) :
    ({z : ℂ | z ^ k = c} : Set ℂ).encard ≤ k := by
  classical
  let p : Polynomial ℂ := Polynomial.X ^ k - Polynomial.C c
  have hp : p ≠ 0 := by
    simpa [p] using Polynomial.X_pow_sub_C_ne_zero hk c
  let S : Finset ℂ := p.roots.toFinset
  have hset : {z : ℂ | z ^ k = c} = (S : Set ℂ) := by
    ext z
    simp [S, Polynomial.mem_roots hp, Polynomial.IsRoot, p]
    exact sub_eq_zero.symm
  rw [hset, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (calc
    S.card ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ k := Polynomial.card_roots_X_pow_sub_C hk c)

private lemma finiteLogDerivative_local_order {f : ℂ → ℂ}
    (d : NormalizedFunction f) :
    ∃ k : ℕ, 0 < k ∧ ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∀ᶠ z : ℂ in 𝓝 0,
        finiteLogDerivative d z - (d.multiplicity : ℂ) = z ^ k * u z := by
  let H : ℂ → ℂ := fun z => finiteLogDerivative d z - (d.multiplicity : ℂ)
  have hHanalytic : AnalyticAt ℂ H 0 := by
    exact (finiteLogDerivative_analyticAt d d.at_zero).sub analyticAt_const
  have hHzero : H 0 = 0 := by simp [H, finiteLogDerivative]
  have hnot : ¬ ∀ᶠ z : ℂ in 𝓝 0, H z = 0 := by
    intro hzero
    have hG : ∀ᶠ z : ℂ in 𝓝 0, d.g z ≠ 0 :=
      d.entire.continuous.continuousAt.eventually_ne d.at_zero
    have hderiv : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), deriv d.g z = 0 := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hzero, hG] with z hzA hgz hz0
      have hz0' : z ≠ 0 := by simpa using hz0
      have hzA' : finiteLogDerivative d z = (d.multiplicity : ℂ) := by
        dsimp [H] at hzA
        exact sub_eq_zero.mp hzA
      have hratio : z * deriv d.g z / d.g z = 0 := by
        have hsum : (d.multiplicity : ℂ) + z * deriv d.g z / d.g z =
            (d.multiplicity : ℂ) + 0 := by
          simpa [finiteLogDerivative] using hzA'
        exact add_left_cancel hsum
      have hnum : z * deriv d.g z = 0 :=
        (div_eq_zero_iff).mp hratio |>.resolve_right hgz
      exact (mul_eq_zero.mp hnum).resolve_left hz0'
    have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), deriv d.g z = 0 := hderiv.frequently
    have hwhole : AnalyticOnNhd ℂ (deriv d.g) Set.univ :=
      d.entire.deriv.differentiableOn.analyticOnNhd isOpen_univ
    have hderivZero := hwhole.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ (0 : ℂ)) hfreq
    have hconst : ∀ z, d.g z = d.g 0 := by
      intro z
      exact is_const_of_deriv_eq_zero d.entire
        (fun w => hderivZero (Set.mem_univ w)) z 0
    exact d.nonconstant ⟨d.g 0, fun z => hconst z⟩
  obtain ⟨k, u, hu, hu0, hfactor⟩ :=
    (hHanalytic.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnot
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hval := hfactor.self_of_nhds
    have hval0 : H 0 = u 0 := by simpa [hk0] using hval
    rw [hHzero] at hval0
    exact hu0 hval0.symm
  refine ⟨k, hk, u, hu, hu0, ?_⟩
  filter_upwards [hfactor] with z hz
  simpa using hz

private lemma finiteLogDerivative_small_fiber_bound {f : ℂ → ℂ}
    (d : NormalizedFunction f) :
    ∃ ε : ℝ, ∃ k : ℕ, 0 < ε ∧ 0 < k ∧
      ∀ q : OnePoint ℂ,
        ({z : ℂ | ‖z‖ < ε ∧
          logarithmicValue d.multiplicity d.g z = q} : Set ℂ).encard ≤ k := by
  obtain ⟨k, hk, u, hu, hu0, hfactor⟩ := finiteLogDerivative_local_order d
  let ρ : ℂ → ℂ := fun z => u z / u 0
  let ℓ : ℂ → ℂ := fun z => Complex.log (ρ z) / (k : ℂ)
  let R : ℂ → ℂ := fun z => Complex.exp (ℓ z)
  let e : ℂ → ℂ := fun z => z * R z
  have hρanalytic : AnalyticAt ℂ ρ 0 := by
    dsimp [ρ]
    exact hu.div_const
  have hρzero : ρ 0 = 1 := by simp [ρ, hu0]
  have hρslit0 : ρ 0 ∈ Complex.slitPlane := by
    rw [hρzero]
    exact Complex.one_mem_slitPlane
  have hρslit : ∀ᶠ z : ℂ in 𝓝 0, ρ z ∈ Complex.slitPlane :=
    hρanalytic.continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds hρslit0)
  have hℓanalytic : AnalyticAt ℂ ℓ 0 := by
    dsimp [ℓ]
    exact (hρanalytic.clog hρslit0).div_const
  have hRanalytic : AnalyticAt ℂ R 0 := by
    dsimp [R]
    exact analyticAt_cexp.comp hℓanalytic
  have hRzero : R 0 = 1 := by simp [R, ℓ, hρzero]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hRpow (z : ℂ) (hz : ρ z ∈ Complex.slitPlane) : R z ^ k = ρ z := by
    have harg : (k : ℂ) * ℓ z = Complex.log (ρ z) := by
      dsimp [ℓ]
      field_simp [hkC]
    calc
      R z ^ k = Complex.exp ((k : ℂ) * ℓ z) := by
        change (Complex.exp (ℓ z)) ^ k = _
        rw [← Complex.exp_nat_mul (ℓ z) k]
      _ = Complex.exp (Complex.log (ρ z)) := by rw [harg]
      _ = ρ z := Complex.exp_log (Complex.slitPlane_ne_zero hz)
  have heanalytic : AnalyticAt ℂ e 0 := by
    change AnalyticAt ℂ (fun z : ℂ => z * R z) 0
    exact analyticAt_id.mul hRanalytic
  have hederiv : deriv e 0 = 1 := by
    change deriv (fun z : ℂ => z * R z) 0 = 1
    simpa [Function.id_def, hRzero] using
      (deriv_fun_mul (c := id) (d := R) differentiableAt_id hRanalytic.differentiableAt)
  have hederiv_ne : deriv e 0 ≠ 0 := by rw [hederiv]; exact one_ne_zero
  let hstrict := heanalytic.hasStrictDerivAt
  let hstrictF := hstrict.hasStrictFDerivAt_equiv hederiv_ne
  let chart := hstrictF.toOpenPartialHomeomorph e
  have hsource0 : (0 : ℂ) ∈ chart.source := hstrictF.mem_toOpenPartialHomeomorph_source
  obtain ⟨εc, hεc, hballc⟩ :=
    Metric.nhds_basis_ball.mem_iff.mp (chart.open_source.mem_nhds hsource0)
  have hG : ∀ᶠ z : ℂ in 𝓝 0, d.g z ≠ 0 :=
    d.entire.continuous.continuousAt.eventually_ne d.at_zero
  have hevent : ∀ᶠ z : ℂ in 𝓝 0,
      (finiteLogDerivative d z - (d.multiplicity : ℂ) = z ^ k * u z) ∧
        d.g z ≠ 0 ∧ ρ z ∈ Complex.slitPlane := by
    filter_upwards [hfactor, hG, hρslit] with z hzFactor hzG hzR
    exact ⟨hzFactor, hzG, hzR⟩
  obtain ⟨εf, hεf, hballf⟩ := Metric.nhds_basis_ball.mem_iff.mp hevent
  let ε : ℝ := min εc εf
  have hε : 0 < ε := lt_min hεc hεf
  have hballSource : Metric.ball (0 : ℂ) ε ⊆ chart.source := by
    exact Subset.trans (Metric.ball_subset_ball (min_le_left _ _)) hballc
  have hballFactor : ∀ z ∈ Metric.ball (0 : ℂ) ε,
      (finiteLogDerivative d z - (d.multiplicity : ℂ) = z ^ k * u z) ∧
        d.g z ≠ 0 ∧ ρ z ∈ Complex.slitPlane := by
    intro z hz
    exact hballf (Metric.ball_subset_ball (min_le_right _ _) hz)
  have heInjective : InjOn e (Metric.ball (0 : ℂ) ε) := by
    intro x hx y hy hxy
    have hxsource := hballSource hx
    have hysource := hballSource hy
    calc
      x = chart.symm (e x) := (chart.left_inv hxsource).symm
      _ = chart.symm (e y) := congrArg chart.symm hxy
      _ = y := chart.left_inv hysource
  have hlocal (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) ε) :
      finiteLogDerivative d z - (d.multiplicity : ℂ) =
        u 0 * e z ^ k := by
    rcases hballFactor z hz with ⟨hzFactor, _, hzR⟩
    rw [hzFactor]
    calc
      z ^ k * u z = u 0 * (z ^ k * (u z / u 0)) := by field_simp [hu0]
      _ = u 0 * (z ^ k * R z ^ k) := by rw [hRpow z hzR]
      _ = u 0 * (z * R z) ^ k := by rw [mul_pow]
      _ = u 0 * e z ^ k := rfl
  have hcoord (q : OnePoint ℂ) :
      ({z : ℂ | ‖z‖ < ε ∧
        logarithmicValue d.multiplicity d.g z = q} : Set ℂ).encard ≤ k := by
    by_cases hq : q = OnePoint.infty
    · subst q
      have hempty : {z : ℂ | ‖z‖ < ε ∧
          logarithmicValue d.multiplicity d.g z = OnePoint.infty} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hz
        have hg := (hballFactor z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)).2.1
        simp [logarithmicValue, hg]
      rw [hempty]
      simp
    · obtain ⟨c, hq⟩ := OnePoint.ne_infty_iff_exists.mp hq
      let S : Set ℂ := {z : ℂ | z ∈ Metric.ball (0 : ℂ) ε ∧
        logarithmicValue d.multiplicity d.g z = (c : OnePoint ℂ)}
      let T : Set ℂ := {w : ℂ | w ^ k = (c - (d.multiplicity : ℂ)) / u 0}
      have hmap : MapsTo e S T := by
        intro z hz
        have hzFactor := hballFactor z hz.1
        have hzG : d.g z ≠ 0 := hzFactor.2.1
        have hAcoe :
            (((d.multiplicity : ℂ) + z * deriv d.g z / d.g z : ℂ) : OnePoint ℂ) =
              (c : OnePoint ℂ) := by
          simpa [logarithmicValue, hzG] using hz.2
        have hA : finiteLogDerivative d z = c := by
          change (d.multiplicity : ℂ) + z * deriv d.g z / d.g z = c
          exact OnePoint.coe_injective hAcoe
        have hEq : u 0 * e z ^ k = c - (d.multiplicity : ℂ) := by
          rw [← hlocal z hz.1]
          rw [hA]
        have hzroot : e z ^ k = (c - (d.multiplicity : ℂ)) / u 0 := by
          apply (eq_div_iff hu0).2
          simpa [mul_comm] using hEq
        exact hzroot
      have hinj : InjOn e S := by
        intro x hx y hy hxy
        exact heInjective hx.1 hy.1 hxy
      have hbound : T.encard ≤ k := by
        simpa [T] using encard_pow_fiber_le k hk
          ((c - (d.multiplicity : ℂ)) / u 0)
      have hencard := Set.encard_le_encard_of_injOn hmap hinj
      have hS : S.encard ≤ k := hencard.trans hbound
      have hSset : {z : ℂ | ‖z‖ < ε ∧
          logarithmicValue d.multiplicity d.g z = q} = S := by
        ext z
        constructor
        · rintro ⟨hz, hqz⟩
          refine ⟨?_, ?_⟩
          · simpa [Metric.mem_ball, dist_eq_norm] using hz
          · simpa [hq] using hqz
        · rintro ⟨hz, hqz⟩
          refine ⟨?_, ?_⟩
          · simpa [Metric.mem_ball, dist_eq_norm] using hz
          · simpa [hq] using hqz
      rw [hSset]
      exact hS
  refine ⟨ε, k, hε, hk, ?_⟩
  intro q
  simpa [Metric.mem_ball, dist_eq_norm] using hcoord q

theorem small_coordinate_bound_proof {f : ℂ → ℂ} (d : NormalizedFunction f) :
    ∃ L : ℕ, SmallCoordinateBound d L := by
  obtain ⟨ε₁, k₁, hε₁, hk₁, hbound₁⟩ := finiteLogDerivative_small_fiber_bound d
  let d₂ := reflectedNormalized d
  obtain ⟨ε₂, k₂, hε₂, hk₂, hbound₂⟩ := finiteLogDerivative_small_fiber_bound d₂
  let ε : ℝ := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  refine ⟨k₁ + k₂, ε, hε, ?_⟩
  intro s q hs
  let Z₁ : Set ℂ := {z | ‖z‖ < ε₁ ∧
    logarithmicValue d.multiplicity d.g z = q}
  let Z₂ : Set ℂ := {w | ‖w‖ < ε₂ ∧
    logarithmicValue d₂.multiplicity d₂.g w = q}
  let A : Set (ℂ × ℂ) :=
    {v | v ∈ physicalFiber d s q ∧ ‖v.1‖ < ε}
  let B : Set (ℂ × ℂ) :=
    {v | v ∈ physicalFiber d s q ∧ ‖v.2‖ < ε}
  let S : Set (ℂ × ℂ) :=
    {v | v ∈ physicalFiber d s q ∧ (‖v.1‖ < ε ∨ ‖v.2‖ < ε)}
  have hAmap : MapsTo Prod.fst A Z₁ := by
    intro v hv
    change v ∈ physicalFiber d s q ∧ ‖v.1‖ < ε at hv
    rcases hv with ⟨hvFiber, hvsmall⟩
    change ‖v.1‖ < ε₁ ∧ logarithmicValue d.multiplicity d.g v.1 = q
    change v.1 * v.2 = s ∧
      logarithmicValue d.multiplicity d.g v.1 = q ∧
      logarithmicValue d.multiplicity (MaxModulusPoints.Blueprint.reflected d.g) v.2 = q
      at hvFiber
    exact ⟨lt_of_lt_of_le hvsmall (min_le_left _ _), hvFiber.2.1⟩
  have hAinj : InjOn Prod.fst A := by
    intro v hv w hw hfst
    change v ∈ physicalFiber d s q ∧ ‖v.1‖ < ε at hv
    change w ∈ physicalFiber d s q ∧ ‖w.1‖ < ε at hw
    rcases hv with ⟨hvFiber, _⟩
    rcases hw with ⟨hwFiber, _⟩
    change v.1 * v.2 = s ∧ _ ∧ _ at hvFiber
    change w.1 * w.2 = s ∧ _ ∧ _ at hwFiber
    have hvne : v.1 ≠ 0 := by
      intro hz
      have hzero := hvFiber.1
      rw [hz, zero_mul] at hzero
      exact hs hzero.symm
    have hprod : v.1 * v.2 = v.1 * w.2 := by
      calc
        v.1 * v.2 = s := hvFiber.1
        _ = w.1 * w.2 := hwFiber.1.symm
        _ = v.1 * w.2 := by rw [← hfst]
    have hsecond : v.2 = w.2 := mul_left_cancel₀ hvne hprod
    exact Prod.ext hfst hsecond
  have hAenc : A.encard ≤ k₁ := by
    calc
      A.encard ≤ Z₁.encard := Set.encard_le_encard_of_injOn hAmap hAinj
      _ ≤ k₁ := by simpa [Z₁] using hbound₁ q
  have hBmap : MapsTo Prod.snd B Z₂ := by
    intro v hv
    change v ∈ physicalFiber d s q ∧ ‖v.2‖ < ε at hv
    rcases hv with ⟨hvFiber, hvsmall⟩
    change ‖v.2‖ < ε₂ ∧ logarithmicValue d₂.multiplicity d₂.g v.2 = q
    change v.1 * v.2 = s ∧
      logarithmicValue d.multiplicity d.g v.1 = q ∧
      logarithmicValue d.multiplicity (MaxModulusPoints.Blueprint.reflected d.g) v.2 = q
      at hvFiber
    have hlog : logarithmicValue d₂.multiplicity d₂.g v.2 = q := by
      simpa [d₂, reflectedNormalized, MaxModulusPoints.Blueprint.reflected,
        MaxModulusPoints.Liminf.reflected] using hvFiber.2.2
    exact ⟨lt_of_lt_of_le hvsmall (min_le_right _ _), hlog⟩
  have hBinj : InjOn Prod.snd B := by
    intro v hv w hw hsnd
    change v ∈ physicalFiber d s q ∧ ‖v.2‖ < ε at hv
    change w ∈ physicalFiber d s q ∧ ‖w.2‖ < ε at hw
    rcases hv with ⟨hvFiber, _⟩
    rcases hw with ⟨hwFiber, _⟩
    change v.1 * v.2 = s ∧ _ ∧ _ at hvFiber
    change w.1 * w.2 = s ∧ _ ∧ _ at hwFiber
    have hvne : v.2 ≠ 0 := by
      intro hz
      have hzero := hvFiber.1
      rw [hz, mul_zero] at hzero
      exact hs hzero.symm
    have hprod : v.2 * v.1 = v.2 * w.1 := by
      calc
        v.2 * v.1 = v.1 * v.2 := mul_comm _ _
        _ = s := hvFiber.1
        _ = w.1 * w.2 := hwFiber.1.symm
        _ = w.2 * w.1 := mul_comm _ _
        _ = v.2 * w.1 := by rw [← hsnd]
    have hfirst : v.1 = w.1 := mul_left_cancel₀ hvne hprod
    exact Prod.ext hfirst hsnd
  have hBenc : B.encard ≤ k₂ := by
    calc
      B.encard ≤ Z₂.encard := Set.encard_le_encard_of_injOn hBmap hBinj
      _ ≤ k₂ := by simpa [Z₂] using hbound₂ q
  have hSsub : S ⊆ A ∪ B := by
    intro v hv
    change v ∈ physicalFiber d s q ∧ (‖v.1‖ < ε ∨ ‖v.2‖ < ε) at hv
    rcases hv.2 with h | h
    · exact Or.inl ⟨hv.1, h⟩
    · exact Or.inr ⟨hv.1, h⟩
  calc
    S.encard ≤ (A ∪ B).encard := Set.encard_le_encard hSsub
    _ ≤ A.encard + B.encard := Set.encard_union_le _ _
    _ ≤ (k₁ : ℕ∞) + (k₂ : ℕ∞) := add_le_add hAenc hBenc
    _ = ((k₁ + k₂ : ℕ) : ℕ∞) := by simp

end MaxModulusPoints.Blueprint.Packages
