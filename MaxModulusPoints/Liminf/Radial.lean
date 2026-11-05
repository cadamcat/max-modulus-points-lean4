module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import MaxModulusPoints.Blueprint.Data

/-!
# `MaxModulusPoints.Liminf.Radial`
-/

@[expose] public section

open MeasureTheory Set

open scoped ComplexConjugate Topology NNReal

namespace MaxModulusPoints.Liminf

open MaxModulusPoints.Blueprint

private lemma hasDerivAt_normSq_comp {h : ℂ → ℂ} {h' : ℂ} {x : ℝ}
    (hh : HasDerivAt h h' (x : ℂ)) :
    HasDerivAt (fun u : ℝ => Complex.normSq (h u))
      (2 * (star (h x) * h').re) x := by
  have hre := hh.real_of_complex
  have him : HasDerivAt (fun u : ℝ => (h u).im) h'.im x := by
    let k : ℂ → ℂ := fun w => -Complex.I * h w
    have hk : HasDerivAt k (-Complex.I * h') x := by
      simpa [k] using hh.const_mul (-Complex.I)
    have hkr := hk.real_of_complex
    convert hkr using 1
    · funext u
      simp [k, Complex.mul_re]
    · simp [Complex.mul_re]
  have hsum := (hre.pow 2).add (him.pow 2)
  convert hsum using 1
  · funext u
    simp [Complex.normSq, pow_two]
  · simp [Complex.mul_re]
    ring

noncomputable def radialEnvelope {f : ℂ → ℂ} (d : NormalizedFunction f) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ => Complex.normSq (d.g z)) '' {z | ‖z‖ = r})

lemma radialEnvelope_spec {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r : ℝ} (hr : 0 < r) :
    ∃ z : ℂ, ‖z‖ = r ∧ Complex.normSq (d.g z) = radialEnvelope d r ∧
      ∀ w : ℂ, ‖w‖ = r → Complex.normSq (d.g w) ≤ radialEnvelope d r := by
  let s : Set ℂ := Metric.sphere 0 r
  have hsphere : Metric.sphere (0 : ℂ) r = {z : ℂ | ‖z‖ = r} := by
    ext z
    simp [Metric.sphere, dist_eq_norm]
  have hne : s.Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp [s, hr.le]
  obtain ⟨z, hz, hsup⟩ := (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq hne
    (Complex.continuous_normSq.comp d.entire.continuous).continuousOn
  have hz' : ‖z‖ = r := by
    simpa [s, Metric.mem_sphere, dist_eq_norm] using hz
  have heq : radialEnvelope d r = Complex.normSq (d.g z) := by
    simpa [radialEnvelope, hsphere] using hsup
  refine ⟨z, hz', heq.symm, ?_⟩
  intro w hw
  have hwle : Complex.normSq (d.g w) ≤
      sSup ((fun z : ℂ => Complex.normSq (d.g z)) '' s) :=
    le_csSup ((isCompact_sphere (0 : ℂ) r).bddAbove_image
      (Complex.continuous_normSq.comp d.entire.continuous).continuousOn)
      ⟨w, by simpa [s, Metric.mem_sphere, dist_eq_norm] using hw, rfl⟩
  simpa [radialEnvelope, s, hsphere] using hwle

private lemma normSq_difference_le {A B M K δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAM : A ≤ M) (hBM : B ≤ M) (_hM : 0 ≤ M) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hAB : |A - B| ≤ K * δ) :
    A ^ 2 ≤ B ^ 2 + 2 * M * K * δ := by
  have hsum : A + B ≤ 2 * M := by linarith
  have hfactor : A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
  have hprod : (A - B) * (A + B) ≤ 2 * M * K * δ := by
    calc
      (A - B) * (A + B) ≤ |A - B| * (A + B) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (add_nonneg hA hB)
      _ ≤ (K * δ) * (2 * M) :=
        mul_le_mul hAB hsum (add_nonneg hA hB) (mul_nonneg hK hδ)
      _ = 2 * M * K * δ := by ring
  nlinarith

lemma radialEnvelope_lipschitzOn {f : ℂ → ℂ} (d : NormalizedFunction f)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ∃ K : ℝ≥0, LipschitzOnWith K (radialEnvelope d) (Icc a b) := by
  let disk : Set ℂ := Metric.closedBall 0 b
  have hdisk : IsCompact disk := isCompact_closedBall 0 b
  have hgcont : ContinuousOn (fun z : ℂ => ‖d.g z‖) disk :=
    continuous_norm.comp_continuousOn d.entire.continuous.continuousOn
  have hgbdd : BddAbove ((fun z : ℂ => ‖d.g z‖) '' disk) := hdisk.bddAbove_image hgcont
  obtain ⟨M₀, hM₀⟩ := hgbdd
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hM_bound : ∀ z ∈ disk, ‖d.g z‖ ≤ M := by
    intro z hz
    exact (hM₀ ⟨z, hz, rfl⟩).trans (le_max_left M₀ 0)
  have hderivcont : ContinuousOn (fun z : ℂ => ‖deriv d.g z‖) disk :=
    continuous_norm.comp_continuousOn d.entire.deriv.continuous.continuousOn
  have hderivbdd : BddAbove ((fun z : ℂ => ‖deriv d.g z‖) '' disk) :=
    hdisk.bddAbove_image hderivcont
  obtain ⟨D₀, hD₀⟩ := hderivbdd
  let D : ℝ := max D₀ 0
  have hD_nonneg : 0 ≤ D := le_max_right D₀ 0
  have hD_bound : ∀ z ∈ disk, ‖deriv d.g z‖ ≤ D := by
    intro z hz
    exact (hD₀ ⟨z, hz, rfl⟩).trans (le_max_left D₀ 0)
  let DN : ℝ≥0 := ⟨D, hD_nonneg⟩
  have hderivbound (z : ℂ) (hz : z ∈ disk) : ‖deriv d.g z‖₊ ≤ DN := by
    exact NNReal.coe_le_coe.mpr (hD_bound z hz)
  have hglip : LipschitzOnWith DN d.g disk :=
    (convex_closedBall 0 b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z _ => d.entire z) hderivbound
  let K : ℝ := 2 * M * D
  have hK : 0 ≤ K := by positivity
  refine ⟨Real.toNNReal K, ?_⟩
  apply LipschitzOnWith.of_le_add_mul' (s := Icc a b) K
  intro r hr u hu
  have hrpos : 0 < r := lt_of_lt_of_le ha hr.1
  have hupos : 0 < u := lt_of_lt_of_le ha hu.1
  obtain ⟨z, hz, hzval, hzmax⟩ := radialEnvelope_spec d hrpos
  let w : ℂ := ((u / r : ℝ) : ℂ) * z
  have hscale : ‖((u / r : ℝ) : ℂ)‖ = u / r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hupos hrpos)]
  have hw : ‖w‖ = u := by
    dsimp [w]
    rw [norm_mul, hscale, hz]
    exact (div_mul_cancel₀ u hrpos.ne')
  have hzDisk : z ∈ disk := by
    simp only [disk, Metric.mem_closedBall, dist_zero_right]
    rw [hz]
    exact hr.2
  have hwDisk : w ∈ disk := by
    simp only [disk, Metric.mem_closedBall, dist_zero_right]
    rw [hw]
    exact hu.2
  have hdist : ‖z - w‖ = |r - u| := by
    dsimp [w]
    have hsub : (1 : ℂ) - (u / r : ℝ) = ((1 - u / r : ℝ) : ℂ) := by push_cast; ring
    calc
      ‖z - ((u / r : ℝ) : ℂ) * z‖ = ‖(1 - (u / r : ℝ)) * z‖ := by congr 1 <;> ring
      _ = |1 - u / r| * r := by
        rw [norm_mul, hsub, Complex.norm_real, Real.norm_eq_abs, hz]
      _ = |r - u| := by
        rw [show 1 - u / r = (r - u) / r by field_simp]
        rw [abs_div, abs_of_pos hrpos]
        field_simp
  have hdistg : ‖d.g z - d.g w‖ ≤ D * |r - u| := by
    have h := hglip.dist_le_mul z hzDisk w hwDisk
    change dist (d.g z) (d.g w) ≤ D * dist z w at h
    simpa [dist_eq_norm, hdist] using h
  have hnormdiff : |‖d.g z‖ - ‖d.g w‖| ≤ D * |r - u| :=
    (abs_norm_sub_norm_le (d.g z) (d.g w)).trans hdistg
  have hsq := normSq_difference_le (norm_nonneg _) (norm_nonneg _)
      (hM_bound z hzDisk) (hM_bound w hwDisk) hM_nonneg hD_nonneg
      (abs_nonneg (r - u)) hnormdiff
  obtain ⟨zu, hzu, hzuval, hzumax⟩ := radialEnvelope_spec d hupos
  have hGwu : Complex.normSq (d.g w) ≤ radialEnvelope d u := hzumax w hw
  have hzr : radialEnvelope d r = ‖d.g z‖ ^ 2 := by
    rw [← hzval, Complex.normSq_eq_norm_sq]
  have hwu : ‖d.g w‖ ^ 2 ≤ radialEnvelope d u := by
    simpa [Complex.normSq_eq_norm_sq] using hGwu
  rw [hzr]
  calc
    ‖d.g z‖ ^ 2 ≤ ‖d.g w‖ ^ 2 + 2 * M * D * |r - u| := by
      exact hsq
    _ ≤ ‖d.g w‖ ^ 2 + K * dist r u := by
      simp [K, Real.dist_eq]
    _ ≤ radialEnvelope d u + K * dist r u := by
      exact add_le_add_left hwu (K * dist r u)

lemma radialEnvelope_strictMono {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r u : ℝ} (hr : 0 < r) (hru : r < u) : radialEnvelope d r < radialEnvelope d u := by
  obtain ⟨z, hz, hzval, hzmax⟩ := radialEnvelope_spec d hr
  obtain ⟨zu, hzu, hzuval, hzumax⟩ := radialEnvelope_spec d (hr.trans hru)
  have hzball : z ∈ Metric.ball (0 : ℂ) u := by
    simpa [Metric.mem_ball, dist_zero_right, hz] using hru
  have hboundary : ∀ w ∈ frontier (Metric.ball (0 : ℂ) u), ‖d.g w‖ ≤ ‖d.g zu‖ := by
    intro w hw
    have hwsphere := Metric.frontier_ball_subset_sphere hw
    have hwNorm : ‖w‖ = u := by
      simpa [Metric.sphere, dist_eq_norm] using hwsphere
    have hsq := hzumax w hwNorm
    rw [Complex.normSq_eq_norm_sq] at hsq hzuval
    exact le_of_sq_le_sq (hsq.trans_eq hzuval.symm) (norm_nonneg (d.g zu))
  have hnormAll : ∀ w ∈ Metric.ball (0 : ℂ) u, ‖d.g w‖ ≤ ‖d.g zu‖ := by
    intro w hw
    have hwcl : w ∈ closure (Metric.ball (0 : ℂ) u) := subset_closure hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      (d.entire.differentiableOn.diffContOnCl_ball (subset_univ _)) hboundary hwcl
  have hzSq : radialEnvelope d r = ‖d.g z‖ ^ 2 := by
    rw [← hzval, Complex.normSq_eq_norm_sq]
  have hzuSq : radialEnvelope d u = ‖d.g zu‖ ^ 2 := by
    rw [← hzuval, Complex.normSq_eq_norm_sq]
  have hle : radialEnvelope d r ≤ radialEnvelope d u := by
    rw [hzSq, hzuSq]
    exact (sq_le_sq₀ (norm_nonneg (d.g z)) (norm_nonneg (d.g zu))).2 (hnormAll z hzball)
  by_contra hnot
  have heq : radialEnvelope d r = radialEnvelope d u := le_antisymm hle (le_of_not_gt hnot)
  have hnormEq : ‖d.g z‖ = ‖d.g zu‖ := by
    apply le_antisymm
    · exact (sq_le_sq₀ (norm_nonneg (d.g z)) (norm_nonneg (d.g zu))).1 (by rw [← hzSq, heq, hzuSq])
    · exact (sq_le_sq₀ (norm_nonneg (d.g zu)) (norm_nonneg (d.g z))).1 (by rw [← hzuSq, ← heq, hzSq])
  have hmaxBall : IsMaxOn (norm ∘ d.g) (Metric.ball (0 : ℂ) u) z := by
    intro w hw
    calc
      ‖d.g w‖ ≤ ‖d.g zu‖ := hnormAll w hw
      _ = ‖d.g z‖ := hnormEq.symm
  have hconstantOn : Set.EqOn d.g (Function.const ℂ (d.g z)) (Metric.ball (0 : ℂ) u) :=
    Complex.eq_const_of_exists_max (d.entire.differentiableOn.mono (subset_univ _)) hzball hmaxBall
  have hevent : ∀ᶠ x : ℂ in 𝓝 (0 : ℂ), d.g x - d.g z = 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (hr.trans hru)] with x hx
    have hxball : x ∈ Metric.ball (0 : ℂ) u := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    simpa using congrArg (fun y : ℂ => y - d.g z) (hconstantOn hxball)
  have hfreq : ∃ᶠ x : ℂ in 𝓝[≠] (0 : ℂ), d.g x - d.g z = 0 :=
    (hevent.filter_mono nhdsWithin_le_nhds).frequently
  have hanalytic : AnalyticOnNhd ℂ (fun x : ℂ => d.g x - d.g z) Set.univ := by
    exact (d.entire.sub_const (d.g z)).differentiableOn.analyticOnNhd isOpen_univ
  have hzero := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ (0 : ℂ)) hfreq
  apply d.nonconstant
  refine ⟨d.g z, ?_⟩
  intro x
  have hx := hzero (Set.mem_univ x)
  exact sub_eq_zero.mp hx

noncomputable def radialSupport {f : ℂ → ℂ} (d : NormalizedFunction f) (r : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (d.g ((t : ℂ) * (z / (r : ℂ))))

lemma radialSupport_hasDerivAt {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    HasDerivAt (radialSupport d r z)
      (2 * (star (d.g z) * (deriv d.g z * (z / (r : ℂ)))).re) r := by
  let v : ℂ := z / (r : ℂ)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrv : (r : ℂ) * v = z := by
    dsimp [v]
    field_simp [hrC]
  have hpath : HasDerivAt (fun w : ℂ => w * v) v (r : ℂ) := by
    simpa [v] using (hasDerivAt_id (r : ℂ)).mul_const v
  have he : HasDerivAt (fun w : ℂ => d.g (w * v))
      (deriv d.g z * v) (r : ℂ) := by
    have houter : HasDerivAt d.g (deriv d.g z) ((r : ℂ) * v) := by
      simpa [hrv] using (d.entire z).hasDerivAt
    have hh := HasDerivAt.comp (r : ℂ) houter hpath
    simpa [Function.comp_def] using hh
  have hs := hasDerivAt_normSq_comp he
  change HasDerivAt
    (fun t : ℝ => Complex.normSq (d.g ((t : ℂ) * (z / (r : ℂ)))))
    (2 * (star (d.g z) * (deriv d.g z * (z / (r : ℂ)))).re) r
  simpa [Function.comp_def, v, hrv] using hs

lemma radialSupport_le_envelope {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r t : ℝ} (hr : 0 < r) (z : ℂ) (hz : ‖z‖ = r) (ht : 0 < t) :
    radialSupport d r z t ≤ radialEnvelope d t := by
  have hrC : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hvnorm : ‖z / (r : ℂ)‖ = 1 := by
    rw [norm_div, hz, hrC, div_self hr.ne']
  have htnorm : ‖(t : ℂ) * (z / (r : ℂ))‖ = t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, hvnorm]
    ring
  obtain ⟨w, hw, hwval, hwmax⟩ := radialEnvelope_spec d ht
  exact hwmax ((t : ℂ) * (z / (r : ℂ))) htnorm

lemma radialSupport_eq_envelope {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hzval : Complex.normSq (d.g z) = radialEnvelope d r) :
    radialSupport d r z r = radialEnvelope d r := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrv : (r : ℂ) * (z / (r : ℂ)) = z := by field_simp [hrC]
  simp [radialSupport, hrv, hzval]

lemma radialSupport_deriv_eq_envelope_deriv {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hz : ‖z‖ = r)
    (hzval : Complex.normSq (d.g z) = radialEnvelope d r)
    (hF : DifferentiableAt ℝ (radialEnvelope d) r) :
    deriv (radialSupport d r z) r = deriv (radialEnvelope d) r := by
  have hAt := radialSupport_eq_envelope d hr z hzval
  have hmin : IsLocalMin (fun t : ℝ => radialEnvelope d t - radialSupport d r z t) r := by
    change ∀ᶠ t : ℝ in 𝓝 r,
      radialEnvelope d r - radialSupport d r z r ≤
        radialEnvelope d t - radialSupport d r z t
    filter_upwards [Ioi_mem_nhds hr] with t ht
    have hle := radialSupport_le_envelope d hr z hz ht
    rw [hAt]
    linarith
  have hG := hF.hasDerivAt
  have hH := radialSupport_hasDerivAt d hr z
  have hdiff := hG.sub hH
  have hzDeriv := hmin.hasDerivAt_eq_zero hdiff
  rw [← hH.deriv] at hzDeriv
  exact (sub_eq_zero.mp hzDeriv).symm

lemma radialEnvelope_differentiableAt_of_deriv_pos {f : ℂ → ℂ} (d : NormalizedFunction f)
    {r : ℝ} (h : 0 < deriv (radialEnvelope d) r) :
    DifferentiableAt ℝ (radialEnvelope d) r := by
  by_contra hnd
  rw [deriv_zero_of_not_differentiableAt hnd] at h
  exact (lt_irrefl 0) h

noncomputable def angularSupport {f : ℂ → ℂ} (d : NormalizedFunction f) (z : ℂ)
    (t : ℝ) : ℝ :=
  Complex.normSq (d.g (z * Complex.exp ((t : ℂ) * Complex.I)))

lemma angularSupport_hasDerivAt {f : ℂ → ℂ} (d : NormalizedFunction f) (z : ℂ) :
    HasDerivAt (angularSupport d z)
      (2 * (star (d.g z) * (deriv d.g z * (z * Complex.I))).re) 0 := by
  let p : ℂ → ℂ := fun w => z * Complex.exp (w * Complex.I)
  have hlin : HasDerivAt (fun w : ℂ => w * Complex.I) Complex.I 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const Complex.I
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I)) Complex.I 0 := by
    have h := HasDerivAt.comp (0 : ℂ)
      (Complex.hasDerivAt_exp ((0 : ℂ) * Complex.I)) hlin
    simpa only [Function.comp_def, zero_mul, Complex.exp_zero, one_mul] using h
  have hp : HasDerivAt p (z * Complex.I) 0 := by
    simpa [p] using (HasDerivAt.const_mul z hexp)
  have houter : HasDerivAt d.g (deriv d.g z) (p 0) := by
    simpa [p] using (d.entire z).hasDerivAt
  have hh := HasDerivAt.comp (0 : ℂ) houter hp
  have hs := hasDerivAt_normSq_comp hh
  change HasDerivAt
    (fun t : ℝ => Complex.normSq (d.g (z * Complex.exp ((t : ℂ) * Complex.I))))
    (2 * (star (d.g z) * (deriv d.g z * (z * Complex.I))).re) 0
  simpa [Function.comp_def, p] using hs

/-- If an absolutely continuous function increases between two endpoints, its derivative
is positive somewhere outside any prescribed countable set in the interval. -/
theorem exists_deriv_pos_away_countable {F : ℝ → ℝ} {Q : Set ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b) (hab : a < b) (hinc : F a < F b)
    (hQ : Q.Countable) :
    ∃ r, a < r ∧ r < b ∧ r ∉ Q ∧ 0 < deriv F r := by
  by_contra hno
  have hQ' : (insert a (insert b Q)).Countable := hQ.insert b |>.insert a
  have hderiv_le : ∀ᵐ x ∂volume.restrict (Icc a b), deriv F x ≤ 0 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hQ'.ae_notMem volume] with x hxQ hxIcc
    have hxa : x ≠ a := by
      intro h
      subst x
      exact hxQ (by simp)
    have hxb : x ≠ b := by
      intro h
      subst x
      exact hxQ (by simp)
    have hnotQ : x ∉ Q := by
      intro hx
      exact hxQ (by simp [hx])
    have hleft : a < x := lt_of_le_of_ne hxIcc.1 hxa.symm
    have hright : x < b := lt_of_le_of_ne hxIcc.2 hxb
    have hnotpos : ¬ 0 < deriv F x := by
      intro hpos
      exact hno ⟨x, hleft, hright, hnotQ, hpos⟩
    exact le_of_not_gt hnotpos
  have hIntNeg : 0 ≤ ∫ x in a..b, -deriv F x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab.le
    filter_upwards [hderiv_le] with x hx
    exact neg_nonneg.mpr hx
  have hInt : ∫ x in a..b, deriv F x ≤ 0 := by
    have hNegEq : (∫ x in a..b, -deriv F x) = -(∫ x in a..b, deriv F x) := by simp
    rw [hNegEq] at hIntNeg
    linarith
  rw [hF.integral_deriv_eq_sub] at hInt
  linarith

end MaxModulusPoints.Liminf
