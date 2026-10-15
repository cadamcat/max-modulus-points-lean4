import OAI.Probability.SLE.AngularLaws
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Construction.RealOrientation
/-!
# Compact strip containment from physical clearance

Pardo-Simón–Sixsmith, Proposition 4.1, bounds the strip coordinates of an
open chamber by joining its centre to a clean reference point. A uniform
clearance radius and a uniform speed bound give compact containment:
the omitted strip walls control the derivative, and their positive
distances have logarithms with uniformly bounded derivatives.
-/

namespace MaxModulusPoints.Construction

open Set Metric

noncomputable section

/-- Distance to the upper or lower horizontal boundary of the strip. -/
def stripWallDistance (upper : Bool) (z : ℂ) : ℝ :=
  if upper then 1 / 2 - z.im else 1 / 2 + z.im

theorem stripWallDistance_pos (upper : Bool) {z : ℂ} (hz : z ∈ Blueprint.strip) :
    0 < stripWallDistance upper z := by
  have h := abs_lt.mp (show |z.im| < 1 / 2 from hz)
  cases upper <;> dsimp [stripWallDistance] <;> linarith

/-- A strip-valued univalent map on a clearance ball has derivative bounded
by its distance to either omitted strip wall. -/
theorem strip_derivative_wall_bound {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball z r))
    (hi : InjOn f (ball z r)) (hm : MapsTo f (ball z r) Blueprint.strip)
    (upper : Bool) :
    ‖deriv f z‖ ≤ (128 * Real.pi / r) * stripWallDistance upper (f z) := by
  let y : ℝ := if upper then 1 / 2 else -1 / 2
  let a : ℂ := ((f z).re : ℂ) + (y : ℂ) * Complex.I
  have haim : |a.im| = 1 / 2 := by cases upper <;> norm_num [a, y]
  have hnot : a ∉ f '' ball z r := by
    rintro ⟨w, hw, he⟩
    have hmem : |(f w).im| < 1 / 2 := hm hw
    rw [he, haim] at hmem
    exact lt_irrefl _ hmem
  have hdiff : f z - a = (((f z).im - y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [a]
  have hnorm : ‖f z - a‖ = stripWallDistance upper (f z) := by
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    have hmem := abs_lt.mp (show |(f z).im| < 1 / 2 from hm (mem_ball_self hr))
    cases upper <;> dsimp [y, stripWallDistance]
    · rw [abs_of_nonneg (by linarith)]
      ring
    · rw [abs_of_nonpos (by linarith)]
      ring
  have hbound := OAI.SLEExactGauge.univalent_omitted_value_bound_ball hr hd hi a hnot
  rw [hnorm] at hbound
  calc
    ‖deriv f z‖ ≤ (128 * Real.pi * stripWallDistance upper (f z)) / r :=
      (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by ring

theorem hasDerivAt_stripWallDistance (upper : Bool) {β : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hβ : HasDerivAt β v t) :
    HasDerivAt (fun s => stripWallDistance upper (β s))
      (if upper then -v.im else v.im) t := by
  have him : HasDerivAt (fun s => (β s).im) v.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hβ
  cases upper
  · exact him.const_add (1 / 2)
  · exact him.const_sub (1 / 2)

/-- Relative wall-distance derivative bounds give a Lipschitz logarithm. -/
theorem log_stripWallDistance_lipschitz {β : ℝ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hβ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ β t)
    (hstrip : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ Blueprint.strip)
    (upper : Bool)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv β t‖ ≤ K * stripWallDistance upper (β t)) :
    LipschitzOnWith ⟨K, hK⟩ (fun t => Real.log (stripWallDistance upper (β t)))
      (Icc (0 : ℝ) 1) := by
  have hlog (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => Real.log (stripWallDistance upper (β s)))
        ((if upper then -(deriv β t).im else (deriv β t).im) /
          stripWallDistance upper (β t)) t :=
    (hasDerivAt_stripWallDistance upper (hβ t ht).hasDerivAt).log
      (stripWallDistance_pos upper (hstrip t ht)).ne'
  apply (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hlog t ht).hasDerivWithinAt)
  intro t ht
  change ‖(if upper then -(deriv β t).im else (deriv β t).im) /
    stripWallDistance upper (β t)‖ ≤ K
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (stripWallDistance_pos upper (hstrip t ht))]
  have habs : |if upper then -(deriv β t).im else (deriv β t).im| = |(deriv β t).im| := by
    cases upper <;> simp
  rw [habs]
  exact (div_le_iff₀ (stripWallDistance_pos upper (hstrip t ht))).mpr
    ((Complex.abs_im_le_norm _).trans (hspeed t ht))

/-- A common compact subset strictly inside the strip. -/
def stripConfinement (K : ℝ) : Set ℂ :=
  closedBall 0 (K / 2) ∩ {z : ℂ | |z.im| ≤ 1 / 2 - Real.exp (-K) / 2}

theorem stripConfinement_compact (K : ℝ) : IsCompact (stripConfinement K) :=
  (isCompact_closedBall _ _).inter_right
    (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem stripConfinement_subset_strip (K : ℝ) : stripConfinement K ⊆ Blueprint.strip := by
  intro z hz
  change |z.im| < 1 / 2
  have he := Real.exp_pos (-K)
  have hbound : |z.im| ≤ 1 / 2 - Real.exp (-K) / 2 := hz.2
  linarith

/-- A strip curve starting at zero stays in one compact subset when its speed
is bounded relative to both wall distances. -/
theorem strip_curve_confinement {β : ℝ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hβ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ β t)
    (hstrip : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ Blueprint.strip)
    (hzero : β 0 = 0)
    (hspeed : ∀ upper t, t ∈ Icc (0 : ℝ) 1 →
      ‖deriv β t‖ ≤ K * stripWallDistance upper (β t)) :
    MapsTo β (Icc (0 : ℝ) 1) (stripConfinement K) := by
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖deriv β t‖ ≤ K / 2 := by
    have hu := hspeed true t ht
    have hl := hspeed false t ht
    dsimp [stripWallDistance] at hu hl
    nlinarith
  have hLip : LipschitzOnWith ⟨K / 2, by positivity⟩ β (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le hβ hnorm
  have hwall (upper : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Real.exp (-K) / 2 ≤ stripWallDistance upper (β t) := by
    have hL := log_stripWallDistance_lipschitz hK hβ hstrip upper (hspeed upper)
    have hdist := hL.dist_le_mul t ht 0 (by norm_num)
    have htdist : dist t 0 ≤ 1 := by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; exact ht.2
    have hlog := hdist.trans (mul_le_mul_of_nonneg_left htdist hK)
    change dist (Real.log (stripWallDistance upper (β t)))
      (Real.log (stripWallDistance upper (β 0))) ≤ K * 1 at hlog
    rw [Real.dist_eq, hzero, mul_one] at hlog
    have hwallzero : stripWallDistance upper 0 = 1 / 2 := by
      cases upper <;> norm_num [stripWallDistance]
    rw [hwallzero] at hlog
    have hloglower : Real.log (1 / 2) - K ≤ Real.log (stripWallDistance upper (β t)) := by
      linarith [(abs_le.mp hlog).1]
    have he := Real.exp_le_exp.mpr hloglower
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2),
      Real.exp_log (stripWallDistance_pos upper (hstrip t ht))] at he
    calc
      Real.exp (-K) / 2 = (1 / 2) / Real.exp K := by rw [Real.exp_neg]; ring
      _ ≤ _ := he
  intro t ht
  refine ⟨?_, ?_⟩
  · have h := hLip.dist_le_mul t ht 0 (by norm_num)
    rw [hzero, dist_zero_right] at h
    change ‖β t‖ ≤ K / 2 * dist t 0 at h
    have hdist : dist t 0 ≤ 1 := by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; exact ht.2
    have hbound := h.trans (mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ K / 2))
    exact mem_closedBall_zero_iff.mpr (by simpa only [mul_one] using hbound)
  · have hu := hwall true t ht
    have hl := hwall false t ht
    dsimp [stripWallDistance] at hu hl
    change |(β t).im| ≤ 1 / 2 - Real.exp (-K) / 2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Clearance balls and a physical speed bound supply the relative strip-speed
bounds, hence a common compact set after real translation at the initial point. -/
theorem strip_map_curve_confinement {U : Set ℂ} {f : ℂ → ℂ} {α : ℝ → ℂ} {r V : ℝ}
    (hr : 0 < r) (hV : 0 ≤ V) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U)
    (hm : MapsTo f U Blueprint.strip)
    (hclear : ∀ t ∈ Icc (0 : ℝ) 1, ball (α t) r ⊆ U)
    (hα : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ α t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv α t‖ ≤ V)
    (hstart : (f (α 0)).im = 0) :
    MapsTo (fun t => f (α t) - ((f (α 0)).re : ℂ)) (Icc (0 : ℝ) 1)
      (stripConfinement ((128 * Real.pi / r) * V)) := by
  let β : ℝ → ℂ := fun t => f (α t) - ((f (α 0)).re : ℂ)
  have hK : 0 ≤ (128 * Real.pi / r) * V := by positivity
  have hαmem t (ht : t ∈ Icc (0 : ℝ) 1) : α t ∈ U := hclear t ht (mem_ball_self hr)
  have hfd t (ht : t ∈ Icc (0 : ℝ) 1) : DifferentiableAt ℂ f (α t) :=
    (hf.mono (hclear t ht)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hβder t (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt β (deriv α t * deriv f (α t)) t := by
    simpa only [β, smul_eq_mul, Function.comp_apply] using!
      (((hfd t ht).hasDerivAt.scomp t (hα t ht).hasDerivAt).sub_const ((f (α 0)).re : ℂ))
  refine strip_curve_confinement hK (fun t ht => (hβder t ht).differentiableAt) ?_ ?_ ?_
  · intro t ht
    change |(f (α t) - ((f (α 0)).re : ℂ)).im| < 1 / 2
    have hmem : |(f (α t)).im| < 1 / 2 := hm (hαmem t ht)
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hmem
  · change f (α 0) - ((f (α 0)).re : ℂ) = 0
    apply Complex.ext <;> simp [hstart]
  · intro upper t ht
    rw [(hβder t ht).deriv, norm_mul, mul_comm]
    have hbound := strip_derivative_wall_bound hr (hf.mono (hclear t ht))
      (hi.mono (hclear t ht)) (hm.mono_left (hclear t ht)) upper
    have hwallpos := stripWallDistance_pos upper (hm (hαmem t ht))
    have h := mul_le_mul hbound (hv t ht) (norm_nonneg _) (by positivity)
    calc
      ‖deriv f (α t)‖ * ‖deriv α t‖ ≤
          ((128 * Real.pi / r) * stripWallDistance upper (f (α t))) * V := h
      _ = ((128 * Real.pi / r) * V) * stripWallDistance upper (β t) := by
        simp only [β, stripWallDistance, Complex.sub_im, Complex.ofReal_im, sub_zero]
        ring

#print axioms strip_derivative_wall_bound
#print axioms log_stripWallDistance_lipschitz
#print axioms strip_curve_confinement
#print axioms strip_map_curve_confinement

end

end MaxModulusPoints.Construction
