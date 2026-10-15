import TauCeti.Analysis.Complex.Conformal.LengthArea
import Mathlib.Topology.Order.IntermediateValue
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.Basepoint
import MaxModulusPoints.TractGeometry.BlockPositions
import MaxModulusPoints.TractGeometry.Connectedness
import MaxModulusPoints.TractGeometry.EndBounds
import MaxModulusPoints.TractGeometry.GapPaths
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
import MaxModulusPoints.TractGeometry.RealAxisLimits
import MaxModulusPoints.TractGeometry.StripContainment
import MaxModulusPoints.TractGeometry.TargetGeometry
import MaxModulusPoints.TractGeometry.TargetGeometryProof
/-!
# Bounds on finite portions of a conformal tract

The exponential of the negative inverse has bounded image. Length–area
estimates provide a large circular crosscut whose inverse lies far to the
right. A retraction at a gap in the tract then bounds every finite portion.
-/

namespace MaxModulusPoints.TractGeometry

open Set Filter Metric Complex MeasureTheory
open Blueprint
open scoped Topology ENNReal Real

private theorem logPlus_mono_abs {u v : ℝ} (h : |u| ≤ |v|) :
    max 0 (Real.log |u|) ≤ max 0 (Real.log |v|) := by
  by_cases hu : |u| ≤ 1
  · rw [max_eq_left (Real.log_nonpos (abs_nonneg u) hu)]
    exact le_max_left _ _
  · exact max_le_max le_rfl (Real.log_le_log (by linarith [abs_nonneg u]) h)

private theorem target_positive_circle_arc {ρ a : ℝ} (hρ : 1 < ρ)
    (ha : a ∈ Icc 0 Real.pi) (hw : circleMap 0 ρ a ∈ target)
    {t : ℝ} (ht : t ∈ Icc 0 a) : circleMap 0 ρ t ∈ target := by
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  change -14 * max 0 (Real.log |(circleMap 0 ρ a).im|) <
    (circleMap 0 ρ a).re at hw
  change -14 * max 0 (Real.log |(circleMap 0 ρ t).im|) <
    (circleMap 0 ρ t).re
  simp only [circleMap_zero_re, circleMap_zero_im] at hw ⊢
  rcases lt_trichotomy t (Real.pi / 2) with hlt | heq | hgt
  · have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], hlt⟩
    have hm := le_max_left (0 : ℝ) (Real.log |ρ * Real.sin t|)
    have hp := mul_pos hρpos hc
    linarith
  · rw [heq, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one,
      abs_of_pos hρpos]
    have hl : 0 < Real.log ρ := Real.log_pos hρ
    rw [max_eq_right hl.le]
    linarith
  · have hcos : Real.cos a ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht.1 ha.2 ht.2
    have hsin : Real.sin a ≤ Real.sin t := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ t - Real.pi / 2 by linarith)
        (show a - Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos, ha.2])
        (sub_le_sub_right ht.2 (Real.pi / 2))
      simpa only [Real.cos_sub_pi_div_two] using h
    have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_mem_Icc ha
    have hst : 0 ≤ Real.sin t := Real.sin_nonneg_of_mem_Icc ⟨ht.1, ht.2.trans ha.2⟩
    have habs : |ρ * Real.sin a| ≤ |ρ * Real.sin t| := by
      rw [abs_of_nonneg (mul_nonneg hρpos.le hsa),
        abs_of_nonneg (mul_nonneg hρpos.le hst)]
      exact mul_le_mul_of_nonneg_left hsin hρpos.le
    have hlog := logPlus_mono_abs habs
    have hre := mul_le_mul_of_nonneg_left hcos hρpos.le
    linarith

private theorem exists_clean_cut (p : BlockParameters) (δ : GateIndex → ℝ) (R : ℝ) :
    ∃ s : ℝ, R < s ∧ -1 < s ∧
      ∀ y : ℝ, |y| < Real.pi / 2 → (⟨s, y⟩ : ℂ) ∈ tract p δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max R (-1))
  let a : ℝ := blockPosition p n
  have ha : 1 + 2 * (n : ℝ) ≤ a := by
    have hg := blockPosition_growth p (Nat.zero_le n)
    have hzero : 1 ≤ blockPosition p 0 := by
      simpa [blockPosition] using p.gap_ge_one 0
    simp only [Nat.cast_zero, sub_zero] at hg
    dsimp [a]
    linarith
  have hR : R < a + 3 / 2 := by
    have := le_max_left R (-1)
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hbase : -1 < a + 3 / 2 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  refine ⟨a + 3 / 2, hR, hbase, ?_⟩
  intro y hy
  apply (tract_gap_joined p δ (z := ⟨a + 3 / 2, y⟩) (by dsimp; linarith) hy ?_).source_mem
  intro k
  by_cases hk : k ≤ n
  · right
    have hg := blockPosition_growth p hk
    have hc : (k : ℝ) ≤ n := by exact_mod_cast hk
    change blockPosition p k + 1 < a + 3 / 2
    change blockPosition p k + 2 * ((n : ℝ) - (k : ℝ)) ≤ a at hg
    linarith
  · left
    have hnk : n < k := lt_of_not_ge hk
    have hg := blockPosition_growth p hnk.le
    have hc : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hnk
    change a + 3 / 2 < blockPosition p k
    change a + 2 * ((k : ℝ) - (n : ℝ)) ≤ blockPosition p k at hg
    linarith

private theorem tract_left_isConnected (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ gateUpper i) {s : ℝ}
    (hs : ∀ y : ℝ, |y| < Real.pi / 2 → (⟨s, y⟩ : ℂ) ∈ tract p δ) :
    IsConnected {z ∈ tract p δ | z.re ≤ s} := by
  let c : ℂ → ℂ := fun z => ⟨min z.re s, z.im⟩
  have hc : Continuous c :=
    Complex.equivRealProdCLM.symm.continuous.comp
      ((Complex.continuous_re.min continuous_const).prodMk Complex.continuous_im)
  have himage : c '' tract p δ = {z ∈ tract p δ | z.re ≤ s} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, min_le_right _ _⟩
      by_cases hws : w.re ≤ s
      · simpa only [c, min_eq_left hws, Complex.eta] using hw
      · simpa only [c, min_eq_right (le_of_not_ge hws)] using
          hs w.im (tract_im_lt p δ (fun i => (hδ i).2) hw)
    · rintro ⟨hz, hzs⟩
      refine ⟨z, hz, ?_⟩
      simp only [c, min_eq_left hzs, Complex.eta]
  rw [← himage]
  exact (tract_isConnected p δ (fun i => (hδ i).2) (fun i => (hδ i).1)).image c hc.continuousOn

private theorem target_circle_chord {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f target) {ρ : ℝ} (hρ : 1 < ρ)
    {w : ℂ} (hw : w ∈ target) (hnorm : ‖w‖ = ρ) :
    ENNReal.ofReal (dist (f (ρ : ℂ)) (f w)) ≤
      TauCeti.circleImageLength f target 0 ρ := by
  have hrepr : circleMap 0 ρ w.arg = w := by
    rw [circleMap_zero, ← hnorm]
    exact Complex.norm_mul_exp_arg_mul_I w
  have hzero : circleMap 0 ρ 0 = (ρ : ℂ) := by simp [circleMap_zero]
  have harg : circleMap 0 ρ w.arg ∈ target := by rwa [hrepr]
  by_cases ha : 0 ≤ w.arg
  · have h := TauCeti.ofReal_dist_le_circleImageLength target_geometry.open_domain hf 0
      (lt_trans zero_lt_one hρ) ha
      (show w.arg ≤ 0 + 2 * Real.pi by linarith [Complex.arg_le_pi w, Real.pi_pos])
      (fun θ hθ => target_positive_circle_arc hρ ⟨ha, Complex.arg_le_pi w⟩
        harg hθ)
      (fun θ hθ => target_positive_circle_arc hρ ⟨ha, Complex.arg_le_pi w⟩
        harg hθ)
    simpa only [hzero, hrepr] using h
  · have ha' : 0 ≤ -w.arg := by linarith
    have haπ : -w.arg ≤ Real.pi := by linarith [Complex.neg_pi_lt_arg w]
    have hstart : circleMap 0 ρ (-w.arg) ∈ target := by
      rw [← conj_circleMap_zero, hrepr]
      exact target_geometry.symmetric_domain w hw
    have hmem {θ : ℝ} (hθ : θ ∈ Icc w.arg 0) : circleMap 0 ρ θ ∈ target := by
      have hp := target_positive_circle_arc hρ ⟨ha', haπ⟩ hstart
        (show -θ ∈ Icc 0 (-w.arg) by constructor <;> linarith [hθ.1, hθ.2])
      have hs := target_geometry.symmetric_domain _ hp
      simpa only [Complex.star_def, conj_circleMap_zero, neg_neg] using hs
    have h := TauCeti.ofReal_dist_le_circleImageLength target_geometry.open_domain hf 0
      (lt_trans zero_lt_one hρ) (show w.arg ≤ 0 by linarith)
      (show 0 ≤ w.arg + 2 * Real.pi by linarith [Complex.neg_pi_lt_arg w, Real.pi_pos])
      (fun _ hθ => hmem hθ) (fun _ hθ => hmem hθ)
    simpa only [hzero, hrepr, dist_comm] using h

private theorem exists_large_short_circle {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    (hb : Bornology.IsBounded (f '' U)) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ ρ : ℝ, r < ρ ∧ TauCeti.circleImageLength f U 0 ρ < ENNReal.ofReal ε := by
  let A : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi) * volume (f '' U)
  have hA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb.measure_lt_top.ne
  let q : ℝ := (A.toReal + 1) / ε ^ 2
  have hq : 0 < q := div_pos (by positivity) (sq_pos_of_pos hε)
  let R : ℝ := r * Real.exp q
  have hrR : r < R := by
    have hexp : 1 < Real.exp q := Real.one_lt_exp_iff.mpr hq
    dsimp [R]
    nlinarith
  have hlog : Real.log (R / r) = q := by
    dsimp [R]
    rw [mul_div_cancel_left₀ _ hr.ne', Real.log_exp]
  have hc : A < ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (Real.log (R / r)) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg ε), hlog]
    have heq : ε ^ 2 * q = A.toReal + 1 := by
      dsimp [q]
      field_simp
    rw [heq]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hA).mpr (by linarith)
  obtain ⟨ρ, hρ, hsmall⟩ := TauCeti.exists_circleImageLength_sq_lt_of_volume_image
    hU hf hU.measurableSet (Subset.rfl) hinj 0 hr hrR hc
  refine ⟨ρ, hρ.1, ?_⟩
  rw [ENNReal.ofReal_pow hε.le] at hsmall
  by_contra h
  have hle : ENNReal.ofReal ε ≤ TauCeti.circleImageLength f U 0 ρ := le_of_not_gt h
  have hsq : ENNReal.ofReal ε ^ 2 ≤ TauCeti.circleImageLength f U 0 ρ ^ 2 := by gcongr
  exact (not_lt_of_ge hsq) hsmall

theorem tract_end_bounds : TractEndBounds := by
  intro p δ hδ e R
  have hupper : ∀ i, δ i ≤ gateUpper i := fun i => (hδ i).2
  obtain ⟨s, hRs, hbase, hcut⟩ := exists_clean_cut p δ R
  let f : ℂ → ℂ := fun w => Complex.exp (-e.invFun w)
  have hf : DifferentiableOn ℂ f target := e.inverse_holomorphic.neg.cexp
  have hfi : InjOn f target := by
    intro z hz w hw heq
    have hexp : Complex.exp (e.invFun z) = Complex.exp (e.invFun w) := by
      apply inv_injective
      simpa only [f, Complex.exp_neg] using heq
    have hinv := tract_exp_injective p δ hupper (e.inverse_mapsTo hz)
      (e.inverse_mapsTo hw) hexp
    calc
      z = e.toFun (e.invFun z) := (e.right_inv z hz).symm
      _ = e.toFun (e.invFun w) := congrArg e.toFun hinv
      _ = w := e.right_inv w hw
  have hfb : Bornology.IsBounded (f '' target) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Real.exp 2, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simp only [f, Complex.norm_exp, Complex.neg_re]
    apply Real.exp_le_exp.mpr
    linarith [tract_re_gt p δ (e.inverse_mapsTo hw)]
  let ε : ℝ := Real.exp (-s) / 3
  have hε : 0 < ε := div_pos (Real.exp_pos _) (by norm_num)
  obtain ⟨T, hT⟩ := tendsto_atTop_atTop.mp
    (tract_real_axis_limits p δ hupper e).2 (-Real.log ε)
  obtain ⟨ρ, hρ, hshort⟩ := exists_large_short_circle target_geometry.open_domain hf hfi hfb
    hε (show 0 < max 2 T from lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hρone : 1 < ρ := by linarith [le_max_left (2 : ℝ) T]
  have hρT : T ≤ ρ := (le_max_right (2 : ℝ) T).trans hρ.le
  have hreal : ‖f (ρ : ℂ)‖ ≤ ε := by
    simp only [f, Complex.norm_exp, Complex.neg_re]
    calc
      Real.exp (-(e.invFun (ρ : ℂ)).re) ≤ Real.exp (Real.log ε) :=
        Real.exp_le_exp.mpr (by linarith [hT ρ hρT])
      _ = ε := Real.exp_log hε
  have hpre {w : ℂ} (hw : w ∈ target) (hnorm : ‖w‖ = ρ) :
      s < (e.invFun w).re := by
    have hd : dist (f (ρ : ℂ)) (f w) < ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).mp
        ((target_circle_chord hf hρone hw hnorm).trans_lt hshort)
    have htri := dist_triangle (f w) (f (ρ : ℂ)) 0
    simp only [dist_zero_right] at htri
    rw [dist_comm (f w) (f (ρ : ℂ))] at htri
    have hnormf : ‖f w‖ < Real.exp (-s) := by
      have he : 0 < Real.exp (-s) := Real.exp_pos _
      dsimp [ε] at hd hreal
      linarith
    have he : -(e.invFun w).re < -s := by
      apply Real.exp_lt_exp.mp
      simpa only [f, Complex.norm_exp, Complex.neg_re] using hnormf
    linarith
  refine ⟨ρ, ?_⟩
  intro z hz hzR
  by_contra h
  have hzρ : ρ < ‖e.toFun z‖ := lt_of_not_ge h
  let S : Set ℂ := {v ∈ tract p δ | v.re ≤ s}
  have hS : IsConnected S := tract_left_isConnected p δ hδ hcut
  have hcont : ContinuousOn (fun v => ‖e.toFun v‖) S :=
    e.holomorphic.continuousOn.norm.mono (fun _ hv => hv.1)
  have hleft : (-1 : ℂ) ∈ S := ⟨tract_base_mem p δ, hbase.le⟩
  have hzS : z ∈ S := ⟨hz, hzR.trans hRs.le⟩
  have hbetween : ρ ∈ Icc ‖e.toFun (-1)‖ ‖e.toFun z‖ := by
    refine ⟨?_, hzρ.le⟩
    have he : e.toFun (-1) = 1 := by simpa using e.base_value
    simpa only [he, norm_one] using hρone.le
  obtain ⟨v, hv, hvρ⟩ := hS.isPreconnected.intermediate_value hleft hzS hcont hbetween
  have hvright := hpre (e.mapsTo hv.1) hvρ
  rw [e.left_inv v hv.1] at hvright
  exact (not_lt_of_ge hv.2) hvright

end MaxModulusPoints.TractGeometry
