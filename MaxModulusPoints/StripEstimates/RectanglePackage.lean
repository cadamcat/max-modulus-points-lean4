import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
import MaxModulusPoints.Blueprint.Interfaces.ClosedGateInterval
import MaxModulusPoints.Blueprint.Interfaces.Rectangle
import MaxModulusPoints.Blueprint.Interfaces.RectangleBarriers
import MaxModulusPoints.StripEstimates.BoundaryMaximum
/-!
# Rectangle gate bounds

A rational harmonic barrier bounds the effect of a shrinking boundary gate on
a separated vertical slice, as in Pardo-Simón–Sixsmith, Proposition 4.3.
-/

open Set Filter Metric Topology InnerProductSpace
open MaxModulusPoints.StripEstimates

namespace MaxModulusPoints.Blueprint.Packages

/-- A gate of length `s` on the right side contributes at most `4 * B * s / 3`
on the vertical slice at real part `1 / 4`. -/
theorem rectangle_barriers_proof : RectangleBarriers := by
  intro h y ρ _ _ _ _
  refine ⟨4 / 3, by norm_num, ?_⟩
  intro s B hs _ hB G hG hbound hboundary z hz hzre
  let D := rectangle h
  have hD : D = {w : ℂ | 0 < w.re} ∩
      ({w : ℂ | w.re < 1} ∩ ({w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < h})) := rfl
  have hopen : IsOpen D := by
    rw [hD]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hconn : IsPreconnected D := by
    rw [hD]
    exact ((convex_halfSpace_re_gt 0).inter ((convex_halfSpace_re_lt 1).inter
      ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_im_lt h)))).isPreconnected
  have hbounded : Bornology.IsBounded D := by
    refine isBounded_iff_forall_norm_le.mpr ⟨1 + h, ?_⟩
    intro w hw
    have hw' : 0 < w.re ∧ w.re < 1 ∧ 0 < w.im ∧ w.im < h := hw
    calc
      ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 1 + h := by rw [abs_of_pos hw'.1, abs_of_pos hw'.2.2.1]; linarith [hw'.2.1, hw'.2.2.2]
  let p : ℂ := ⟨1 + s / 2, y⟩
  let F : ℂ → ℂ := fun w => (s : ℂ) / (p - w)
  let v : ℂ → ℝ := fun w => (F w).re
  have hvformula (w : ℂ) : v w =
      s * (1 + s / 2 - w.re) / ((1 + s / 2 - w.re) ^ 2 + (y - w.im) ^ 2) := by
    simp [v, F, p, Complex.div_re, Complex.normSq_apply, pow_two]
  have hne (w : ℂ) (hw : w.re ≤ 1) : p - w ≠ 0 := by
    intro heq
    have heqre := congrArg Complex.re (sub_eq_zero.mp heq)
    change 1 + s / 2 = w.re at heqre
    linarith
  have hFanalytic (w : ℂ) (hw : w.re ≤ 1) : AnalyticAt ℂ F w :=
    analyticAt_const.div (analyticAt_const.sub analyticAt_id) (hne w hw)
  have hvharmonic : HarmonicOnNhd v D := by
    intro w hw
    exact (hFanalytic w hw.2.1.le).harmonicAt_re
  have hvnonneg (w : ℂ) (hw : w.re ≤ 1) : 0 ≤ v w := by
    rw [hvformula]
    have hx : 0 < 1 + s / 2 - w.re := by linarith
    positivity
  have hu : HarmonicOnNhd (fun w => (G w).re) D := by
    intro w hw
    exact (hG.analyticOnNhd hopen w hw).harmonicAt_re
  have hw : HarmonicOnNhd (fun w => (G w).re - B * v w) D := by
    simpa only [Pi.sub_def, Pi.smul_def, smul_eq_mul] using
      hu.sub (hvharmonic.const_smul (c := B))
  have hwboundary : ∀ q ∈ frontier D, ∀ b : ℝ, 0 < b →
      ∀ᶠ w in 𝓝[D] q, (G w).re - B * v w < b := by
    intro q hq b hb
    have hqre : q.re ≤ 1 := ContinuousWithinAt.closure_le
      (frontier_subset_closure hq) Complex.continuous_re.continuousWithinAt
      continuousWithinAt_const (fun _ hw => hw.2.1.le)
    have hvcont : ContinuousAt v q :=
      Complex.continuous_re.continuousAt.comp (hFanalytic q hqre).continuousAt
    have hboundaryPair : ∃ a : ℝ, a ≤ B * v q ∧
        ∀ c : ℝ, a < c → ∀ᶠ w in 𝓝[D] q, (G w).re < c := by
      by_cases hgate : q ∈ closedGateInterval y s
      · have hgate' : q.re = 1 ∧ |q.im - y| ≤ s / 2 := hgate
        have habs := abs_le.mp hgate'.2
        have hsq : (y - q.im) ^ 2 ≤ (s / 2) ^ 2 := by
          nlinarith [mul_nonneg (show 0 ≤ s / 2 - (q.im - y) by linarith)
            (show 0 ≤ s / 2 + (q.im - y) by linarith)]
        have hvone : 1 ≤ v q := by
          rw [hvformula, hgate'.1]
          have hd : 0 < (1 + s / 2 - 1) ^ 2 + (y - q.im) ^ 2 := by
            have hx : 0 < 1 + s / 2 - 1 := by linarith
            positivity
          apply (le_div_iff₀ hd).mpr
          nlinarith
        refine ⟨B, by nlinarith, ?_⟩
        intro c hc
        filter_upwards [self_mem_nhdsWithin] with w hwD
        exact (hbound w hwD).trans_lt hc
      · refine ⟨0, mul_nonneg hB.le (hvnonneg q hqre), ?_⟩
        intro c hc
        filter_upwards [hboundary q ⟨hq, hgate⟩ (c / 2) (by linarith)] with w hwc
        change (G w).re ≤ 0 + c / 2 at hwc
        linarith
    obtain ⟨a, hav, ha⟩ := hboundaryPair
    have hvnear : ∀ᶠ w in 𝓝[D] q, B * v q - b / 2 < B * v w :=
      ((continuousAt_const.mul hvcont).tendsto.mono_left nhdsWithin_le_nhds).eventually
        (eventually_gt_nhds (by linarith : B * v q - b / 2 < B * v q))
    filter_upwards [ha (a + b / 2) (by linarith), hvnear] with w hwa hwv
    linarith
  have hcompare := harmonic_le_of_boundary_limsup hopen hconn hbounded hw hwboundary
  have hx : 0 < 1 + s / 2 - z.re := by rw [hzre]; linarith
  have hvsmall : v z ≤ (4 / 3) * s := by
    rw [hvformula]
    calc
      s * (1 + s / 2 - z.re) /
          ((1 + s / 2 - z.re) ^ 2 + (y - z.im) ^ 2) ≤
          s * (1 + s / 2 - z.re) / (1 + s / 2 - z.re) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hx)
          (le_add_of_nonneg_right (sq_nonneg _))
      _ = s / (1 + s / 2 - z.re) := by field_simp
      _ ≤ (4 / 3) * s := by
        apply (div_le_iff₀ hx).mpr
        rw [hzre]
        nlinarith [sq_nonneg s]
  calc
    (G z).re ≤ B * v z := sub_nonpos.mp (hcompare z hz)
    _ ≤ B * ((4 / 3) * s) := mul_le_mul_of_nonneg_left hvsmall hB.le
    _ = B * (4 / 3) * s := by ring

end MaxModulusPoints.Blueprint.Packages
