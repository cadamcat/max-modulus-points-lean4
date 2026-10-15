import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.ParameterApproximation.SemicircleBounds
import MaxModulusPoints.ParameterApproximation.TargetMajorant
import MaxModulusPoints.StripEstimates.ExceptionalBoundary
import MaxModulusPoints.StripEstimates.HalfDisc
/-!
# Harmonic comparison from a reciprocal-height semicircle bound

A rational barrier transfers a bound on the semicircle to the diameter
midpoint. Only an individual upper bound is needed in the half-disc;
the comparison constant is determined by the semicircle values.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Metric Topology InnerProductSpace Blueprint StripEstimates

/-- A reciprocal-height bound on the semicircle controls a harmonic function
throughout the half-disc, with nonpositive diameter boundary upper limits. -/
theorem harmonic_half_disc_comparison {u : ℂ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hu3 : HarmonicOnNhd u (upperHalfDisc 3))
    (hbound : BddAbove (u '' upperHalfDisc 1))
    (hdiameter : ∀ p : ℂ, p.im = 0 → ‖p‖ < 1 → ∀ b : ℝ, 0 < b →
      ∀ᶠ z in 𝓝[upperHalfDisc 1] p, u z < b)
    (hcircle : ∀ q : ℂ, ‖q‖ = 1 → 0 < q.im → u q ≤ C / q.im)
    {z : ℂ} (hz : z ∈ upperHalfDisc 1) :
    u z ≤ C * upperHalfDiscBarrier z := by
  classical
  have hu : HarmonicOnNhd u (upperHalfDisc 1) :=
    hu3.mono (fun _ hw => ⟨by linarith [hw.1], hw.2⟩)
  let D := upperHalfDisc 1
  have hD : D = ball (0 : ℂ) 1 ∩ {z : ℂ | 0 < z.im} := by
    ext z
    simp only [D, upperHalfDisc, mem_ofPred_eq, mem_inter_iff, mem_ball, dist_zero_right]
  have hopen : IsOpen D := by
    rw [hD]
    exact isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hconn : IsPreconnected D := by
    rw [hD]
    exact ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hbounded : Bornology.IsBounded D :=
    (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset (by rw [hD]; exact inter_subset_left)
  let F : ℂ → ℂ := fun z => (1 - z)⁻¹ - (1 + z)⁻¹
  let v : ℂ → ℝ := fun z => (F z).im
  have hvformula (z : ℂ) :
      v z = z.im / ((1 - z.re) ^ 2 + z.im ^ 2) +
        z.im / ((1 + z.re) ^ 2 + z.im ^ 2) := by
    dsimp [v, F]
    simp only [Complex.sub_im, Complex.inv_im, Complex.normSq_apply, Complex.sub_re,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hFanalytic (z : ℂ) (hz1 : z ≠ 1) (hzn : z ≠ -1) : AnalyticAt ℂ F z := by
    change AnalyticAt ℂ (fun w : ℂ => (1 - w)⁻¹ - (1 + w)⁻¹) z
    apply AnalyticAt.sub
    · exact (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hz1.symm)
    · apply (analyticAt_const.add analyticAt_id).inv
      intro h
      apply hzn
      change 1 + z = 0 at h
      linear_combination h
  have hzends (z : ℂ) (hz : z ∈ D) : z ≠ 1 ∧ z ≠ -1 := by
    constructor <;> intro heq <;> have hi := hz.2
    · rw [heq] at hi
      norm_num at hi
    · rw [heq] at hi
      norm_num at hi
  have hvharmonic : HarmonicOnNhd v D := by
    intro z hz
    exact (hFanalytic z (hzends z hz).1 (hzends z hz).2).harmonicAt_im
  have hvnonneg (z : ℂ) (hz : z ∈ D) : 0 ≤ v z := by
    have hi : 0 < z.im := hz.2
    rw [hvformula]
    positivity
  let E : Finset ℂ := ({1, -1} : Finset ℂ).filter (fun p => p ∈ frontier D)
  have hEfront : (E : Set ℂ) ⊆ frontier D := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hw : HarmonicOnNhd (fun z => u z - C * v z) D := by
    simpa only [Pi.sub_def, Pi.smul_def, smul_eq_mul] using
      hu.sub (hvharmonic.const_smul (c := C))
  have hwbounded : BddAbove ((fun z => u z - C * v z) '' D) := by
    obtain ⟨B, hB⟩ := hbound
    refine ⟨B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have := mul_nonneg hC (hvnonneg z hz)
    have hub : u z ≤ B := hB ⟨z, hz, rfl⟩
    linarith
  have hwboundary : ∀ q ∈ frontier D, q ∉ E → ∀ b : ℝ, 0 < b →
      ∀ᶠ z in 𝓝[D] q, u z - C * v z < b := by
    intro q hq hqE b hb
    have hqends : q ≠ 1 ∧ q ≠ -1 := by
      simpa only [E, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        hq, and_true, not_or] using hqE
    have hqclosure : q ∈ closure D := frontier_subset_closure hq
    have hqnorm : ‖q‖ ≤ 1 := ContinuousWithinAt.closure_le hqclosure
      continuous_norm.continuousWithinAt continuousWithinAt_const (fun _ hz => hz.1.le)
    have hqim : 0 ≤ q.im := ContinuousWithinAt.closure_le hqclosure
      continuousWithinAt_const Complex.continuous_im.continuousWithinAt (fun _ hz => hz.2.le)
    have hqnot : q ∉ D := by
      intro hqd
      exact hq.2 (by simpa only [hopen.interior_eq] using hqd)
    have hvcont : ContinuousAt v q :=
      Complex.continuous_im.continuousAt.comp
        (hFanalytic q hqends.1 hqends.2).continuousAt
    have hboundaryPair : ∃ a : ℝ, a ≤ C * v q ∧
        ∀ c : ℝ, a < c → ∀ᶠ z in 𝓝[D] q, u z < c := by
      by_cases hi : q.im = 0
      · have hnormlt : ‖q‖ < 1 := by
          by_contra hn
          have heq : ‖q‖ = 1 := le_antisymm hqnorm (le_of_not_gt hn)
          have hsq := Complex.sq_norm_sub_sq_re q
          rw [heq, hi] at hsq
          have hprod : (q.re - 1) * (q.re + 1) = 0 := by nlinarith
          rcases mul_eq_zero.mp hprod with hre | hre
          · apply hqends.1
            apply Complex.ext
            · simp only [Complex.one_re]
              linarith
            · simpa only [Complex.one_im] using hi
          · apply hqends.2
            apply Complex.ext
            · simp only [Complex.neg_re, Complex.one_re]
              linarith
            · simpa only [Complex.neg_im, Complex.one_im, neg_zero] using hi
        refine ⟨0, ?_, fun c hc => hdiameter q hi hnormlt c hc⟩
        simp only [hvformula, hi, zero_div, add_zero, mul_zero, le_refl]
      · have hipos : 0 < q.im := lt_of_le_of_ne hqim (Ne.symm hi)
        have hnormeq : ‖q‖ = 1 := by
          by_contra hn
          exact hqnot ⟨lt_of_le_of_ne hqnorm hn, hipos⟩
        have hunit : q.re ^ 2 + q.im ^ 2 = 1 := by
          have hs := Complex.sq_norm_sub_sq_re q
          rw [hnormeq] at hs
          linarith
        have hx1 : 0 < 1 - q.re := by nlinarith [sq_pos_of_pos hipos]
        have hx2 : 0 < 1 + q.re := by nlinarith [sq_pos_of_pos hipos]
        have hd1 : (1 - q.re) ^ 2 + q.im ^ 2 = 2 * (1 - q.re) := by nlinarith
        have hd2 : (1 + q.re) ^ 2 + q.im ^ 2 = 2 * (1 + q.re) := by nlinarith
        have hvq : v q = 1 / q.im := by
          rw [hvformula, hd1, hd2]
          field_simp [ne_of_gt hx1, ne_of_gt hx2, ne_of_gt hipos] <;> nlinarith [hunit]
        refine ⟨u q, ?_, ?_⟩
        · simpa only [hvq, mul_one_div] using hcircle q hnormeq hipos
        · intro c hc
          have hucont : ContinuousAt u q :=
            (hu3 q ⟨by rw [hnormeq]; norm_num, hipos⟩).1.continuousAt
          exact (hucont.tendsto.mono_left nhdsWithin_le_nhds).eventually
            (eventually_lt_nhds hc)
    obtain ⟨a, hav, ha⟩ := hboundaryPair
    have hvnear : ∀ᶠ z in 𝓝[D] q, C * v q - b / 2 < C * v z :=
      ((continuousAt_const.mul hvcont).tendsto.mono_left nhdsWithin_le_nhds).eventually
        (eventually_gt_nhds (by linarith : C * v q - b / 2 < C * v q))
    filter_upwards [ha (a + b / 2) (by linarith), hvnear] with z hz hvz
    linarith
  have hcompare := harmonic_le_of_boundary_limsup_except_finite
    hopen hconn hbounded E hEfront hw hwbounded hwboundary
  simpa only [upperHalfDiscBarrier, hvformula] using sub_nonpos.mp (hcompare z hz)

/-- Three interior majorant values bound a target map near the midpoint of
a straight boundary segment, without a common bound on the whole half-disc. -/
theorem target_map_half_disc_normal_bound {G : ℂ → ℂ} {A : ℝ}
    (hG : DifferentiableOn ℂ G (upperHalfDisc 3))
    (hmaps : MapsTo G (upperHalfDisc 3) target)
    (hbound : BddAbove ((fun z => (G z).re) '' upperHalfDisc 1))
    (hdiameter : ∀ p : ℂ, p.im = 0 → ‖p‖ < 1 → ∀ b : ℝ, 0 < b →
      ∀ᶠ z in 𝓝[upperHalfDisc 1] p, (G z).re < b)
    (hA : ∀ s : ℝ, s = -1 ∨ s = 0 ∨ s = 1 →
      ‖targetMajorant (G ((s : ℂ) + Complex.I))‖ ≤ A)
    {y : ℝ} (hy : 0 < y) (hyone : y < 1) :
    (G ((y : ℂ) * Complex.I)).re ≤ 16 * (1 + A) * y := by
  have hAnonneg : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Or.inr (Or.inl rfl)))
  have hC : 0 ≤ 8 * (1 + A) := by positivity
  have hopen : IsOpen (upperHalfDisc 3) :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hu : HarmonicOnNhd (fun z => (G z).re) (upperHalfDisc 3) := by
    intro z hz
    exact (hG.analyticOnNhd hopen z hz).harmonicAt_re
  have hyD : (y : ℂ) * Complex.I ∈ upperHalfDisc 1 := by
    constructor
    · simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, abs_of_pos hy] using hyone
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using hy
  have hcomp := harmonic_half_disc_comparison hC hu hbound hdiameter
    (fun q hq hi => target_map_re_le_on_semicircle hG hmaps hA hq hi) hyD
  have hvaxis : upperHalfDiscBarrier ((y : ℂ) * Complex.I) = 2 * y / (1 + y ^ 2) := by
    dsimp [upperHalfDiscBarrier]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, sub_zero, one_pow]
    ring
  have hvle : upperHalfDiscBarrier ((y : ℂ) * Complex.I) ≤ 2 * y := by
    rw [hvaxis]
    exact div_le_self (by positivity) (by nlinarith [sq_nonneg y])
  calc
    (G ((y : ℂ) * Complex.I)).re ≤
        (8 * (1 + A)) * upperHalfDiscBarrier ((y : ℂ) * Complex.I) := hcomp
    _ ≤ (8 * (1 + A)) * (2 * y) := mul_le_mul_of_nonneg_left hvle hC
    _ = 16 * (1 + A) * y := by ring

#print axioms harmonic_half_disc_comparison
#print axioms target_map_half_disc_normal_bound

end MaxModulusPoints.ParameterApproximation
