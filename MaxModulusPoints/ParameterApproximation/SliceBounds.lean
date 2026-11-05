module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.ParameterApproximation.CleanGapGeometry
public import MaxModulusPoints.ParameterApproximation.SemicircleBounds
public import MaxModulusPoints.ParameterApproximation.TargetMajorant
public import MaxModulusPoints.TractGeometry.StripContainment

/-!
# Uniform bounds on clean vertical slices

Three fixed interior values control the two endpieces of a clean slice.
Locally uniform convergence controls its compact middle segment, giving a
common real-part bound on the whole slice.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Metric Topology Blueprint TractGeometry StripEstimates

universe u

/-- The target majorant is continuous at every point of the target. -/
theorem continuousAt_targetMajorant {w : ℂ} (hw : w ∈ target) :
    ContinuousAt targetMajorant w := by
  have hshift : ContinuousAt (fun z : ℂ => z + 1) w :=
    continuousAt_id.add continuousAt_const
  have hlog : ContinuousAt (fun z : ℂ => Complex.log (z + 1)) w :=
    hshift.clog (target_add_one_mem_slitPlane hw)
  exact continuousAt_id.add (continuousAt_const.mul hlog)

/-- A middle-segment bound and three interior majorant values control an
entire clean slice, including its approaches to the two outer walls. -/
theorem clean_gap_slice_re_bound (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ) (G : LogModel (tract p δ)) {A B : ℝ}
    (hA : ∀ s : ℝ, s = -1 ∨ s = 0 ∨ s = 1 →
      ‖targetMajorant (G.toFun (cleanGapUpperChart p n ((s : ℂ) + Complex.I)))‖ ≤ A)
    (hB : ∀ z : ℂ, z.re = blockPosition p n + 3 / 2 →
      |z.im| ≤ Real.pi / 2 - 1 / 32 → (G.toFun z).re ≤ B)
    {z : ℂ} (hz : z ∈ tract p δ) (hre : z.re = blockPosition p n + 3 / 2) :
    (G.toFun z).re ≤ max B (16 * (1 + A)) := by
  have hAnonneg : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Or.inr (Or.inl rfl)))
  have hupper {w : ℂ} (hw : w ∈ tract p δ)
      (hwr : w.re = blockPosition p n + 3 / 2)
      (hwi : Real.pi / 2 - 1 / 32 < w.im) : (G.toFun w).re ≤ 16 * (1 + A) := by
    let y : ℝ := 16 * (Real.pi / 2 - w.im)
    have hwim := (abs_lt.mp (tract_im_lt p δ hδ hw)).2
    have hy : 0 < y := by dsimp [y]; linarith
    have hyone : y < 1 := by dsimp [y]; linarith
    have heq : cleanGapUpperChart p n ((y : ℂ) * Complex.I) = w := by
      apply Complex.ext
      · simpa [cleanGapUpperChart, Complex.mul_re, Complex.mul_im] using hwr.symm
      · simp [cleanGapUpperChart, Complex.mul_re, Complex.mul_im, y]
        <;> ring
    have hb := clean_gap_upper_normal_bound p δ hδ n G hA hy hyone
    rw [heq] at hb
    exact hb.trans (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hyone.le (by positivity : 0 ≤ 16 * (1 + A)))
  by_cases hmid : |z.im| ≤ Real.pi / 2 - 1 / 32
  · exact (hB z hre hmid).trans (le_max_left _ _)
  · have hend : Real.pi / 2 - 1 / 32 < |z.im| := lt_of_not_ge hmid
    by_cases hsign : 0 ≤ z.im
    · have hi : Real.pi / 2 - 1 / 32 < z.im := by
        simpa only [abs_of_nonneg hsign] using hend
      exact (hupper hz hre hi).trans (le_max_right _ _)
    · have hstar : star z ∈ tract p δ := G.symmetric_domain z hz
      have hrstar : (star z).re = blockPosition p n + 3 / 2 := by
        simpa only [Complex.star_def, Complex.conj_re] using hre
      have histar : Real.pi / 2 - 1 / 32 < (star z).im := by
        simpa only [Complex.star_def, Complex.conj_im,
          abs_of_neg (lt_of_not_ge hsign)] using hend
      have hb := hupper hstar hrstar histar
      rw [G.symmetric_map z hz] at hb
      simpa only [Complex.star_def, Complex.conj_re] using hb.trans (le_max_right _ _)

/-- Forward locally uniform convergence on the limiting tract gives an
eventual common real-part bound on every fixed clean slice. -/
theorem eventually_clean_gap_slice_bound {ι : Type u} {l : Filter ι}
    (p : BlockParameters) (δ : ι → GateIndex → ℝ) (δ₀ : GateIndex → ℝ)
    (hδ : ∀ i j, δ i j ≤ gateUpper j) (G : ∀ i, LogModel (tract p (δ i)))
    (G₀ : LogModel (tract p δ₀))
    (hlim : TendstoLocallyUniformlyOn (fun i => (G i).toFun) G₀.toFun l (tract p δ₀))
    (n : ℕ) :
    ∃ C : ℝ, ∀ᶠ i in l, ∀ z ∈ tract p (δ i),
      z.re = blockPosition p n + 3 / 2 → ((G i).toFun z).re ≤ C := by
  let q : ℝ → ℂ := fun s => cleanGapUpperChart p n ((s : ℂ) + Complex.I)
  have hq (s : ℝ) (hs : s = -1 ∨ s = 0 ∨ s = 1) : q s ∈ tract p δ₀ := by
    apply clean_gap_upper_chart_mapsTo p δ₀ n
    exact tangent_disk_subset_upperHalfDisc hs (mem_ball_self (by norm_num))
  let b : ℝ → ℝ := fun s => ‖targetMajorant (G₀.toFun (q s))‖
  let A : ℝ := b (-1) + b 0 + b 1 + 1
  have hbn (s : ℝ) : 0 ≤ b s := norm_nonneg _
  have hcenter (s : ℝ) (hs : s = -1 ∨ s = 0 ∨ s = 1) :
      ∀ᶠ i in l, ‖targetMajorant ((G i).toFun (q s))‖ < b s + 1 := by
    have ht := ((continuousAt_targetMajorant (G₀.mapsTo (hq s hs))).tendsto.comp
      (hlim.tendsto_at (hq s hs))).norm
    exact ht.eventually (eventually_lt_nhds (by dsimp [b]; linarith))
  have hA : ∀ᶠ i in l, ∀ s : ℝ, s = -1 ∨ s = 0 ∨ s = 1 →
      ‖targetMajorant ((G i).toFun (q s))‖ ≤ A := by
    filter_upwards [hcenter (-1) (Or.inl rfl), hcenter 0 (Or.inr (Or.inl rfl)),
      hcenter 1 (Or.inr (Or.inr rfl))] with i hi₁ hi₀ hi₂ s hs
    rcases hs with rfl | rfl | rfl <;> dsimp [A] <;>
      linarith [hbn (-1), hbn 0, hbn 1]
  let r : ℝ := Real.pi / 2 - 1 / 32
  let T : ℝ → ℂ := fun t => ((blockPosition p n + 3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let K : Set ℂ := T '' Icc (-r) r
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hK : IsCompact K := isCompact_Icc.image hT
  have hKT : ∀ t : ℝ, (T t).re = blockPosition p n + 3 / 2 ∧ (T t).im = t := by
    intro t
    simp [T]
  have hKsub : K ⊆ tract p δ₀ := by
    rintro _ ⟨t, ht, rfl⟩
    apply clean_gap_mem_tract p δ₀ n
    · rw [(hKT t).1]; linarith
    · rw [(hKT t).1]; linarith
    · rw [(hKT t).2]
      have ht' : |t| ≤ r := abs_le.mpr ht
      dsimp [r] at ht'
      linarith
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn
    ((G₀.holomorphic.continuousOn.mono hKsub).norm)).bddAbove
  have hu : TendstoUniformlyOn (fun i => (G i).toFun) G₀.toFun l K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hlim.mono hKsub)
  have hmiddle : ∀ᶠ i in l, ∀ z : ℂ, z.re = blockPosition p n + 3 / 2 →
      |z.im| ≤ r → ((G i).toFun z).re ≤ B + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num)] with i hi z hzr hzi
    have heq : T z.im = z := by
      apply Complex.ext
      · simpa only [(hKT z.im).1] using hzr.symm
      · exact (hKT z.im).2
    have hzK : z ∈ K := ⟨z.im, abs_le.mp hzi, heq⟩
    have hzB : ‖G₀.toFun z‖ ≤ B := hB ⟨z, hzK, rfl⟩
    have hdist : ‖(G i).toFun z - G₀.toFun z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hi z hzK
    have hn := norm_le_norm_sub_add ((G i).toFun z) (G₀.toFun z)
    have hr := Complex.re_le_norm ((G i).toFun z)
    linarith
  refine ⟨max (B + 1) (16 * (1 + A)), ?_⟩
  filter_upwards [hA, hmiddle] with i hiA hiB z hz hzr
  exact clean_gap_slice_re_bound p (δ i) (hδ i) n (G i) hiA hiB hz hzr

#print axioms continuousAt_targetMajorant
#print axioms clean_gap_slice_re_bound
#print axioms eventually_clean_gap_slice_bound

end MaxModulusPoints.ParameterApproximation
