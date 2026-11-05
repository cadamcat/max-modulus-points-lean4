module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.CoreIntersection
public import MaxModulusPoints.CrosscutDistortion.HalfCurveLength
public import MaxModulusPoints.CrosscutDistortion.PotentialSpeed
public import MaxModulusPoints.CrosscutDistortion.SlabPotentials
public import MaxModulusPoints.CrosscutDistortion.TractSymmetry
public import MaxModulusPoints.CrosscutDistortion.TunnelBoundary
public import MaxModulusPoints.CrosscutDistortion.TunnelSlice

/-!
# Weighted lengths of tunnel half-crosscuts

Both halves of an interior tunnel crosscut meet the target slab core by
reflection symmetry. Holomorphy and escape at the excluded endpoints give
the hypotheses of the half-curve length estimate.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set Filter MeasureTheory Blueprint
open scoped Topology

/-- Either signed tunnel half-crosscut has slab-weighted length at least
one half, whenever its weighted speed is integrable. -/
theorem tunnel_half_weighted_length (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    (w z : ℂ) (hw : w ∈ passageSlice p n) (hz : z ∈ cleanSlice p n)
    (hwV : w ∈ tract p δ) (hzV : z ∈ tract p δ)
    (ε : ℝ) (hε : |ε| = 1)
    (hspeed : IntervalIntegrable
      (slabWeightedSpeed (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        (fun t : ℝ => φ.toFun ((s : ℂ) + (ε * t : ℝ) * Complex.I)))
      volume 0 (p.tunnelHeight n / 2)) :
    1 / 2 ≤ ∫ t in 0..(p.tunnelHeight n / 2),
      slabWeightedSpeed (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        (fun u : ℝ => φ.toFun ((s : ℂ) + (ε * u : ℝ) * Complex.I)) t := by
  let H : ℝ := p.tunnelHeight n / 2
  let a : ℝ := (φ.toFun w).re
  let b : ℝ := max a (φ.toFun z).re
  let f : ℝ → ℂ := fun t => (s : ℂ) + (ε * t : ℝ) * Complex.I
  have hH : 0 < H := half_pos (p.tunnel_pos n)
  have hcomponent := tunnel_vertical_component p δ n s hs
  have hsub : {q : ℂ | q.re = s ∧ |q.im| < H} ⊆ tract p δ := by
    intro q hq
    have hq' : q ∈ connectedComponentIn (tract p δ ∩ {q : ℂ | q.re = s})
        (s : ℂ) := by
      rw [hcomponent]
      exact hq
    exact (connectedComponentIn_subset _ _ hq').1
  have hsource (t : ℝ) (ht : t ∈ Ico (0 : ℝ) H) : f t ∈ tract p δ := by
    apply hsub
    constructor
    · simp [f]
    · simpa only [f, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, zero_add, add_zero,
        abs_mul, hε, one_mul, abs_of_nonneg ht.1] using ht.2
  have hsym := tract_strip_equivalence_conj p δ φ hφ0 hφre hφim
  have hreal : (φ.toFun (f 0)).im = 0 := by
    have hr := congrArg Complex.im (hsym (f 0) (hsource 0 ⟨le_rfl, hH⟩))
    have hstar : star (f 0) = f 0 := by simp [f]
    rw [hstar] at hr
    simp only [Complex.star_def, Complex.conj_im] at hr
    linarith
  have hcore : ∃ c ∈ Ico (0 : ℝ) H,
      (φ.toFun (f c)).re ∈ Icc a b ∧ |(φ.toFun (f c)).im| ≤ 1 / 2 := by
    obtain ⟨q, hqre, hqim, hqcore⟩ :=
      tunnel_image_meets_real_core p δ φ hφ0 hφre hφim n s hs w z hw hz hwV hzV
    have hqV : q ∈ tract p δ := hsub ⟨hqre, hqim⟩
    refine ⟨|q.im|, ⟨abs_nonneg _, hqim⟩, ?_, ?_⟩
    · have habs : |ε * (|q.im|)| = |q.im| := by rw [abs_mul, hε, one_mul, abs_abs]
      rcases abs_eq_abs.mp habs with heq | heq
      · have hfq : f |q.im| = q := by
          apply Complex.ext <;> simp [f, hqre, heq]
        simpa only [hfq] using hqcore
      · have hfq : f |q.im| = star q := by
          apply Complex.ext <;> simp [f, hqre, heq]
        rw [hfq, hsym q hqV]
        simpa only [Complex.star_def, Complex.conj_re] using hqcore
    · exact (φ.mapsTo (hsource |q.im| ⟨abs_nonneg _, hqim⟩)).le
  have hSo : IsOpen strip := isOpen_lt Complex.continuous_im.abs continuous_const
  have h0S : (0 : ℂ) ∈ strip := by norm_num [strip]
  have h1S : (1 : ℂ) ∈ strip := by norm_num [strip]
  have hconv : Convex ℝ strip := by
    simpa only [strip, abs_lt, ofPred_and] using
      (convex_halfSpace_im_gt (-(1 / 2 : ℝ))).inter
        (convex_halfSpace_im_lt (1 / 2 : ℝ))
  have hnonconstant : ¬ ∃ c : ℂ, ∀ q ∈ strip, φ.invFun q = c := by
    rintro ⟨c, hc⟩
    have hh := congrArg φ.toFun ((hc 0 h0S).trans (hc 1 h1S).symm)
    simp only [φ.right_inv 0 h0S, φ.right_inv 1 h1S] at hh
    exact zero_ne_one hh
  have hopen := ((φ.inverse_holomorphic.analyticOnNhd hSo).is_constant_or_isOpen
    hconv.isPreconnected).resolve_left hnonconstant
  have himage : φ.invFun '' strip = tract p δ := by
    apply subset_antisymm
    · rintro q ⟨v, hv, rfl⟩
      exact φ.inverse_mapsTo hv
    · intro q hq
      exact ⟨φ.toFun q, φ.mapsTo hq, φ.left_inv q hq⟩
  have hUo : IsOpen (tract p δ) := by
    rw [← himage]
    exact hopen strip subset_rfl hSo
  have hφC1 : ContDiffOn ℝ 1 φ.toFun (tract p δ) :=
    (φ.holomorphic.contDiffOn hUo).restrict_scalars ℝ
  have hf : ContDiff ℝ 1 f := by
    dsimp [f]
    exact contDiff_const.add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)
  have hC1 (d : ℝ) (hd : d ∈ Ico (0 : ℝ) H) :
      ContDiffOn ℝ 1 (fun t => φ.toFun (f t)) (uIcc 0 d) := by
    apply hφC1.comp hf.contDiffOn
    intro t ht
    rw [uIcc_of_le hd.1] at ht
    exact hsource t ⟨ht.1, ht.2.trans_lt hd.2⟩
  have hendpoint : f H ∉ tract p δ :=
    (tunnel_endpoints_frontier p δ n s hs (f H) (by simp [f])
      (by simpa only [f, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, zero_add, add_zero,
        abs_mul, hε, one_mul, abs_of_pos hH] using
        (show H = p.tunnelHeight n / 2 from rfl))).2
  have hroof : Tendsto (fun t => slabRoofPotential a b (φ.toFun (f t)))
      (𝓝[<] H) (𝓝 0) := by
    apply slab_roof_tendsto_zero (tract p δ) φ f (f H) ?_ hendpoint
      (hf.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) a b
    filter_upwards [Ico_mem_nhdsLT hH] with t ht using hsource t ht
  exact half_curve_weighted_length a b H hH (fun t => φ.toFun (f t)) hC1 hspeed
    hreal hroof hcore

end MaxModulusPoints.CrosscutDistortion
