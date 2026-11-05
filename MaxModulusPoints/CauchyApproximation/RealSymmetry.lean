module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.MeasureTheory.Group.Integral
public import MaxModulusPoints.CauchyApproximation.CanonicalApproximation
public import MaxModulusPoints.CauchyApproximation.CanonicalDensity
public import MaxModulusPoints.CauchyApproximation.ImproperIntegral
public import MaxModulusPoints.CauchyApproximation.Model

/-!
# Real symmetry of the canonical approximation

Reality of the conformal map on the real axis implies its conjugation
symmetry by the identity principle. The canonical contour reverses under
conjugation, so its Cauchy transform is real symmetric. Uniqueness of the
entire extension gives the same symmetry everywhere.
-/


@[expose] public section

open Complex ComplexConjugate Filter MeasureTheory Set
open scoped Topology

namespace MaxModulusPoints.CauchyApproximation

/-- The reality assumption on real points determines conjugation symmetry
of the conformal map on its entire domain. -/
theorem NormalizedModel.forward_conj (m : NormalizedModel) (hs : m.IsRealSymmetric)
    {z : ℂ} (hz : z ∈ m.domain) : m.forward (conj z) = conj (m.forward z) := by
  let F : ℂ → ℂ := conj ∘ m.forward ∘ conj
  have hF : DifferentiableOn ℂ F m.domain := by
    intro w hw
    have hf := m.holomorphic_forward.differentiableAt
      (m.isOpen_domain.mem_nhds (hs.1 w hw))
    simpa only [F, conj_conj, Function.comp_def] using
      hf.conj_conj.differentiableWithinAt
  let a : ℝ := Real.exp (-1)
  have ha : (a : ℂ) ∈ m.domain := by
    simpa only [a, ofReal_exp, ofReal_neg, ofReal_one] using m.base_mem
  have hreal : ∀ᶠ x : ℝ in 𝓝[≠] a, m.forward (x : ℂ) = F x := by
    have hmem : ∀ᶠ x : ℝ in 𝓝 a, (x : ℂ) ∈ m.domain :=
      continuous_ofReal.continuousAt (m.isOpen_domain.mem_nhds ha)
    filter_upwards [nhdsWithin_le_nhds hmem] with x hx
    simpa only [F, Function.comp_def, conj_ofReal] using
      (conj_eq_iff_im.2 (hs.2 x hx)).symm
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] (a : ℂ), m.forward w = F w :=
    (continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
      (fun _ hx ↦ by simpa only [mem_compl_iff, mem_singleton_iff, ofReal_inj] using hx)).frequently
      hreal.frequently
  have heq := (m.holomorphic_forward.analyticOnNhd m.isOpen_domain).eqOn_of_preconnected_of_frequently_eq
      (hF.analyticOnNhd m.isOpen_domain)
      m.simplyConnected_domain.isPathConnected.isConnected.isPreconnected ha hfreq
  simpa only [F, Function.comp_def, conj_conj] using heq (hs.1 z hz)

/-- The inverse conformal map respects conjugation on the fixed image domain. -/
theorem NormalizedModel.inverse_conj (m : NormalizedModel) (hs : m.IsRealSymmetric)
    {w : ℂ} (hw : w ∈ modelHalfPlane) : m.inverse (conj w) = conj (m.inverse w) := by
  have hi : m.inverse w ∈ m.domain := m.inverse_mem hw
  have hf : m.forward (conj (m.inverse w)) = conj w := by
    rw [m.forward_conj hs hi, m.right_inverse w hw]
  rw [← hf, m.left_inverse _ (hs.1 _ hi)]

/-- The exponential conformal model has the same real symmetry. -/
theorem NormalizedModel.modelFunction_conj (m : NormalizedModel) (hs : m.IsRealSymmetric)
    {z : ℂ} (hz : z ∈ m.domain) :
    m.modelFunction (conj z) = conj (m.modelFunction z) := by
  simp only [NormalizedModel.modelFunction, m.forward_conj hs hz, exp_conj]

/-- Conjugation reverses the fixed image curve. -/
theorem imageContour_neg (t : ℝ) : imageContour (-t) = conj (imageContour t) := by
  apply Complex.ext <;> simp [imageContour, abs_neg]

/-- Conjugation reverses the actual interior contour. -/
theorem NormalizedModel.contour_neg (m : NormalizedModel) (hs : m.IsRealSymmetric)
    (t : ℝ) : m.contour (-t) = conj (m.contour t) := by
  change m.inverse (imageContour (-t)) = conj (m.inverse (imageContour t))
  rw [imageContour_neg, m.inverse_conj hs (imageContour_mem_modelHalfPlane t)]

/-- The total real derivative also reverses under conjugation, including at
the two corners of the image curve. -/
theorem NormalizedModel.deriv_contour_neg (m : NormalizedModel) (hs : m.IsRealSymmetric)
    (t : ℝ) : deriv m.contour (-t) = -conj (deriv m.contour t) := by
  have heq : (fun u : ℝ ↦ m.contour (-u)) = fun u ↦ conj (m.contour u) :=
    funext (m.contour_neg hs)
  have hd := congrArg (fun f : ℝ → ℂ ↦ deriv f t) heq
  rw [deriv_comp_neg] at hd
  change -deriv m.contour (-t) = deriv (fun u : ℝ ↦ star (m.contour u)) t at hd
  rw [deriv.star] at hd
  simpa only [neg_neg, starRingEnd_apply] using congrArg Neg.neg hd

/-- The actual Cauchy density acquires the orientation sign under conjugation. -/
theorem NormalizedModel.density_neg (m : NormalizedModel) (hs : m.IsRealSymmetric)
    (t : ℝ) : m.density (-t) = -conj (m.density t) := by
  have ht : m.contour t ∈ m.domain := m.inverse_mem (imageContour_mem_modelHalfPlane t)
  simp only [NormalizedModel.density, m.contour_neg hs, m.modelFunction_conj hs ht,
    m.deriv_contour_neg hs, mul_neg, map_mul]

/-- The improper Cauchy transform is real symmetric. -/
theorem NormalizedModel.cauchyIntegral_conj (m : NormalizedModel) (hs : m.IsRealSymmetric)
    (z : ℂ) :
    cauchyIntegral m.contour m.density (conj z) =
      conj (cauchyIntegral m.contour m.density z) := by
  have hk (t : ℝ) : m.density (-t) / (m.contour (-t) - conj z) =
      -conj (m.density t / (m.contour t - z)) := by
    rw [m.density_neg hs, m.contour_neg hs, neg_div, map_div₀, map_sub]
  unfold cauchyIntegral
  rw [← integral_neg_eq_self (fun t : ℝ ↦ m.density t / (m.contour t - conj z)) volume]
  simp_rw [hk]
  rw [integral_neg, integral_conj, map_mul]
  have htwo : conj (2 : ℂ) = (2 : ℂ) := conj_ofReal 2
  simp [htwo]

/-- The right-hand core of a symmetric tract is invariant under conjugation. -/
theorem NormalizedModel.conj_mem_core_iff (m : NormalizedModel) (hs : m.IsRealSymmetric)
    (z : ℂ) : conj z ∈ m.core ↔ z ∈ m.core := by
  have H (w : ℂ) (hw : w ∈ m.core) : conj w ∈ m.core := by
    refine ⟨hs.1 w hw.1, ?_⟩
    simpa only [m.forward_conj hs hw.1, conj_im, abs_neg, conj_re] using hw.2
  exact ⟨fun hz ↦ by simpa only [conj_conj] using H _ hz, H z⟩

/-- The contour image of a symmetric tract is invariant under conjugation. -/
theorem NormalizedModel.conj_mem_range_contour_iff (m : NormalizedModel)
    (hs : m.IsRealSymmetric) (z : ℂ) : conj z ∈ range m.contour ↔ z ∈ range m.contour := by
  have H (w : ℂ) (hw : w ∈ range m.contour) : conj w ∈ range m.contour := by
    obtain ⟨t, rfl⟩ := hw
    exact ⟨-t, m.contour_neg hs t⟩
  exact ⟨fun hz ↦ by simpa only [conj_conj] using H _ hz, H z⟩

/-- The unique entire canonical approximation is real symmetric whenever
the tract and its conformal model are real symmetric. -/
theorem NormalizedModel.canonicalEntire_conj (m : NormalizedModel) (hs : m.IsRealSymmetric)
    (z : ℂ) : m.canonicalEntire (conj z) = conj (m.canonicalEntire z) := by
  let F : ℂ → ℂ := conj ∘ m.canonicalEntire ∘ conj
  have hF : Differentiable ℂ F := by
    intro w
    simpa only [F, conj_conj] using
      (m.canonicalEntire_spec.1 (conj w)).conj_conj
  have hcanonical : IsCanonicalApproximation m F := by
    intro w hw
    have hwc : conj w ∉ range m.contour :=
      fun h ↦ hw ((m.conj_mem_range_contour_iff hs w).1 h)
    obtain ⟨hin, hout⟩ := m.canonicalEntire_spec.2 (conj w) hwc
    constructor
    · intro hcore
      have hwD : w ∈ m.domain := hcore.1
      have heq := hin ((m.conj_mem_core_iff hs w).2 hcore)
      simp only [F, Function.comp_def, heq, map_add, m.cauchyIntegral_conj hs,
        m.modelFunction_conj hs hwD, conj_conj]
    · intro hcore
      have heq := hout (fun h ↦ hcore ((m.conj_mem_core_iff hs w).1 h))
      simp only [F, Function.comp_def, heq, m.cauchyIntegral_conj hs, conj_conj]
  have heq := m.eq_canonicalEntire_of_entire_canonical hF hcanonical
  have hz := congrFun heq (conj z)
  simpa only [F, Function.comp_def, conj_conj] using hz.symm

#print axioms NormalizedModel.forward_conj
#print axioms NormalizedModel.inverse_conj
#print axioms NormalizedModel.deriv_contour_neg
#print axioms NormalizedModel.cauchyIntegral_conj
#print axioms NormalizedModel.canonicalEntire_conj

end MaxModulusPoints.CauchyApproximation
