import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.CrosscutDistortion.ConformalDensity
import MaxModulusPoints.CrosscutDistortion.ProductEnergy
import MaxModulusPoints.CrosscutDistortion.TunnelSlice
/-!
# Complex-plane energy in an open tunnel

Real and imaginary coordinates identify complex Lebesgue measure on a
rectangle with the product of the restricted real Lebesgue measures.
This transfers the tunnel energy lower bound to the complex plane.
-/

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set MeasureTheory Blueprint

private theorem complex_coordinates_symm :
    (Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) =
      fun q => (q.1 : ℂ) + q.2 * Complex.I := by
  funext q
  apply Complex.ext <;> simp

/-- The inverse coordinate map preserves volume restricted to a rectangle. -/
theorem complex_rectangle_measurePreserving (A B : Set ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * Complex.I)
      ((volume.restrict A).prod (volume.restrict B))
      (volume.restrict {q : ℂ | q.re ∈ A ∧ q.im ∈ B}) := by
  have hpreimage : Complex.measurableEquivRealProd.symm ⁻¹'
      {q : ℂ | q.re ∈ A ∧ q.im ∈ B} = A ×ˢ B := by
    ext q
    simp
  have h := (Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).restrict_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding
      {q : ℂ | q.re ∈ A ∧ q.im ∈ B}
  rw [hpreimage, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  simpa only [complex_coordinates_symm] using h

/-- Integrability on a complex rectangle is equivalent to product-coordinate
integrability, with no separate measurability hypothesis on the integrand. -/
theorem complex_rectangle_integrable_iff (A B : Set ℝ) (g : ℂ → ℝ) :
    IntegrableOn g {q : ℂ | q.re ∈ A ∧ q.im ∈ B} ↔
      Integrable (fun q : ℝ × ℝ => g ((q.1 : ℂ) + q.2 * Complex.I))
        ((volume.restrict A).prod (volume.restrict B)) := by
  have hemb : MeasurableEmbedding (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * Complex.I) := by
    simpa only [complex_coordinates_symm] using
      Complex.measurableEquivRealProd.symm.measurableEmbedding
  simpa only [IntegrableOn, Function.comp_def] using
    ((complex_rectangle_measurePreserving A B).integrable_comp_emb hemb (g := g)).symm

/-- Complex integration on a rectangle agrees with the product-coordinate
integral, including when the totalized Bochner integral is zero. -/
theorem complex_rectangle_integral (A B : Set ℝ) (g : ℂ → ℝ) :
    (∫ q in {q : ℂ | q.re ∈ A ∧ q.im ∈ B}, g q) =
      ∫ q : ℝ × ℝ, g ((q.1 : ℂ) + q.2 * Complex.I)
        ∂((volume.restrict A).prod (volume.restrict B)) := by
  have hemb : MeasurableEmbedding (fun q : ℝ × ℝ => (q.1 : ℂ) + q.2 * Complex.I) := by
    simpa only [complex_coordinates_symm] using
      Complex.measurableEquivRealProd.symm.measurableEmbedding
  exact ((complex_rectangle_measurePreserving A B).integral_comp hemb g).symm

/-- The tunnel rectangle with all four edges omitted. -/
def openTunnel (p : BlockParameters) (n : ℕ) : Set ℂ :=
  {q : ℂ | q.re ∈ Ioo (blockPosition p n + 1 / 2) (blockPosition p n + 1) ∧
    q.im ∈ Ioo (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2)}

theorem isOpen_openTunnel (p : BlockParameters) (n : ℕ) :
    IsOpen (openTunnel p n) := by
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)

/-- The open tunnel lies in the tract for every choice of gate widths. -/
theorem openTunnel_subset_tract (p : BlockParameters) (δ : GateIndex → ℝ) (n : ℕ) :
    openTunnel p n ⊆ tract p δ := by
  intro q hq
  have hcomponent := tunnel_vertical_component p δ n q.re hq.1
  have hqcomponent : q ∈ connectedComponentIn
      (tract p δ ∩ {v : ℂ | v.re = q.re}) (q.re : ℂ) := by
    rw [hcomponent]
    exact ⟨rfl, abs_lt.mpr ⟨by linarith [hq.2.1], hq.2.2⟩⟩
  exact (connectedComponentIn_subset _ _ hqcomponent).1

/-- The complex-plane squared conformal density has energy at least the
reciprocal tunnel aspect ratio, assuming its integrability on the tunnel. -/
theorem tunnel_complex_energy_lower_bound (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0) (n : ℕ)
    (w z : ℂ) (hw : w ∈ passageSlice p n) (hz : z ∈ cleanSlice p n)
    (hwV : w ∈ tract p δ) (hzV : z ∈ tract p δ)
    (hsquare : IntegrableOn (fun q : ℂ =>
      (slabPullbackDensity (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        φ.toFun q) ^ 2) (openTunnel p n)) :
    1 / (2 * p.tunnelHeight n) ≤ ∫ q in openTunnel p n,
      (slabPullbackDensity (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        φ.toFun q) ^ 2 := by
  have hproduct := (complex_rectangle_integrable_iff
    (Ioo (blockPosition p n + 1 / 2) (blockPosition p n + 1))
    (Ioo (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2)) _).mp hsquare
  rw [openTunnel, complex_rectangle_integral]
  exact tunnel_product_energy_lower_bound p δ φ hφ0 hφre hφim n w z hw hz hwV hzV hproduct

end MaxModulusPoints.CrosscutDistortion
