import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.ParameterApproximation.BoundaryControl
import MaxModulusPoints.ParameterApproximation.HalfDiscComparison
import MaxModulusPoints.ParameterApproximation.TargetMajorant
import MaxModulusPoints.StripEstimates.HalfDisc
/-!
# Bounds near an affine straight boundary segment

Inverse escape supplies the individual boundedness needed for harmonic
comparison. The resulting bound near a straight boundary segment depends
only on three fixed interior values of the conformal map.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Metric Topology Blueprint StripEstimates

/-- An affine upper half-disc inside a tract, with its diameter outside the
tract, has a normal-radius estimate controlled by three interior values. -/
theorem logModel_affine_normal_bound {V : Set ℂ} (G : LogModel V) {p a : ℂ} {A : ℝ}
    (hwindow : MapsTo (fun z : ℂ => p + a * z) (upperHalfDisc 3) V)
    (hdiameter : ∀ q : ℂ, q.im = 0 → ‖q‖ < 1 → p + a * q ∉ V)
    (hA : ∀ s : ℝ, s = -1 ∨ s = 0 ∨ s = 1 →
      ‖targetMajorant (G.toFun (p + a * ((s : ℂ) + Complex.I)))‖ ≤ A)
    {y : ℝ} (hy : 0 < y) (hyone : y < 1) :
    (G.toFun (p + a * ((y : ℂ) * Complex.I))).re ≤ 16 * (1 + A) * y := by
  let T : ℂ → ℂ := fun z => p + a * z
  have hT : Differentiable ℂ T := by
    dsimp [T]
    fun_prop
  have hsub : upperHalfDisc 1 ⊆ upperHalfDisc 3 :=
    fun _ hz => ⟨by linarith [hz.1], hz.2⟩
  have hG : DifferentiableOn ℂ (fun z => G.toFun (T z)) (upperHalfDisc 3) :=
    G.holomorphic.comp hT.differentiableOn hwindow
  have hmaps : MapsTo (fun z => G.toFun (T z)) (upperHalfDisc 3) target :=
    G.mapsTo.comp hwindow
  have hbounded : BddAbove ((fun z => (G.toFun (T z)).re) '' upperHalfDisc 1) := by
    obtain ⟨C, hC⟩ := logModel_image_norm_bound G (‖p‖ + ‖a‖)
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hnorm : ‖T z‖ ≤ ‖p‖ + ‖a‖ := by
      calc
        ‖T z‖ ≤ ‖p‖ + ‖a * z‖ := norm_add_le _ _
        _ = ‖p‖ + ‖a‖ * ‖z‖ := by rw [norm_mul]
        _ ≤ ‖p‖ + ‖a‖ := by nlinarith [norm_nonneg a, hz.1.le]
    exact (Complex.re_le_norm _).trans
      (hC (T z) (hwindow (hsub hz)) ((Complex.re_le_norm _).trans hnorm))
  have hboundary : ∀ q : ℂ, q.im = 0 → ‖q‖ < 1 → ∀ b : ℝ, 0 < b →
      ∀ᶠ z in 𝓝[upperHalfDisc 1] q, (G.toFun (T z)).re < b := by
    intro q hqim hqnorm b hb
    have hTlim : Tendsto T (𝓝[upperHalfDisc 1] q) (𝓝[V] (T q)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (hT.continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact hwindow (hsub hz)
    exact hTlim.eventually (logModel_boundary_re_upper G (hdiameter q hqim hqnorm) hb)
  exact target_map_half_disc_normal_bound hG hmaps hbounded hboundary hA hy hyone

#print axioms logModel_affine_normal_bound

end MaxModulusPoints.ParameterApproximation
