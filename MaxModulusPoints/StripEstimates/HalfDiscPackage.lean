import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
import MaxModulusPoints.Blueprint.Interfaces.HalfDisc
import MaxModulusPoints.Blueprint.Interfaces.HalfDiscBarriers
import MaxModulusPoints.StripEstimates.HalfDisc
/-!
# Uniform half-disc boundary decay

The rational barrier tends to zero uniformly near the midpoint of the diameter,
as required in the endpiece estimate of Pardo-Simón–Sixsmith, Proposition 4.4.
-/

open Set Filter Metric Topology InnerProductSpace
open MaxModulusPoints.StripEstimates

namespace MaxModulusPoints.Blueprint.Packages

/-- The half-disc barrier contract, with a cutoff valid at every nearby point. -/
theorem half_disc_barriers_proof : HalfDiscBarriers := by
  intro B ε hB hε
  refine ⟨min (1 / 2) (ε / (8 * B)), lt_min (by norm_num) (by positivity), ?_⟩
  intro G hG hbound hboundary z hz hznorm
  have hopen : IsOpen halfDisc :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hreal : HarmonicOnNhd (fun w => (G w).re) (upperHalfDisc 1) := by
    intro w hw
    exact (hG.analyticOnNhd hopen w hw).harmonicAt_re
  have hdiameter : ∀ p : ℂ, p.im = 0 → ‖p‖ < 1 → ∀ b : ℝ, 0 < b →
      ∀ᶠ w in 𝓝[upperHalfDisc 1] p, (G w).re < b := by
    intro p hpim hpnorm b hb
    filter_upwards [hboundary p hpnorm hpim (b / 2) (by linarith)] with w hw
    change (G w).re ≤ 0 + b / 2 at hw
    linarith
  have hbarrier := harmonic_upper_half_disc_barrier_bound hB.le hreal hbound hdiameter hz
  have hnormhalf : ‖z‖ < 1 / 2 := hznorm.trans_le (min_le_left _ _)
  have hnormε : ‖z‖ < ε / (8 * B) := hznorm.trans_le (min_le_right _ _)
  have hre : |z.re| < 1 / 2 := (Complex.abs_re_le_norm z).trans_lt hnormhalf
  have hd1 : (1 / 4 : ℝ) ≤ (1 - z.re) ^ 2 + z.im ^ 2 := by
    obtain ⟨_, hr⟩ := abs_lt.mp hre
    nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 1 / 2)]
  have hd2 : (1 / 4 : ℝ) ≤ (1 + z.re) ^ 2 + z.im ^ 2 := by
    obtain ⟨hr, _⟩ := abs_lt.mp hre
    nlinarith [sq_nonneg z.im, sq_nonneg (z.re + 1 / 2)]
  have hterm1 : z.im / ((1 - z.re) ^ 2 + z.im ^ 2) ≤ 4 * z.im := by
    calc
      z.im / ((1 - z.re) ^ 2 + z.im ^ 2) ≤ z.im / (1 / 4 : ℝ) :=
        div_le_div_of_nonneg_left hz.2.le (by norm_num) hd1
      _ = 4 * z.im := by ring
  have hterm2 : z.im / ((1 + z.re) ^ 2 + z.im ^ 2) ≤ 4 * z.im := by
    calc
      z.im / ((1 + z.re) ^ 2 + z.im ^ 2) ≤ z.im / (1 / 4 : ℝ) :=
        div_le_div_of_nonneg_left hz.2.le (by norm_num) hd2
      _ = 4 * z.im := by ring
  have hvsmall : upperHalfDiscBarrier z ≤ 8 * ‖z‖ := by
    dsimp [upperHalfDiscBarrier]
    linarith [Complex.im_le_norm z]
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 8 * B)).mp hnormε
  calc
    (G z).re ≤ B * upperHalfDiscBarrier z := hbarrier
    _ ≤ B * (8 * ‖z‖) := mul_le_mul_of_nonneg_left hvsmall hB.le
    _ ≤ ε := by nlinarith

end MaxModulusPoints.Blueprint.Packages
