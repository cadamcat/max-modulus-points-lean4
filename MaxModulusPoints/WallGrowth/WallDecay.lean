module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CauchyApproximation.TractWallContract
public import MaxModulusPoints.WallGrowth.InverseGrowth

/-!
# Uniform decay at the tract walls

Quadratic inverse growth and the logarithmic target boundary give a uniform
bound for the product of the physical modulus and the exponential conformal
function outside the interior contour.
-/


@[expose] public section

namespace MaxModulusPoints.WallGrowth

open Set Complex Blueprint CauchyApproximation

/-- The exponential conformal function decays at inverse physical modulus
on the part of every chamber and gate tract outside the interior core. -/
theorem tract_wall_decay : TractWallDecay := by
  have hA : 0 < inverseGrowthConstant := inverseGrowthConstant_pos
  refine ⟨256 * inverseGrowthConstant * Real.exp 1, by positivity, ?_⟩
  intro p δ hδ G z hz hphysical hcore
  have hx : 0 < z.re := by
    rw [Complex.norm_exp] at hphysical
    exact Real.one_lt_exp_iff.mp hphysical
  let w := G.toFun z
  let L := max 0 (Real.log |w.im|)
  have hL : 0 ≤ L := le_max_left _ _
  have hT : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hLe : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have him : |w.im| ≤ Real.exp L :=
    (Real.le_exp_log |w.im|).trans (Real.exp_le_exp.mpr (le_max_right _ _))
  have htarget := G.mapsTo hz
  change -14 * L < w.re at htarget
  change w.re ≤ 1 - 13 * L at hcore
  have hre : |w.re| ≤ 14 * L + 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnorm : ‖w‖ ≤ 16 * Real.exp L := by
    have htri := Complex.norm_le_abs_re_add_abs_im w
    linarith
  have hmax : max 2 ‖w‖ ≤ 16 * Real.exp L := max_le (by linarith) hnorm
  have hgrowth : ‖Complex.exp z‖ ≤ inverseGrowthConstant * (16 * Real.exp L) ^ 2 := by
    apply (norm_exp_le_quadratic p δ hδ G hz hx).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmax 2) hA.le
  apply (le_div_iff₀ (norm_pos_iff.mpr (Complex.exp_ne_zero z))).mpr
  change ‖Complex.exp w‖ * ‖Complex.exp z‖ ≤ _
  calc
    ‖Complex.exp w‖ * ‖Complex.exp z‖ ≤
        Real.exp w.re * (inverseGrowthConstant * (16 * Real.exp L) ^ 2) := by
      rw [Complex.norm_exp]
      exact mul_le_mul_of_nonneg_left hgrowth (Real.exp_pos _).le
    _ = 256 * inverseGrowthConstant * Real.exp (w.re + 2 * L) := by
      rw [Real.exp_add,
        show Real.exp (2 * L) = Real.exp L * Real.exp L by rw [two_mul, Real.exp_add]]
      ring
    _ ≤ 256 * inverseGrowthConstant * Real.exp 1 := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      positivity

end MaxModulusPoints.WallGrowth
