module

public import Mathlib.Analysis.Real.Pi.Bounds
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.ParameterApproximation.AffineBoundary
public import MaxModulusPoints.ParameterApproximation.TargetMajorant
public import MaxModulusPoints.StripEstimates.HalfDisc
public import MaxModulusPoints.TractGeometry.BlockPositions
public import MaxModulusPoints.TractGeometry.StripContainment
public import MaxModulusPoints.TractGeometry.Walls

/-!
# Fixed half-discs at the ends of clean slices

The gap after each block contains a fixed vertical strip free of walls.
A half-disc at the upper strip boundary is therefore common to all gate
parameters, and its diameter lies outside every admissible tract.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Blueprint TractGeometry StripEstimates

/-- The open unit-width gap after a block contains the full ambient strip. -/
theorem clean_gap_mem_tract (p : BlockParameters) (δ : GateIndex → ℝ) (n : ℕ)
    {z : ℂ} (hl : blockPosition p n + 1 < z.re)
    (hr : z.re < blockPosition p n + 2) (him : |z.im| < Real.pi / 2) :
    z ∈ tract p δ := by
  have hb0 : 1 ≤ blockPosition p 0 := by
    simpa [blockPosition] using p.gap_ge_one 0
  have hb := blockPosition_growth p (Nat.zero_le n)
  simp only [Nat.cast_zero, sub_zero] at hb
  have hreal : -2 < z.re := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnwall : z ∉ walls p := by
    intro hw
    have hw' := (walls_localization p n (by linarith) hr).mp hw
    have hwr := (blockWalls_re_bounds p n hw').2
    linarith
  exact Or.inl (Or.inl ⟨⟨hreal, him⟩, hnwall⟩)

/-- A chart directed downwards from the upper endpoint of a clean slice. -/
def cleanGapUpperChart (p : BlockParameters) (n : ℕ) (z : ℂ) : ℂ :=
  ((blockPosition p n + 3 / 2 : ℝ) : ℂ) + (Real.pi / 2 : ℂ) * Complex.I +
    (-1 / 16 : ℂ) * z

/-- The radius-three upper half-disc in the chart lies in every tract. -/
theorem clean_gap_upper_chart_mapsTo (p : BlockParameters) (δ : GateIndex → ℝ) (n : ℕ) :
    MapsTo (cleanGapUpperChart p n) (upperHalfDisc 3) (tract p δ) := by
  intro z hz
  have hre : |z.re| < 3 := (Complex.abs_re_le_norm z).trans_lt hz.1
  have him : z.im < 3 := (Complex.im_le_norm z).trans_lt hz.1
  have hcoords : (cleanGapUpperChart p n z).re = blockPosition p n + 3 / 2 - z.re / 16 ∧
      (cleanGapUpperChart p n z).im = Real.pi / 2 - z.im / 16 := by
    constructor <;> simp [cleanGapUpperChart, Complex.mul_re, Complex.mul_im] <;> ring
  apply clean_gap_mem_tract p δ n
  · rw [hcoords.1]
    linarith [(abs_lt.mp hre).2]
  · rw [hcoords.1]
    linarith [(abs_lt.mp hre).1]
  · rw [hcoords.2]
    apply abs_lt.mpr
    have hpi := Real.pi_gt_three
    constructor <;> linarith [hz.2]

/-- The chart diameter lies on the outer boundary of every admissible tract. -/
theorem clean_gap_upper_chart_diameter_not_mem (p : BlockParameters)
    (δ : GateIndex → ℝ) (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ)
    {q : ℂ} (hq : q.im = 0) : cleanGapUpperChart p n q ∉ tract p δ := by
  intro hmem
  have him := tract_im_lt p δ hδ hmem
  have hcoord : (cleanGapUpperChart p n q).im = Real.pi / 2 := by
    simp [cleanGapUpperChart, Complex.mul_im, hq]
  rw [hcoord, abs_of_pos (by positivity : 0 < Real.pi / 2)] at him
  exact (lt_irrefl _ him)

/-- The affine estimate applies at the upper endpoint of each clean slice. -/
theorem clean_gap_upper_normal_bound (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (n : ℕ) (G : LogModel (tract p δ)) {A : ℝ}
    (hA : ∀ s : ℝ, s = -1 ∨ s = 0 ∨ s = 1 →
      ‖targetMajorant (G.toFun (cleanGapUpperChart p n ((s : ℂ) + Complex.I)))‖ ≤ A)
    {y : ℝ} (hy : 0 < y) (hyone : y < 1) :
    (G.toFun (cleanGapUpperChart p n ((y : ℂ) * Complex.I))).re ≤
      16 * (1 + A) * y := by
  apply logModel_affine_normal_bound G (clean_gap_upper_chart_mapsTo p δ n)
    (fun q hq _ => clean_gap_upper_chart_diameter_not_mem p δ hδ n hq) hA hy hyone

#print axioms clean_gap_mem_tract
#print axioms clean_gap_upper_chart_mapsTo
#print axioms clean_gap_upper_chart_diameter_not_mem
#print axioms clean_gap_upper_normal_bound

end MaxModulusPoints.ParameterApproximation
