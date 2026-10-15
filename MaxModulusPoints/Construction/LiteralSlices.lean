import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Construction.ClosedChamberGeometry
import MaxModulusPoints.Construction.PassageCut
import MaxModulusPoints.Construction.SliceWindows
import MaxModulusPoints.Construction.StarredBounds
import MaxModulusPoints.Construction.StarredSegments
import MaxModulusPoints.Construction.Tract
import MaxModulusPoints.Construction.TractMembership
/-!
# Sample sections of the chamber tract

The passage and chamber slices cover the entire tract section at each
sample coordinate. Horizontal walls exclude their endpoints. Together
with the uniform endpiece estimate, this gives the circle bound outside
the fixed starred segments in Pardo-Simón–Sixsmith, Corollary 4.6.
-/

namespace MaxModulusPoints.Construction

open Set

noncomputable section

theorem fullSlice_passage (p : Blueprint.BlockParameters) (n : ℕ) :
    fullSlice (blockParametersLayout p) n none = Blueprint.passageSlice p n := by
  ext z
  change (z.re = Blueprint.slicePosition p n ∧ -passageHalfHeight < z.im ∧
    z.im < passageHalfHeight) ↔ (z.re = Blueprint.slicePosition p n ∧
      |z.im| < Blueprint.chamberBase)
  rw [abs_lt]
  rfl

theorem upper_fullSlice_subset_chamber_interior (p : Blueprint.BlockParameters)
    (i : Blueprint.GateIndex) :
    fullSlice (blockParametersLayout p) i.1 (some (false, i.2)) ⊆
      interior (Blueprint.chamber p i true) := by
  intro z hz
  rw [upper_chamber_interior]
  have hx : z.re = Blueprint.blockPosition p i.1 + 1 / 4 := hz.1
  exact ⟨by linarith, by linarith, hz.2.1, hz.2.2⟩

/-- Every point of the literal tract on a sample line lies in one
of the passage or chamber height intervals. -/
theorem literal_tract_slice_cover (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) (n : ℕ) {z : ℂ}
    (hz : z ∈ Blueprint.tract p δ) (hx : z.re = Blueprint.slicePosition p n) :
    ∃ i : SliceIndex n, z ∈ fullSlice (blockParametersLayout p) n i := by
  have hamb := tract_subset_ambient p δ hδ hz
  by_cases hp : |z.im| < Blueprint.chamberBase
  · refine ⟨none, hx, ?_, ?_⟩
    · exact (abs_lt.mp hp).1
    · exact (abs_lt.mp hp).2
  · obtain ⟨m, hmlo, hmhi⟩ := exists_chamber_height n (le_of_not_gt hp) hamb.2
    by_cases hsign : 0 ≤ z.im
    · rw [abs_of_nonneg hsign] at hmlo hmhi
      have hne : z.im ≠ chamberBottom n m := by
        intro he
        exact upper_chamber_horizontal_wall_not_mem p δ hδ ⟨n, m⟩
          (by simp [hx]) (Or.inl he) hz
      exact ⟨some (false, m), hx, lt_of_le_of_ne hmlo hne.symm, hmhi⟩
    · rw [abs_of_neg (lt_of_not_ge hsign)] at hmlo hmhi
      have hne : -z.im ≠ chamberBottom n m := by
        intro he
        have hwall := upper_chamber_horizontal_wall_not_mem p δ hδ ⟨n, m⟩
          (z := star z) (by simpa using (show |z.re - Blueprint.slicePosition p n| < 1 / 8 by simp [hx]))
          (Or.inl (by simpa using he))
        exact hwall (G.symmetric_domain z hz)
      have hlo := lt_of_le_of_ne hmlo hne.symm
      exact ⟨some (true, m), hx, by change -chamberTop n m < z.im; linarith,
        by change z.im < -chamberBottom n m; linarith⟩

theorem literal_tract_sample_section (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) (n : ℕ) :
    Blueprint.tract p δ ∩ {z | z.re = Blueprint.slicePosition p n} =
      ⋃ i : SliceIndex n, fullSlice (blockParametersLayout p) n i := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := literal_tract_slice_cover p δ hδ G n hz.1 hz.2
    exact mem_iUnion.mpr ⟨i, hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact ⟨fullSlice_subset_literal_tract p δ G n i hi, hi.1⟩

/-- Points outside all starred exponential images obey the common endpiece
ceiling, including points outside the exponential image of the tract. -/
theorem circle_outside_starred_bound (p : Blueprint.BlockParameters) (q : SliceCutoffs)
    (δ : Blueprint.GateIndex → ℝ) (hδ : ∀ i, δ i ≤ Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) {M : ℝ} (hM : 0 ≤ M) (f : ℂ → ℂ)
    (happrox : ∀ z ∈ Blueprint.tract p δ, 1 < ‖Complex.exp z‖ →
      ‖f (Complex.exp z) - Complex.exp (G.toFun z)‖ ≤ M / ‖Complex.exp z‖)
    (houtside : ∀ z, z ∉ Complex.exp '' Blueprint.tract p δ → 1 < ‖z‖ → ‖f z‖ ≤ M / ‖z‖)
    (hbound : ∀ n i, ∀ z ∈ fullSlice (blockParametersLayout p) n i \
      starSlice (blockParametersLayout p) q n i, (G.toFun z).re ≤ 1)
    (n : ℕ) {w : ℂ} (hw : ‖w‖ = Real.exp (Blueprint.slicePosition p n))
    (hstar : w ∉ ⋃ i : SliceIndex n, Complex.exp '' starSlice (blockParametersLayout p) q n i) :
    ‖f w‖ ≤ Real.exp 1 + M := by
  by_cases htract : w ∈ Complex.exp '' Blueprint.tract p δ
  · obtain ⟨z, hz, rfl⟩ := htract
    have hx : z.re = Blueprint.slicePosition p n :=
      Real.exp_injective (by simpa only [Complex.norm_exp] using hw)
    obtain ⟨i, hi⟩ := literal_tract_slice_cover p δ hδ G n hz hx
    have hnot : z ∉ starSlice (blockParametersLayout p) q n i := by
      intro hmem
      exact hstar (mem_iUnion.mpr ⟨i, mem_image_of_mem Complex.exp hmem⟩)
    exact starred_endpiece_norm_bound p q δ G hM f happrox hbound n i ⟨hi, hnot⟩
  · have hbase := (blockParametersLayout p).base_nonneg n
    change 0 ≤ Blueprint.blockPosition p n at hbase
    have hxpos : 0 < Blueprint.slicePosition p n := by dsimp [Blueprint.slicePosition]; linarith
    have hwpos : 1 < ‖w‖ := by rw [hw]; exact Real.one_lt_exp_iff.mpr hxpos
    have hquot : M / ‖w‖ ≤ M :=
      (div_le_iff₀ (by linarith : 0 < ‖w‖)).mpr (by nlinarith)
    exact (houtside w htract hwpos).trans (hquot.trans (by linarith [Real.exp_pos (1 : ℝ)]))

#print axioms literal_tract_slice_cover
#print axioms literal_tract_sample_section
#print axioms circle_outside_starred_bound

end

end MaxModulusPoints.Construction
