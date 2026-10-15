import OAI.Analysis.SymmetricDomains.MontelExpandingDomains
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Challenge
import MaxModulusPoints.ParameterApproximation.DiskBounds
import MaxModulusPoints.ParameterApproximation.SliceBounds
import MaxModulusPoints.ParameterApproximation.Uniqueness
import MaxModulusPoints.TractGeometry.BlockPositions
/-!
# Normality of entire approximants

Real-part bounds on clean logarithmic slices give common bounds on every
fixed planar disk. Montel's theorem for eventual local bounds then produces
an entire locally uniform subsequential limit.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Metric Topology Blueprint TractGeometry

universe u

/-- Forward convergence of tract maps bounds their entire approximants
eventually on every fixed planar disk. -/
theorem eventually_approximants_bounded_on_disks {ι : Type u} {l : Filter ι}
    (p : BlockParameters) (δ : ι → GateIndex → ℝ) (δ₀ : GateIndex → ℝ)
    (hδ : ∀ i j, δ i j ≤ gateUpper j) (G : ∀ i, LogModel (tract p (δ i)))
    (G₀ : LogModel (tract p δ₀)) (F : ι → ℂ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i, Entire (F i))
    (hb : ∀ i, ApproximationBounds (tract p (δ i)) (G i).toFun M (F i))
    (hlim : TendstoLocallyUniformlyOn (fun i => (G i).toFun) G₀.toFun l (tract p δ₀))
    (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in l, ∀ w : ℂ, ‖w‖ ≤ R → ‖F i w‖ ≤ C := by
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hb0 : 1 ≤ blockPosition p 0 := by
    simpa [blockPosition] using p.gap_ge_one 0
  have hg := blockPosition_growth p (Nat.zero_le n)
  simp only [Nat.cast_zero, sub_zero] at hg
  have hRpos : 0 < blockPosition p n + 3 / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hR : R ≤ Real.exp (blockPosition p n + 3 / 2) := by
    have he := Real.add_one_le_exp (blockPosition p n + 3 / 2)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨C, hC⟩ := eventually_clean_gap_slice_bound p δ δ₀ hδ G G₀ hlim n
  have hbound := eventually_disk_bound_of_slice_bound hF hb hM hRpos hC
  refine ⟨Real.exp C + M, by positivity, ?_⟩
  filter_upwards [hbound] with i hi w hw
  exact hi w (hw.trans hR)

/-- A sequence of entire approximants with forward-convergent tract maps
has an entire locally uniform subsequential limit. -/
theorem approximants_subsequence (p : BlockParameters) (δ : ℕ → GateIndex → ℝ)
    (δ₀ : GateIndex → ℝ) (hδ : ∀ i j, δ i j ≤ gateUpper j)
    (G : ∀ i, LogModel (tract p (δ i))) (G₀ : LogModel (tract p δ₀))
    (F : ℕ → ℂ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hF : ∀ i, Entire (F i))
    (hb : ∀ i, ApproximationBounds (tract p (δ i)) (G i).toFun M (F i))
    (hlim : TendstoLocallyUniformlyOn (fun i => (G i).toFun) G₀.toFun atTop (tract p δ₀)) :
    ∃ f : ℂ → ℂ, Entire f ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun i => F (φ i)) f atTop := by
  have hlocal : ∀ x ∈ (univ : Set ℂ), ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ball x r ⊆ univ ∧ ∀ᶠ i in atTop,
        DifferentiableOn ℂ (F i) (ball x r) ∧ ∀ y ∈ ball x r, ‖F i y‖ ≤ C := by
    intro x _
    obtain ⟨C, hCpos, hC⟩ :=
      eventually_approximants_bounded_on_disks p δ δ₀ hδ G G₀ F hM hF hb hlim (‖x‖ + 1)
    refine ⟨1, by norm_num, C, hCpos, subset_univ _, ?_⟩
    filter_upwards [hC] with i hi
    refine ⟨(hF i).differentiableOn, ?_⟩
    intro y hy
    apply hi y
    have hn := norm_le_norm_sub_add y x
    have hd : ‖y - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hy
    linarith
  obtain ⟨f, hf, φ, hφ, hconv⟩ :=
    OAI.Release061.montel_expanding_domains isOpen_univ F hlocal
  exact ⟨f, differentiableOn_univ.mp hf, φ, hφ, tendstoLocallyUniformlyOn_univ.mp hconv⟩

#print axioms eventually_approximants_bounded_on_disks
#print axioms approximants_subsequence

end MaxModulusPoints.ParameterApproximation
