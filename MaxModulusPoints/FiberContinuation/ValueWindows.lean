import Mathlib.Analysis.Complex.Polynomial.Basic
import MaxModulusPoints.FiberContinuation.SphericalCharts
import MaxModulusPoints.FiberContinuation.ValueCoordinates
/-!
# Matched spherical value windows

The image of a centered parameter disk is an open spherical neighborhood.
Matching its radius with a positive integral power ensures that every parameter
root over the window lies inside the same disk.
-/

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Metric

theorem infiniteValue_image_ball {r : ℝ} (hr : 0 < r) :
    infiniteValue '' ball (0 : ℂ) r =
      (((↑) : ℂ → OnePoint ℂ) '' closedBall (0 : ℂ) r⁻¹)ᶜ := by
  have hmem (q : ℂ) : (q : OnePoint ℂ) ∈ infiniteValue '' ball (0 : ℂ) r ↔
      q ≠ 0 ∧ ‖q⁻¹‖ < r := by
    constructor
    · rintro ⟨t, ht, heq⟩
      have ht0 : t ≠ 0 := by
        intro hzero
        simp [infiniteValue, hzero] at heq
      have hinv : t⁻¹ = q := OnePoint.coe_injective
        (by simpa [infiniteValue, ht0] using heq)
      have htq : t = q⁻¹ := by rw [← hinv, inv_inv]
      exact ⟨hinv ▸ inv_ne_zero ht0, by simpa [htq] using ht⟩
    · rintro ⟨hq, hnorm⟩
      exact ⟨q⁻¹, by simpa using hnorm, by simp [infiniteValue, inv_ne_zero hq]⟩
  ext p
  cases p using OnePoint.rec with
  | infty =>
    constructor
    · intro _
      exact OnePoint.infty_notMem_image_coe
    · intro _
      exact ⟨0, mem_ball_self hr, infiniteValue_zero⟩
  | coe q =>
    have hright : (q : OnePoint ℂ) ∉ ((↑) : ℂ → OnePoint ℂ) '' closedBall (0 : ℂ) r⁻¹ ↔
        r⁻¹ < ‖q‖ := by
      simp only [mem_image, OnePoint.coe_eq_coe, exists_eq_right, mem_closedBall, dist_zero_right, not_le]
    rw [hmem]
    change (q ≠ 0 ∧ ‖q⁻¹‖ < r) ↔
      (q : OnePoint ℂ) ∉ ((↑) : ℂ → OnePoint ℂ) '' closedBall (0 : ℂ) r⁻¹
    rw [hright]
    constructor
    · rintro ⟨hq, hnorm⟩
      exact (inv_lt_comm₀ (norm_pos_iff.mpr hq) hr).mp (by simpa using hnorm)
    · intro hnorm
      have hqpos : 0 < ‖q‖ := (inv_pos.mpr hr).trans hnorm
      exact ⟨norm_pos_iff.mp hqpos, by
        simpa using (inv_lt_comm₀ hqpos hr).mpr hnorm⟩

theorem isOpen_centeredValue_image_ball (p : OnePoint ℂ) {r : ℝ} (hr : 0 < r) :
    IsOpen (centeredValue p '' ball (0 : ℂ) r) := by
  cases p using OnePoint.rec with
  | infty =>
    change IsOpen (infiniteValue '' ball (0 : ℂ) r)
    rw [infiniteValue_image_ball hr]
    exact OnePoint.isOpen_compl_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall _ _⟩
  | coe q =>
    change IsOpen ((fun t : ℂ => ((q + t : ℂ) : OnePoint ℂ)) '' ball (0 : ℂ) r)
    have hopen : IsOpen (((↑) : ℂ → OnePoint ℂ) '' ((q + ·) '' ball (0 : ℂ) r)) :=
      OnePoint.isOpen_image_coe.mpr (isOpenMap_add_left q _ isOpen_ball)
    simpa only [image_image, Function.comp_def] using hopen

/-- Every target in the matched value window has a parameter root in the disk. -/
theorem exists_parameter_in_matched_window (p : OnePoint ℂ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) {q : OnePoint ℂ}
    (hq : q ∈ centeredValue p '' ball (0 : ℂ) (δ ^ N)) :
    ∃ t ∈ ball (0 : ℂ) δ, centeredValue p (t ^ N) = q := by
  obtain ⟨u, hu, huq⟩ := hq
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq u hN
  refine ⟨t, ?_, by rw [ht]; exact huq⟩
  have hnorm : ‖t‖ ^ N < δ ^ N := by
    rw [← norm_pow, ht]
    simpa using hu
  have htδ := (pow_lt_pow_iff_left₀ (norm_nonneg t) hδ.le (Nat.ne_of_gt hN)).mp hnorm
  simpa using htδ

/-- Every parameter root of a target in the matched window lies in the disk. -/
theorem parameter_mem_of_matched_window (p : OnePoint ℂ) {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) {t : ℂ}
    (ht : centeredValue p (t ^ N) ∈ centeredValue p '' ball (0 : ℂ) (δ ^ N)) :
    t ∈ ball (0 : ℂ) δ := by
  obtain ⟨u, hu, heq⟩ := ht
  have hequal : u = t ^ N := centeredValue_injective p heq
  have hnorm : ‖t‖ ^ N < δ ^ N := by
    rw [← norm_pow, ← hequal]
    simpa using hu
  simpa using (pow_lt_pow_iff_left₀ (norm_nonneg t) hδ.le (Nat.ne_of_gt hN)).mp hnorm

end MaxModulusPoints.FiberContinuation
