module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.ExactCovers
public import MaxModulusPoints.FiberContinuation.LocalCounts
public import MaxModulusPoints.FiberContinuation.LocalFamilies
public import MaxModulusPoints.FiberContinuation.ParameterInverses
public import MaxModulusPoints.FiberContinuation.RegularBranches
public import MaxModulusPoints.FiberContinuation.RotatedComparisons
public import MaxModulusPoints.FiberContinuation.ValueCoordinates
public import MaxModulusPoints.FiberContinuation.ValueWindows

/-!
# Stabilized exact covers with actual physical counts

Shrink the matched cover until rotated product comparisons and physical
equality kernels stabilize. The whole window stays away from zero products
and the omitted value, and every punctured branch has a constant actual count.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

structure StabilizedCover {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    (C : CommonPowerFamily d s p) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ C.radius
  window : Set (ℂ × OnePoint ℂ)
  open_window : IsOpen window
  center_mem : (s, p) ∈ window
  neighborhood_subset : window ⊆ C.neighborhood
  value_window : window ⊆ Prod.snd ⁻¹' (centeredValue p '' ball (0 : ℂ) (radius ^ C.exponent))
  admissible : ∀ y ∈ window, y.1 ≠ 0 ∧ y.2 ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)
  analytic_pair : ∀ i, AnalyticOnNhd ℂ (C.pair i) (ball 0 radius)
  rotated_stability : C.RotatedProductStability radius
  exact_image : actualTargets d ∩ window = ⋃ i, C.rawTarget i '' ball 0 radius
  count_stable : ∀ i t u, t ∈ ball 0 radius → t ≠ 0 → u ∈ ball 0 radius → u ≠ 0 →
    (physicalFiber d (C.productFunction i t) (centeredValue p (t ^ C.exponent))).encard =
      (physicalFiber d (C.productFunction i u) (centeredValue p (u ^ C.exponent))).encard

namespace CommonPowerFamily

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    (C : CommonPowerFamily d s p)

theorem exists_stabilized_cover (hs : s ≠ 0)
    (hp : p ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)) : Nonempty (StabilizedCover C) := by
  letI := C.finite_index
  obtain ⟨δP, hδP, hcount⟩ := analytic_physical_counts_stabilize C.pair C.analytic_pair
  obtain ⟨δR, hδR, hrotated⟩ := C.exists_rotated_product_stability
  have hproducts : ∀ i, ∀ᶠ t in 𝓝 (0 : ℂ), C.productFunction i t ≠ 0 := by
    intro i
    have hcenter : C.productFunction i 0 ≠ 0 := by rw [C.productFunction_zero]; exact hs
    exact (C.analyticAt_productFunction i).continuousAt.eventually (isOpen_ne.mem_nhds hcenter)
  have hvalues : ∀ᶠ t in 𝓝 (0 : ℂ),
      centeredValue p (t ^ C.exponent) ≠ ((d.multiplicity : ℂ) : OnePoint ℂ) := by
    have hcenter : centeredValue p ((0 : ℂ) ^ C.exponent) ≠
        ((d.multiplicity : ℂ) : OnePoint ℂ) := by simpa [C.exponent_pos.ne'] using hp
    exact ((continuous_centeredValue p).comp (continuous_id.pow C.exponent)).continuousAt.eventually
      (isOpen_ne.mem_nhds hcenter)
  have hgood : ∀ᶠ t in 𝓝 (0 : ℂ), (∀ i, C.productFunction i t ≠ 0) ∧
      centeredValue p (t ^ C.exponent) ≠ ((d.multiplicity : ℂ) : OnePoint ℂ) :=
    (eventually_all.mpr hproducts).and hvalues
  obtain ⟨δG, hδG, hgoodball⟩ := nhds_basis_ball.eventually_iff.mp hgood
  let r : ℝ := min δP (min δR δG)
  have hr : 0 < r := lt_min hδP (lt_min hδR hδG)
  obtain ⟨δ, W₀, hδ, hδr, hδC, hW₀, hcenter₀, hsub₀, hanalytic, hcover₀⟩ :=
    C.exists_exact_local_image_cover hr
  have hδP' : δ ≤ δP := hδr.trans (min_le_left _ _)
  have hδR' : δ ≤ δR := hδr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδG' : δ ≤ δG := hδr.trans ((min_le_right _ _).trans (min_le_right _ _))
  let Ω : Set (ℂ × OnePoint ℂ) := {y | y.1 ≠ 0 ∧ y.2 ≠ ((d.multiplicity : ℂ) : OnePoint ℂ)}
  have hΩ : IsOpen Ω :=
    (isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)
  let V : Set (ℂ × OnePoint ℂ) :=
    Prod.snd ⁻¹' (centeredValue p '' ball (0 : ℂ) (δ ^ C.exponent))
  have hV : IsOpen V :=
    (isOpen_centeredValue_image_ball p (pow_pos hδ _)).preimage continuous_snd
  let W : Set (ℂ × OnePoint ℂ) := (W₀ ∩ Ω) ∩ V
  have hrawW₀ (i : C.index) (t : ℂ) (ht : t ∈ ball 0 δ) : C.rawTarget i t ∈ W₀ := by
    have hmem : C.rawTarget i t ∈ actualTargets d ∩ W₀ := by
      rw [hcover₀]
      exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
    exact hmem.2
  have hrawV (i : C.index) (t : ℂ) (ht : t ∈ ball 0 δ) : C.rawTarget i t ∈ V := by
    refine ⟨t ^ C.exponent, ?_, rfl⟩
    have htδ : ‖t‖ < δ := by simpa using ht
    have hpower := (pow_lt_pow_iff_left₀ (norm_nonneg t) hδ.le C.exponent_pos.ne').mpr htδ
    simpa only [mem_ball, dist_zero_right, norm_pow] using hpower
  have hcover : actualTargets d ∩ W = ⋃ i, C.rawTarget i '' ball 0 δ := by
    ext y
    constructor
    · rintro ⟨hy, hyW⟩
      have hmem : y ∈ actualTargets d ∩ W₀ := ⟨hy, hyW.1.1⟩
      rwa [hcover₀] at hmem
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      obtain ⟨t, ht, rfl⟩ := hi
      have hmem : C.rawTarget i t ∈ actualTargets d ∩ W₀ := by
        rw [hcover₀]
        exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
      exact ⟨hmem.1, ⟨⟨hmem.2, (hgoodball (ball_subset_ball hδG' ht)).1 i,
        (hgoodball (ball_subset_ball hδG' ht)).2⟩, hrawV i t ht⟩⟩
  refine ⟨{
    radius := δ
    radius_pos := hδ
    radius_le := hδC
    window := W
    open_window := (hW₀.inter hΩ).inter hV
    center_mem := ⟨⟨hcenter₀, hs, hp⟩, 0, mem_ball_self (pow_pos hδ _), centeredValue_zero p⟩
    neighborhood_subset := fun _ hy => hsub₀ hy.1.1
    value_window := fun _ hy => hy.2
    admissible := fun _ hy => hy.1.2
    analytic_pair := hanalytic
    rotated_stability := hrotated.mono C hδR'
    exact_image := hcover
    count_stable := ?_ }⟩
  intro i t u ht ht0 hu hu0
  have hEt := C.physicalFiber_eq_image (ball_subset_ball hδC ht) (hsub₀ (hrawW₀ i t ht)) rfl
  have hEu := C.physicalFiber_eq_image (ball_subset_ball hδC hu) (hsub₀ (hrawW₀ i u hu)) rfl
  dsimp only [rawTarget] at hEt hEu
  rw [hEt, hEu]
  exact hcount i t u (ball_subset_ball hδP' ht) ht0 (ball_subset_ball hδP' hu) hu0

end CommonPowerFamily

namespace StabilizedCover

variable {f : ℂ → ℂ} {d : NormalizedFunction f} {s : ℂ} {p : OnePoint ℂ}
    {C : CommonPowerFamily d s p} (D : StabilizedCover C)

theorem rawTarget_mem_window (i : C.index) {t : ℂ} (ht : t ∈ ball 0 D.radius) :
    C.rawTarget i t ∈ D.window := by
  have hmem : C.rawTarget i t ∈ actualTargets d ∩ D.window := by
    rw [D.exact_image]
    exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
  exact hmem.2

theorem regular_rawTarget (i : C.index) {t : ℂ} (ht : t ∈ ball 0 D.radius) (ht0 : t ≠ 0) :
    RegularTarget d (C.productFunction i t) (finiteParameterValue p C.exponent t) := by
  have hadm := D.admissible (C.rawTarget i t) (D.rawTarget_mem_window i ht)
  have hq : finiteParameterValue p C.exponent t ≠ (d.multiplicity : ℂ) := by
    intro heq
    exact hadm.2 ((centeredValue_pow_eq_coe p C.exponent ht0).trans
      (congrArg (fun q : ℂ => (q : OnePoint ℂ)) heq))
  exact C.regularTarget_of_stabilized_family D.radius_pos D.radius_le D.analytic_pair
    D.rotated_stability D.window D.open_window D.exact_image i ht ht0 hadm.1 hq

end StabilizedCover

end MaxModulusPoints.FiberContinuation
