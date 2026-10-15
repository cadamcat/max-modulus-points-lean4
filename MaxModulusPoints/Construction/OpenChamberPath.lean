import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Construction.OpenChamberGeometry
import MaxModulusPoints.Construction.Tract
/-!
# A smooth path through an open gate

A quadratic reparameterization makes the vertical and horizontal legs
meet with zero velocity. Clearance and speed bounds therefore apply
directly to the compact strip-containment estimate.
-/

namespace MaxModulusPoints.Construction

open Set Metric Filter
open scoped Topology

noncomputable section

def cornerLeft (x h t : ℝ) : ℂ :=
  (x : ℂ) + ((h * (4 * t - 4 * t ^ 2) : ℝ) : ℂ) * Complex.I

def cornerRight (x h t : ℝ) : ℂ :=
  ((x - 5 / 4 * (2 * t - 1) ^ 2 : ℝ) : ℂ) + (h : ℂ) * Complex.I

def smoothCorner (x h t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then cornerLeft x h t else cornerRight x h t

def cornerVelocity (h t : ℝ) : ℂ :=
  if t ≤ 1 / 2 then ((h * (4 - 8 * t) : ℝ) : ℂ) * Complex.I
  else ((-5 * (2 * t - 1) : ℝ) : ℂ)

theorem hasDerivAt_cornerLeft (x h t : ℝ) :
    HasDerivAt (cornerLeft x h) (((h * (4 - 8 * t) : ℝ) : ℂ) * Complex.I) t := by
  have hp : HasDerivAt (fun s : ℝ => h * (4 * s - 4 * s ^ 2)) (h * (4 - 8 * t)) t := by
    convert ((((hasDerivAt_id t).const_mul 4).sub
      (((hasDerivAt_id t).pow 2).const_mul 4)).const_mul h) using 1
    · rfl
    · dsimp; ring
  exact (hp.ofReal_comp.mul_const Complex.I).const_add (x : ℂ)

theorem hasDerivAt_cornerRight (x h t : ℝ) :
    HasDerivAt (cornerRight x h) (((-5 * (2 * t - 1) : ℝ) : ℂ)) t := by
  have hp : HasDerivAt (fun s : ℝ => x - 5 / 4 * (2 * s - 1) ^ 2)
      (-5 * (2 * t - 1)) t := by
    convert (((((hasDerivAt_id t).const_mul 2).sub_const 1).pow 2).const_mul
      (5 / 4)).const_sub x using 1
    · rfl
    · dsimp; ring
  exact hp.ofReal_comp.add_const ((h : ℂ) * Complex.I)

theorem smoothCorner_join (x h : ℝ) :
    cornerLeft x h (1 / 2) = cornerRight x h (1 / 2) := by
  norm_num [cornerLeft, cornerRight]

theorem hasDerivAt_smoothCorner (x h t : ℝ) :
    HasDerivAt (smoothCorner x h) (cornerVelocity h t) t := by
  rcases lt_trichotomy t (1 / 2) with ht | ht | ht
  · rw [cornerVelocity, ite_eq_left ht.le]
    apply (hasDerivAt_cornerLeft x h t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [smoothCorner, ite_eq_left (le_of_lt (mem_Iio.mp hs))]
  · subst t
    have hl : HasDerivAt (cornerLeft x h) 0 (1 / 2) := by
      convert hasDerivAt_cornerLeft x h (1 / 2) using 1 <;> norm_num
    have hr : HasDerivAt (cornerRight x h) 0 (1 / 2) := by
      convert hasDerivAt_cornerRight x h (1 / 2) using 1 <;> norm_num
    have hleft : HasDerivWithinAt (smoothCorner x h) 0 (Iic (1 / 2)) (1 / 2) := by
      apply hl.hasDerivWithinAt.congr_of_mem
      · intro s hs
        simp only [smoothCorner, ite_eq_left (mem_Iic.mp hs)]
      · simp
    have hright : HasDerivWithinAt (smoothCorner x h) 0 (Ici (1 / 2)) (1 / 2) := by
      apply hr.hasDerivWithinAt.congr_of_mem
      · intro s hs
        by_cases hle : s ≤ 1 / 2
        · have he : s = 1 / 2 := le_antisymm hle hs
          subst s
          simpa only [smoothCorner, ite_eq_left (le_refl (1 / 2 : ℝ))] using smoothCorner_join x h
        · simp only [smoothCorner, ite_eq_right hle]
      · simp
    have hu := hleft.union hright
    have he : Iic (1 / 2 : ℝ) ∪ Ici (1 / 2) = univ := by
      ext s
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total s (1 / 2)
    rw [he] at hu
    convert hu.hasDerivAt univ_mem using 1 <;> norm_num [cornerVelocity]
  · rw [cornerVelocity, ite_eq_right (not_le.mpr ht)]
    apply (hasDerivAt_cornerRight x h t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp only [smoothCorner, ite_eq_right (not_le.mpr (mem_Ioi.mp hs))]

theorem smoothCorner_endpoints (x h : ℝ) :
    smoothCorner x h 0 = (x : ℂ) ∧
      smoothCorner x h 1 = (⟨x - 5 / 4, h⟩ : ℂ) := by
  constructor <;> apply Complex.ext <;> norm_num [smoothCorner, cornerLeft, cornerRight]

theorem smoothCorner_left_height {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    0 ≤ 4 * t - 4 * t ^ 2 ∧ 4 * t - 4 * t ^ 2 ≤ 1 := by
  constructor
  · nlinarith [mul_nonneg ht.1 (show 0 ≤ 1 - t by linarith [ht.2])]
  · nlinarith [sq_nonneg (2 * t - 1)]

theorem smoothCorner_clearance (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex)
    (hδ : δ i = Blueprint.gateUpper i) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ball (smoothCorner (Blueprint.blockPosition p i.1 + 3 / 2) (upperChamberHeight i) t)
        (chamberClearance i.1) ⊆ Blueprint.tract p δ := by
  intro t ht
  by_cases hle : t ≤ 1 / 2
  · have hy := smoothCorner_left_height ⟨ht.1, hle⟩
    have hh := (upperChamberHeight_bounds i).1
    have hcurve : smoothCorner (Blueprint.blockPosition p i.1 + 3 / 2)
        (upperChamberHeight i) t =
        ⟨Blueprint.blockPosition p i.1 + 3 / 2,
          upperChamberHeight i * (4 * t - 4 * t ^ 2)⟩ := by
      rw [smoothCorner, ite_eq_left hle]
      apply Complex.ext <;> simp only [cornerLeft, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, zero_add, add_zero,
        mul_one, sub_zero]
    rw [hcurve]
    exact vertical_chamber_clearance p δ i
      ⟨mul_nonneg hh.le hy.1, by nlinarith [mul_le_mul_of_nonneg_left hy.2 hh.le]⟩
  · have hcurve : smoothCorner (Blueprint.blockPosition p i.1 + 3 / 2)
        (upperChamberHeight i) t =
        ⟨Blueprint.blockPosition p i.1 + 3 / 2 - 5 / 4 * (2 * t - 1) ^ 2,
          upperChamberHeight i⟩ := by
      rw [smoothCorner, ite_eq_right hle]
      apply Complex.ext <;> simp only [cornerRight, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, zero_add, add_zero,
        mul_one, sub_zero]
    rw [hcurve]
    apply horizontal_chamber_clearance p δ i hδ
    have hs : (2 * t - 1) ^ 2 ≤ 1 := by
      nlinarith [ht.2, not_le.mp hle, sq_nonneg (1 - t)]
    exact ⟨by nlinarith, by nlinarith [sq_nonneg (2 * t - 1)]⟩

theorem smoothCorner_speed (x : ℝ) (i : Blueprint.GateIndex) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv (smoothCorner x (upperChamberHeight i)) t‖ ≤ 8 := by
  intro t ht
  rw [(hasDerivAt_smoothCorner x (upperChamberHeight i) t).deriv]
  have hh := upperChamberHeight_bounds i
  have hh2 : upperChamberHeight i < 2 := by linarith [Real.pi_lt_four, chamberWidth_pos i.1]
  by_cases hle : t ≤ 1 / 2
  · rw [cornerVelocity, ite_eq_left hle, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · nlinarith [ht.1]
    · exact mul_nonneg hh.1.le (by linarith)
  · rw [cornerVelocity, ite_eq_right hle, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith [not_le.mp hle])]
    nlinarith [ht.2]

#print axioms hasDerivAt_smoothCorner
#print axioms smoothCorner_clearance
#print axioms smoothCorner_speed

end

end MaxModulusPoints.Construction
