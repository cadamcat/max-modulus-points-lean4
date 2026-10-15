import Mathlib.Analysis.Convex.PathConnected
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.Openings
import MaxModulusPoints.TractGeometry.RectangleFrontiers
/-!
# The real axis in the chamber and gate tracts

The real interval to the right of the left boundary lies in every tract.
Any wall that meets this interval does so at a restored passage opening.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_real_mem (p : BlockParameters) (δ : GateIndex → ℝ)
    {x : ℝ} (hx : -2 < x) : (x : ℂ) ∈ tract p δ := by
  have hb : 0 < chamberBase := by
    dsimp [chamberBase]
    linarith [Real.pi_gt_three]
  have hyb : |(x : ℂ).im| < chamberBase := by simpa using hb
  by_cases hw : (x : ℂ) ∈ walls p
  · rcases mem_iUnion.mp hw with ⟨n, hn⟩
    have ht : 0 < p.tunnelHeight n / 2 := div_pos (p.tunnel_pos n) (by norm_num)
    have hyt : |(x : ℂ).im| < p.tunnelHeight n / 2 := by simpa using ht
    have ho : (x : ℂ) ∈ openings p n := by
      rcases hn with (hp | htun) | hc
      · have hr := rectangle_frontier_bounds (blockPosition p n)
          (blockPosition p n + 1 / 2) (-chamberBase) chamberBase
          (by simpa only [passage, abs_le] using hp)
        rcases hr.2 with h | h | h | h
        · exact Or.inl ⟨h, hyb⟩
        · exact Or.inr (Or.inl ⟨h, hyt⟩)
        · simp only [Complex.ofReal_im] at h
          linarith
        · simp only [Complex.ofReal_im] at h
          linarith
      · have hr := rectangle_frontier_bounds (blockPosition p n + 1 / 2)
          (blockPosition p n + 1) (-(p.tunnelHeight n / 2)) (p.tunnelHeight n / 2)
          (by simpa only [tunnel, abs_le] using htun)
        rcases hr.2 with h | h | h | h
        · exact Or.inr (Or.inl ⟨h, hyt⟩)
        · exact Or.inr (Or.inr ⟨h, hyt⟩)
        · simp only [Complex.ofReal_im] at h
          linarith
        · simp only [Complex.ofReal_im] at h
          linarith
      · rcases mem_iUnion.mp hc with ⟨m, hm⟩
        rcases mem_iUnion.mp hm with ⟨j, hj⟩
        have hclosed : IsClosed (chamber p ⟨n, m⟩ j) :=
          (isClosed_le continuous_const Complex.continuous_re).inter
            ((isClosed_le Complex.continuous_re continuous_const).inter
              ((isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)).inter
                (isClosed_le (continuous_const.mul Complex.continuous_im) continuous_const)))
        have hlow := (hclosed.frontier_subset hj).2.2.1
        simp only [Complex.ofReal_im, mul_zero] at hlow
        have hfrac : 0 ≤ (m.val : ℝ) / ((n : ℝ) + 1) := by positivity
        exfalso
        linarith
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨n, ho⟩))
  · refine Or.inl (Or.inl ⟨⟨hx, ?_⟩, hw⟩)
    simpa using (div_pos Real.pi_pos (by norm_num) : 0 < Real.pi / 2)

theorem tract_real_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    {x y : ℝ} (hx : -2 < x) (hy : -2 < y) :
    JoinedIn (tract p δ) (x : ℂ) (y : ℂ) := by
  have hreal : JoinedIn (Ioi (-2 : ℝ)) x y :=
    ((convex_Ioi (-2 : ℝ)).isPathConnected ⟨x, hx⟩).joinedIn x hx y hy
  refine (hreal.map Complex.continuous_ofReal.continuousOn).mono ?_
  rintro z ⟨t, ht, rfl⟩
  exact tract_real_mem p δ ht

end MaxModulusPoints.TractGeometry
