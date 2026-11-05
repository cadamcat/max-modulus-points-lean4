module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.ChamberCover
public import MaxModulusPoints.TractGeometry.ChamberPaths
public import MaxModulusPoints.TractGeometry.GapPaths
public import MaxModulusPoints.TractGeometry.PassagePaths
public import MaxModulusPoints.TractGeometry.RealAxis
public import MaxModulusPoints.TractGeometry.RegularCoordinates
public import MaxModulusPoints.TractGeometry.ShoulderPaths
public import MaxModulusPoints.TractGeometry.TunnelPaths

/-!
# Connecting points with regular coordinates

Every regular point of the ambient strip lies in a gap or in the interior of
one of the block regions. The region paths join it to the real axis, which
then connects it to the normalization point.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Blueprint

theorem tract_regular_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (hpos : ∀ i, 0 < δ i) {z : ℂ}
    (hz : z ∈ regularCoordinates p) (hx : -2 < z.re) (hy : |z.im| < Real.pi / 2) :
    JoinedIn (tract p δ) z (-1 : ℂ) := by
  have hreal {x : ℝ} (h : -2 < x) : JoinedIn (tract p δ) (x : ℂ) (-1 : ℂ) := by
    simpa using tract_real_joined p δ (x := x) (y := -1) h (by norm_num)
  by_cases hblock : ∃ n, blockPosition p n ≤ z.re ∧ z.re ≤ blockPosition p n + 1
  · obtain ⟨n, hleft, hright⟩ := hblock
    have hl : blockPosition p n < z.re :=
      lt_of_le_of_ne hleft (hz.1 n).1.symm
    have hr : z.re < blockPosition p n + 1 :=
      lt_of_le_of_ne hright (hz.1 n).2.2
    have hgapReal : -2 < blockPosition p n + 3 / 2 := by linarith
    by_cases hb : |z.im| < chamberBase
    · by_cases hp : z.re < blockPosition p n + 1 / 2
      · exact (tract_passage_joined p δ n hl hp hb).trans (hreal hx)
      · have hp' : blockPosition p n + 1 / 2 < z.re :=
          lt_of_le_of_ne (le_of_not_gt hp) (hz.1 n).2.1.symm
        by_cases ht : |z.im| < p.tunnelHeight n / 2
        · exact (tract_tunnel_joined p δ n hp' hr ht).trans (hreal hx)
        · have ht' : p.tunnelHeight n / 2 < |z.im| :=
            lt_of_le_of_ne (le_of_not_gt ht) (hz.2.1 n).symm
          exact (tract_shoulder_joined p δ n hp' hr ht' hb).trans (hreal hgapReal)
    · have hne : |z.im| ≠ chamberBase := by simpa using hz.2.2 n 0
      have hb' : chamberBase < |z.im| := lt_of_le_of_ne (le_of_not_gt hb) hne.symm
      obtain ⟨m, j, hyl, hyu⟩ := regularCoordinates_chamber_layer p n hz hb' hy
      exact (tract_chamber_joined p δ hδ ⟨n, m⟩ (hpos ⟨n, m⟩) j hl hr hyl hyu).trans
        (hreal hgapReal)
  · have hgap : ∀ n, z.re < blockPosition p n ∨ blockPosition p n + 1 < z.re := by
      intro n
      by_cases hl : z.re < blockPosition p n
      · exact Or.inl hl
      · right
        apply lt_of_not_ge
        intro hr
        exact hblock ⟨n, le_of_not_gt hl, hr⟩
    exact (tract_gap_joined p δ hx hy hgap).trans (hreal hx)

end MaxModulusPoints.TractGeometry
