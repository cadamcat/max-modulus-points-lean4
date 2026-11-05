module

public import Mathlib.Analysis.Convex.PathConnected
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.TractGeometry.StripContainment

/-!
# Paths outside the ambient strip

The left closed half-plane lies in the tract complement. Above or below the
strip, horizontal paths enter that half-plane, where every point connects to
the real point `-3`.
-/


@[expose] public section

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_compl_exterior_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) {z : ℂ}
    (hz : z.re ≤ -2 ∨ Real.pi / 2 ≤ |z.im|) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  have hleft : {w : ℂ | w.re ≤ -2} ⊆ (tract p δ)ᶜ := by
    intro w hw hmem
    exact (not_lt_of_ge hw) (tract_re_gt p δ hmem)
  have hleftConv : Convex ℝ {w : ℂ | w.re ≤ -2} :=
    (convex_Iic (-2 : ℝ)).linear_preimage Complex.reLm
  have hleftPath {w : ℂ} (hw : w.re ≤ -2) :
      JoinedIn (tract p δ)ᶜ w (-3 : ℂ) :=
    ((hleftConv.isPathConnected ⟨w, hw⟩).joinedIn w hw (-3) (by norm_num)).mono hleft
  rcases hz with hx | hy
  · exact hleftPath hx
  · let q : ℂ := ⟨-3, z.im⟩
    have hlevel : Convex ℝ {w : ℂ | w.im = z.im} :=
      (convex_singleton z.im).linear_preimage Complex.imLm
    have hhorizontal : JoinedIn {w : ℂ | w.im = z.im} z q :=
      (hlevel.isPathConnected ⟨z, rfl⟩).joinedIn z rfl q rfl
    have hhorComp : JoinedIn (tract p δ)ᶜ z q := hhorizontal.mono (by
      intro w hw hmem
      have hb := tract_im_lt p δ hδ hmem
      change w.im = z.im at hw
      rw [hw] at hb
      exact (not_lt_of_ge hy) hb)
    exact hhorComp.trans (hleftPath (by norm_num [q]))

end MaxModulusPoints.TractGeometry
