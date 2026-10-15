import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.Basepoint
import MaxModulusPoints.TractGeometry.Openness
import MaxModulusPoints.TractGeometry.RegularCoordinates
import MaxModulusPoints.TractGeometry.RegularPaths
/-!
# Connectedness of the chamber and gate tracts

The path component of the normalization point contains every tract point with
regular coordinates. Openness and coordinate density place the whole tract
in the closure of that connected component.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_isConnected (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (hpos : ∀ i, 0 < δ i) :
    IsConnected (tract p δ) := by
  let C : Set ℂ := pathComponentIn (tract p δ) (-1 : ℂ)
  have hgeneric {z : ℂ} (hmem : z ∈ tract p δ) (hreg : z ∈ regularCoordinates p) :
      z ∈ C := by
    have hamb : -2 < z.re ∧ |z.im| < Real.pi / 2 := by
      rcases hmem with (hclean | hopen) | hgate
      · exact hclean.1
      · obtain ⟨n, hn⟩ := mem_iUnion.mp hopen
        rcases hn with h | h | h
        · exact ((hreg.1 n).1 h.1).elim
        · exact ((hreg.1 n).2.1 h.1).elim
        · exact ((hreg.1 n).2.2 h.1).elim
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hgate
        obtain ⟨j, hj⟩ := mem_iUnion.mp hi
        exact ((hreg.1 i.1).2.2 hj.1).elim
    exact (tract_regular_joined p δ hδ hpos hreg hamb.1 hamb.2).symm
  have hconnected : IsConnected C :=
    (isPathConnected_pathComponentIn (tract_base_mem p δ)).isConnected
  have hsubset : C ⊆ tract p δ := pathComponentIn_subset
  have hclosure : tract p δ ⊆ closure C := by
    intro z hz
    apply mem_closure_iff.mpr
    intro U hU hzU
    obtain ⟨w, hwU, hwreg⟩ := (regularCoordinates_dense p).inter_open_nonempty
      (U ∩ tract p δ) (hU.inter (tract_isOpen p δ hδ)) ⟨z, hzU, hz⟩
    exact ⟨w, hwU.1, hgeneric hwU.2 hwreg⟩
  exact hconnected.subset_closure hsubset hclosure

end MaxModulusPoints.TractGeometry
