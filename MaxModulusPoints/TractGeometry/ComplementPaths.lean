import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.ChamberFrontierPaths
import MaxModulusPoints.TractGeometry.ExteriorPaths
import MaxModulusPoints.TractGeometry.PassageWallPaths
import MaxModulusPoints.TractGeometry.TunnelWallPaths
/-!
# Paths in the complement of the tract

Every point outside the tract lies outside the ambient strip or on a
removed wall. The corresponding paths share a fixed exterior endpoint.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_compl_joined (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) {z : ℂ} (hz : z ∉ tract p δ) :
    JoinedIn (tract p δ)ᶜ z (-3 : ℂ) := by
  by_cases houter : z.re ≤ -2 ∨ Real.pi / 2 ≤ |z.im|
  · exact tract_compl_exterior_joined p δ hδ houter
  · have hreal : -2 < z.re := lt_of_not_ge (fun h => houter (Or.inl h))
    have him : |z.im| < Real.pi / 2 := lt_of_not_ge (fun h => houter (Or.inr h))
    have hwall : z ∈ walls p := by
      by_contra hw
      exact hz (Or.inl (Or.inl ⟨⟨hreal, him⟩, hw⟩))
    obtain ⟨n, hn⟩ := mem_iUnion.mp hwall
    rcases hn with (hpassage | htunnel) | hchamber
    · exact passage_frontier_compl_joined p δ hδ n hpassage hz
    · exact tunnel_frontier_compl_joined p δ hδ n htunnel hz
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hchamber
      obtain ⟨j, hj⟩ := mem_iUnion.mp hm
      exact chamber_frontier_compl_joined p δ hδ ⟨n, m⟩ j hj hz

end MaxModulusPoints.TractGeometry
