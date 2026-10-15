import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.Basepoint
import MaxModulusPoints.TractGeometry.Connectedness
import MaxModulusPoints.TractGeometry.NormalizedSymmetry
import MaxModulusPoints.TractGeometry.Openness
import MaxModulusPoints.TractGeometry.SimplyConnected
import MaxModulusPoints.TractGeometry.StripContainment
import MaxModulusPoints.TractGeometry.Symmetry
import MaxModulusPoints.TractGeometry.TargetGeometry
/-!
# Normalized conformal equivalences for the chamber and gate tract

The source geometry supplies the hypotheses for a normalized symmetric
conformal equivalence with the fixed target.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_normalized_equivalence (hT : TargetGeometry) (hR : SymmetricRiemannMaps)
    (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) (hpos : ∀ i, 0 < δ i) :
    Nonempty (NormalizedSymmetricEquivalence (tract p δ) target (-1) 1) := by
  have hsource : tract p δ ≠ univ := by
    intro heq
    have hmem : (-3 : ℂ) ∈ tract p δ := by rw [heq]; exact mem_univ _
    have hreal := tract_re_gt p δ hmem
    norm_num at hreal
  have htarget : target ≠ univ := by
    intro heq
    apply hT.zero_not_mem
    rw [heq]
    exact mem_univ _
  exact hR (tract p δ) target (-1) 1
    (tract_isOpen p δ hδ) (tract_isConnected p δ hδ hpos)
    (tract_isSimplyConnected p δ hδ hpos) hsource
    hT.open_domain hT.connected_domain hT.simply_connected htarget
    (by simpa using tract_base_mem p δ) (by simpa using hT.base_mem)
    (fun _ hz => tract_star_mem p δ hz)
    hT.symmetric_domain

end MaxModulusPoints.TractGeometry
