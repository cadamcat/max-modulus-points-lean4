import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.TractGeometry.Gates
import MaxModulusPoints.TractGeometry.Openings
import MaxModulusPoints.TractGeometry.Walls
/-!
# Openness of the chamber and gate tracts

The complement of the closed walls is open within the ambient strip. Each
restored opening and gate also has a neighborhood contained in the tract.
-/

namespace MaxModulusPoints.TractGeometry

open Set
open Blueprint

theorem tract_isOpen (p : BlockParameters) (δ : GateIndex → ℝ)
    (hδ : ∀ i, δ i ≤ gateUpper i) : IsOpen (tract p δ) := by
  apply subset_interior_iff_isOpen.mp
  intro z hz
  rcases hz with (hz | hz) | hz
  · have hopen : IsOpen
        ({w : ℂ | -2 < w.re ∧ |w.im| < Real.pi / 2} \ walls p) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im.abs continuous_const)).sdiff (walls_isClosed p)
    exact interior_maximal (fun _ hw => Or.inl (Or.inl hw)) hopen hz
  · rcases mem_iUnion.mp hz with ⟨n, hn⟩
    exact openings_subset_interior p δ n hn
  · rcases mem_iUnion.mp hz with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨j, hj⟩
    exact gate_subset_interior p δ hδ i j hj

end MaxModulusPoints.TractGeometry
