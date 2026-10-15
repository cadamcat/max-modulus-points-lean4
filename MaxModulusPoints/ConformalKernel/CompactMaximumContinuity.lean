import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Challenge
import MaxModulusPoints.ConformalKernel.CompactMaxima
/-!
# Continuity of compact-slice maxima

Local uniform dependence of an entire family gives continuous maximum modulus
on every fixed nonempty compact slice in logarithmic coordinates.
-/

open Set Filter
open scoped Topology

namespace MaxModulusPoints.Blueprint.Packages

/-- Continuity of the compact-slice maximum in Pardo-Simón–Sixsmith, Lemma 4.5. -/
theorem compact_maximum_continuity_proof {P : Type} [TopologicalSpace P]
    (σ : Set ℂ) (hcompact : IsCompact σ) (hne : σ.Nonempty)
    (F : P → ℂ → ℂ) (hF : ∀ p, Entire (F p))
    (hdep : ∀ p, TendstoLocallyUniformly F (F p) (𝓝 p)) :
    Continuous (fun p => sliceMaximum σ (F p)) := by
  exact ConformalKernel.continuous_logSliceMaximum hcompact hne
    (fun p => (hF p).continuous.continuousOn) hdep

#print axioms compact_maximum_continuity_proof

end MaxModulusPoints.Blueprint.Packages
