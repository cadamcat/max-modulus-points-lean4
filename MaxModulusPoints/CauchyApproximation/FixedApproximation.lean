import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.FixedRempeApproximation
import MaxModulusPoints.CauchyApproximation.CanonicalApproximation
import MaxModulusPoints.CauchyApproximation.ExponentialAdapter
import MaxModulusPoints.CauchyApproximation.GlobalCoreBounds
import MaxModulusPoints.CauchyApproximation.Model
import MaxModulusPoints.CauchyApproximation.NonMonomial
import MaxModulusPoints.CauchyApproximation.RealSymmetry
import MaxModulusPoints.CauchyApproximation.TractWallContract
import MaxModulusPoints.Challenge
/-!
# Controlled approximation on the chamber and gate tracts

The canonical entire function gives uniform approximation on the interior
core and uniform decay outside it. Decay of the exponential conformal
function between the core and the tract walls extends the approximation
to the whole original tract.
-/

open Complex Set

namespace MaxModulusPoints.CauchyApproximation

open Blueprint

/-- Wall decay completes the canonical, symmetric, non-monomial entire
approximation with a constant uniform over all admissible tracts. -/
theorem fixedRempeApproximation_of_tractWallDecay (hwall : TractWallDecay) :
    FixedRempeApproximation := by
  obtain ⟨C, hC, hcore⟩ := exists_uniform_core_approximation_bound
  obtain ⟨D, hD, hwall⟩ := hwall
  refine ⟨C + D, by positivity, ?_⟩
  intro p δ hδ G
  obtain ⟨m, hdomain, hforward, _, hsymm⟩ := logModelAdapter (tract p δ) G
  have hmem {z : ℂ} (hz : z ∈ tract p δ) : Complex.exp z ∈ m.domain := by
    rw [hdomain]
    exact mem_image_of_mem _ hz
  have hright : ∀ z ∈ m.domain, 0 < z.re := by
    intro z hz
    rw [hdomain] at hz
    exact tract_exp_re_pos p δ (fun i => (hδ i).2) hz
  refine ⟨m.canonicalEntire, m.canonicalEntire_spec.1,
    m.canonicalEntire_not_monomial hright, ?_, ?_, ?_⟩
  · intro z
    exact m.canonicalEntire_conj hsymm z
  · intro z hz hnorm
    have hn : 0 < ‖Complex.exp z‖ := zero_lt_one.trans hnorm
    by_cases hc : Complex.exp z ∈ m.core
    · have hb := (hcore m _ hn).1 hc
      rw [NormalizedModel.modelFunction, hforward z hz] at hb
      exact hb.trans
        (div_le_div_of_nonneg_right (by linarith : C ≤ C + D) hn.le)
    · have hleft : (G.toFun z).re ≤
          1 - 13 * max 0 (Real.log |(G.toFun z).im|) := by
        apply le_of_not_gt
        intro h
        apply hc
        refine ⟨hmem hz, ?_⟩
        rw [hforward z hz]
        exact h
      have hg := hwall p δ hδ G z hz hnorm hleft
      have hf := (hcore m _ hn).2 hc
      calc
        _ ≤ ‖m.canonicalEntire (Complex.exp z)‖ + ‖Complex.exp (G.toFun z)‖ :=
          norm_sub_le _ _
        _ ≤ C / ‖Complex.exp z‖ + D / ‖Complex.exp z‖ := add_le_add hf hg
        _ = (C + D) / ‖Complex.exp z‖ := (add_div _ _ _).symm
  · intro z hz hnorm
    have hn : 0 < ‖z‖ := zero_lt_one.trans hnorm
    have hc : z ∉ m.core := fun hc => hz (by simpa only [hdomain] using hc.1)
    exact ((hcore m z hn).2 hc).trans
      (div_le_div_of_nonneg_right (by linarith : C ≤ C + D) hn.le)

#print axioms fixedRempeApproximation_of_tractWallDecay

end MaxModulusPoints.CauchyApproximation
