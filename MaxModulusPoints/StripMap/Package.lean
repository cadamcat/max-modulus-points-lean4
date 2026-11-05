module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.StripMap.Growth
public import MaxModulusPoints.StripMap.Normalization
public import MaxModulusPoints.StripMap.RescaledLimit
public import MaxModulusPoints.StripMap.Symmetry
public import MaxModulusPoints.StripMap.VerticalMaximum

/-!
# The normalized strip map estimates

The normalized strip-to-target equivalence has positive real values, uniform
exponential growth on the real axis, a vertical real-part maximum, and the
rescaled exponential limit with convergence of derivatives.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.Blueprint.Packages

open MaxModulusPoints.StripMap

theorem strip_map_estimates_proof : Nonempty StripMapData := by
  obtain ⟨e, he0, hepos, hereal⟩ := exists_normalized_equivalence
  exact ⟨{
    toConformalEquivalence := e
    base_value := he0
    positive_derivative := hepos
    real_derivative := hereal
    positive_real := normalized_equivalence_positive_real e he0 hepos hereal
    lowerRate := 1 / (64 * Real.pi)
    upperRate := 256 * Real.pi
    lowerRate_pos := by positivity
    upperRate_pos := by positivity
    growth := normalized_equivalence_growth e he0 hepos hereal
    vertical_maximum := normalized_equivalence_vertical_maximum e he0 hepos hereal
    rescaled_limit := normalized_equivalence_rescaled_limit e he0 hepos hereal
    rescaled_derivative_limit := normalized_equivalence_rescaled_derivative_limit e he0 hepos hereal
  }⟩

end MaxModulusPoints.Blueprint.Packages
