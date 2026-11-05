module

public import MaxModulusPoints.Challenge
public import MaxModulusPoints.ParameterApproximation.Uniqueness

/-!
# Limits of entire approximants on varying tracts

The interior error estimate passes to a limit wherever membership is eventual.
The exterior estimate passes first at points which remain outside the varying
tracts, then to their closure by continuity. This includes boundary points
which can enter a varying tract while nearby exterior points persist.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter
open scoped Topology

universe u

/-- Approximation bounds are closed under convergence and persistent exterior
approximation of the limiting complement. -/
theorem approximationBounds_of_tendsto {ι : Type u} {l : Filter ι} [NeBot l]
    {V : ι → Set ℂ} {V₀ : Set ℂ} {G : ι → ℂ → ℂ} {G₀ : ℂ → ℂ}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {M : ℝ}
    (hbounds : ∀ i, ApproximationBounds (V i) (G i) M (F i))
    (hmem : ∀ z ∈ V₀, ∀ᶠ i in l, z ∈ V i)
    (hG : ∀ z ∈ V₀, Tendsto (fun i => G i z) l (𝓝 (G₀ z)))
    (hF : ∀ z, Tendsto (fun i => F i z) l (𝓝 (f z)))
    (hf : Continuous f)
    (hext : ∀ z, z ∉ Complex.exp '' V₀ → 1 < ‖z‖ →
      z ∈ closure {w : ℂ | 1 < ‖w‖ ∧ ∀ᶠ i in l, w ∉ Complex.exp '' V i}) :
    ApproximationBounds V₀ G₀ M f := by
  constructor
  · intro z hz hnorm
    have hlim : Tendsto (fun i =>
        ‖F i (Complex.exp z) - Complex.exp (G i z)‖) l
        (𝓝 ‖f (Complex.exp z) - Complex.exp (G₀ z)‖) :=
      ((hF (Complex.exp z)).sub
        (Complex.continuous_exp.continuousAt.tendsto.comp (hG z hz))).norm
    apply le_of_tendsto hlim
    filter_upwards [hmem z hz] with i hi
    exact (hbounds i).1 z hi hnorm
  · have hclosed : IsClosed {z : ℂ | ‖f z‖ * ‖z‖ ≤ M} :=
      isClosed_le (hf.norm.mul continuous_norm) continuous_const
    have hstable : {w : ℂ | 1 < ‖w‖ ∧ ∀ᶠ i in l, w ∉ Complex.exp '' V i} ⊆
        {z : ℂ | ‖f z‖ * ‖z‖ ≤ M} := by
      intro z hz
      have hlim : Tendsto (fun i => ‖F i z‖ * ‖z‖) l (𝓝 (‖f z‖ * ‖z‖)) :=
        (hF z).norm.mul_const ‖z‖
      apply le_of_tendsto hlim
      filter_upwards [hz.2] with i hi
      exact (le_div_iff₀ (lt_trans zero_lt_one hz.1)).mp ((hbounds i).2 z hi hz.1)
    intro z hz hnorm
    apply (le_div_iff₀ (lt_trans zero_lt_one hnorm)).mpr
    exact closure_minimal hstable hclosed (hext z hz hnorm)

/-- Every entire limit retaining the model and exterior convergence data is
the unique approximant of the limiting conformal map. -/
theorem limit_eq_approximant {ι : Type u} {l : Filter ι} [NeBot l]
    {V : ι → Set ℂ} {V₀ : Set ℂ} {G : ι → ℂ → ℂ} {G₀ : ℂ → ℂ}
    {F : ι → ℂ → ℂ} {f f₀ : ℂ → ℂ} {M M₀ : ℝ}
    (hbounds : ∀ i, ApproximationBounds (V i) (G i) M (F i))
    (hmem : ∀ z ∈ V₀, ∀ᶠ i in l, z ∈ V i)
    (hG : ∀ z ∈ V₀, Tendsto (fun i => G i z) l (𝓝 (G₀ z)))
    (hF : ∀ z, Tendsto (fun i => F i z) l (𝓝 (f z)))
    (hf : Entire f) (hf₀ : Entire f₀)
    (hext : ∀ z, z ∉ Complex.exp '' V₀ → 1 < ‖z‖ →
      z ∈ closure {w : ℂ | 1 < ‖w‖ ∧ ∀ᶠ i in l, w ∉ Complex.exp '' V i})
    (h₀ : ApproximationBounds V₀ G₀ M₀ f₀) : f = f₀ := by
  exact approximation_unique hf hf₀
    (approximationBounds_of_tendsto hbounds hmem hG hF hf.continuous hext) h₀

#print axioms approximationBounds_of_tendsto
#print axioms limit_eq_approximant

end MaxModulusPoints.ParameterApproximation
