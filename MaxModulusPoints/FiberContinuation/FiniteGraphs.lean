module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.FiberContinuation.LogarithmicValues

/-!
# Whole-image regularity of finite graph families

If every graph through the chosen target has the same germ, continuity removes
the other finitely many graphs from a smaller product neighborhood. The whole
actual image there is then exactly one holomorphic graph.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.FiberContinuation

open Set Filter Metric
open scoped Topology
open MaxModulusPoints.Blueprint

universe u

/-- A finite analytic graph description with persistent central collisions gives
the frozen whole-image regularity property. -/
theorem regularTarget_of_local_finite_graphs {f : ℂ → ℂ} (d : NormalizedFunction f)
    {ι : Type u} [Finite ι] (ψ : ι → ℂ → ℂ) (j : ι) (q₀ : ℂ)
    (hanalytic : ∀ i, AnalyticAt ℂ (ψ i) q₀)
    (hs₀ : ψ j q₀ ≠ 0) (hq₀ : q₀ ≠ (d.multiplicity : ℂ))
    (hcollision : ∀ i, ψ i q₀ = ψ j q₀ → ∀ᶠ q in 𝓝 q₀, ψ i q = ψ j q)
    (himage : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀),
      (physicalFiber d v.1 (v.2 : OnePoint ℂ)).Nonempty ↔ ∃ i, v.1 = ψ i v.2) :
    RegularTarget d (ψ j q₀) q₀ := by
  have hselect : ∀ i, ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀),
      v.1 = ψ i v.2 → v.1 = ψ j v.2 := by
    intro i
    by_cases hi : ψ i q₀ = ψ j q₀
    · have hevent : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀), ψ i v.2 = ψ j v.2 :=
        (continuous_snd.tendsto (ψ j q₀, q₀)).eventually (hcollision i hi)
      filter_upwards [hevent] with v hv heq
      exact heq.trans hv
    · have hcont : ContinuousAt (fun v : ℂ × ℂ => v.1 - ψ i v.2) (ψ j q₀, q₀) :=
        continuous_fst.continuousAt.sub ((hanalytic i).continuousAt.comp continuous_snd.continuousAt)
      have hne : ψ j q₀ - ψ i q₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
      have hevent : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀), v.1 - ψ i v.2 ≠ 0 :=
        hcont.eventually (isOpen_ne.mem_nhds hne)
      filter_upwards [hevent] with v hv heq
      exact False.elim (hv (sub_eq_zero.mpr heq))
  have hsne : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀), v.1 ≠ 0 :=
    (continuous_fst.tendsto (ψ j q₀, q₀)).eventually (isOpen_ne.mem_nhds hs₀)
  have hqne : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀), v.2 ≠ (d.multiplicity : ℂ) :=
    (continuous_snd.tendsto (ψ j q₀, q₀)).eventually (isOpen_ne.mem_nhds hq₀)
  have hall : ∀ᶠ v : ℂ × ℂ in 𝓝 (ψ j q₀, q₀),
      (∀ i, v.1 = ψ i v.2 → v.1 = ψ j v.2) ∧
      ((physicalFiber d v.1 (v.2 : OnePoint ℂ)).Nonempty ↔ ∃ i, v.1 = ψ i v.2) ∧
      v.1 ≠ 0 ∧ v.2 ≠ (d.multiplicity : ℂ) :=
    (eventually_all.mpr hselect).and (himage.and (hsne.and hqne))
  obtain ⟨U, V, hU, hsU, hV, hqV, hsub⟩ := mem_nhds_prod_iff'.mp hall
  have hmap : ∀ᶠ q in 𝓝 q₀, ψ j q ∈ U :=
    (hanalytic j).continuousAt.eventually (hU.mem_nhds hsU)
  have hconditions : ∀ᶠ q in 𝓝 q₀, q ∈ V ∧ ψ j q ∈ U ∧ AnalyticAt ℂ (ψ j) q :=
    Filter.Eventually.and (hV.mem_nhds hqV) (hmap.and (hanalytic j).eventually_analyticAt)
  obtain ⟨r, hr, hsmall⟩ := nhds_basis_ball.eventually_iff.mp hconditions
  refine ⟨U, ball q₀ r, ψ j, hU, isOpen_ball, hsU, mem_ball_self hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hsub (show (x, q₀) ∈ U ×ˢ V from ⟨hx, hqV⟩)).2.2.1
  · intro q hq
    exact (hsub (show (ψ j q₀, q) ∈ U ×ˢ V from ⟨hsU, (hsmall hq).1⟩)).2.2.2
  · intro q hq
    exact (hsmall hq).2.2.differentiableAt.differentiableWithinAt
  · intro q hq
    exact (hsmall hq).2.1
  · intro x hx q hq
    have h := hsub (show (x, q) ∈ U ×ˢ V from ⟨hx, (hsmall hq).1⟩)
    constructor
    · intro hfiber
      obtain ⟨i, hi⟩ := h.2.1.mp hfiber
      exact h.1 i hi
    · intro heq
      exact h.2.1.mpr ⟨j, heq⟩

end MaxModulusPoints.FiberContinuation
