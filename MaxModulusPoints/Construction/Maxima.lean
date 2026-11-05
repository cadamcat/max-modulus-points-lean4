module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Analysis.SpecialFunctions.Exp
public import MaxModulusPoints.Construction.Brouwer
public import MaxModulusPoints.Construction.Shooting

/-!

# Continuous maxima on fixed compact slices

Pardo-Simón–Sixsmith, Lemma 4.5 and Corollary 4.6, compare maxima on compact
subsegments of chamber and passage slices. Compactness supplies attainment;
continuous dependence in the compact-open topology supplies continuity of these maxima.
The face estimates below are the analytic inputs from Propositions 4.1, 4.3, and 4.4.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set
open scoped ComplexConjugate

universe u v w

noncomputable section

/-- The supremum of a real objective on a fixed set. On a nonempty compact set
and for a continuous objective, this is an attained maximum. -/
def compactMaximum {X : Type v} (U : X → ℝ) (K : Set X) : ℝ := sSup (U '' K)

theorem exists_compactMaximum {X : Type v} [TopologicalSpace X]
    {U : X → ℝ} {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hU : ContinuousOn U K) : ∃ z ∈ K, U z = compactMaximum U K := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_sSup_image_eq hne hU
  exact ⟨z, hz, hmax.symm⟩

theorem le_compactMaximum {X : Type v} [TopologicalSpace X]
    {U : X → ℝ} {K : Set X} (hK : IsCompact K) (hU : ContinuousOn U K)
    {z : X} (hz : z ∈ K) : U z ≤ compactMaximum U K :=
  le_csSup (hK.bddAbove_image hU) (mem_image_of_mem U hz)

theorem compactMaximum_le {X : Type v} {U : X → ℝ} {K : Set X}
    (hne : K.Nonempty) {c : ℝ} (hbound : ∀ z ∈ K, U z ≤ c) :
    compactMaximum U K ≤ c := by
  apply csSup_le (hne.image U)
  rintro _ ⟨z, hz, rfl⟩
  exact hbound z hz

/-- Uniform perturbations of an objective change its maximum by at most the
same amount. This is the estimate used in Lemma 4.5. -/
theorem abs_compactMaximum_sub_le {X : Type v} [TopologicalSpace X]
    {U V : X → ℝ} {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hU : ContinuousOn U K) (hV : ContinuousOn V K) {ε : ℝ}
    (hclose : ∀ z ∈ K, |U z - V z| ≤ ε) :
    |compactMaximum U K - compactMaximum V K| ≤ ε := by
  obtain ⟨z, hz, hUz⟩ := exists_compactMaximum hK hne hU
  obtain ⟨w, hw, hVw⟩ := exists_compactMaximum hK hne hV
  have hzV := le_compactMaximum hK hV hz
  have hwU := le_compactMaximum hK hU hw
  have hzclose := abs_le.mp (hclose z hz)
  have hwclose := abs_le.mp (hclose w hw)
  apply abs_le.mpr
  constructor <;> linarith

/-- Joint continuity suffices for continuous dependence of compact-slice maxima. -/
theorem continuous_compactMaximum {P : Type u} {X : Type v}
    [TopologicalSpace P] [TopologicalSpace X] {U : P → X → ℝ}
    {K : Set X} (hK : IsCompact K) (hU : Continuous (Function.uncurry U)) :
    Continuous (fun p => compactMaximum (U p) K) :=
  hK.continuous_sSup hU

/-- An invariance of the objective identifies the maxima on reflected sets. -/
theorem compactMaximum_image {X : Type v} (U : X → ℝ) (e : X → X)
    (hinv : ∀ z, U (e z) = U z) (K : Set X) :
    compactMaximum U (e '' K) = compactMaximum U K := by
  simp only [compactMaximum, image_image, hinv]

/-- Modulus in logarithmic coordinates. -/
def logModulus (f : ℂ → ℂ) (z : ℂ) : ℝ := ‖f (Complex.exp z)‖

theorem continuous_logModulus (f : C(ℂ, ℂ)) : Continuous (logModulus f) :=
  (f.continuous.comp Complex.continuous_exp).norm

/-- Compact-open dependence of the entire approximants is the input supplied
by Observation 2.3; it implies joint continuity after exponentiation. -/
theorem continuous_logModulus_family {P : Type u} [TopologicalSpace P]
    {F : P → C(ℂ, ℂ)} (hF : Continuous F) :
    Continuous (fun p : P × ℂ => logModulus (F p.1) p.2) :=
  ((hF.comp continuous_fst).eval (Complex.continuous_exp.comp continuous_snd)).norm

theorem continuous_logarithmicMaximum {P : Type u} [TopologicalSpace P]
    {F : P → C(ℂ, ℂ)} (hF : Continuous F) {K : Set ℂ} (hK : IsCompact K) :
    Continuous (fun p => compactMaximum (logModulus (F p)) K) :=
  continuous_compactMaximum hK (continuous_logModulus_family hF)

/-- The upper and lower starred chamber slices have identical maxima when
the approximating function is real-symmetric, as in Lemma 4.5. -/
theorem logarithmicMaximum_conj (f : ℂ → ℂ)
    (hf : ∀ z, f (conj z) = conj (f z)) (K : Set ℂ) :
    compactMaximum (logModulus f) (conj '' K) = compactMaximum (logModulus f) K := by
  apply compactMaximum_image
  intro z
  simp only [logModulus, Complex.exp_conj, hf, Complex.norm_conj]

/-- Analytic face estimates on fixed starred segments. The closed-face bound
comes from Proposition 4.3 and approximation; the passage witness from Proposition 4.4;
the open-face witness from Proposition 4.1. All quantifiers include the other gates. -/
structure GateComparison {ι : Type u} (a b : ι → ℝ)
    (F : ParameterBox a b → C(ℂ, ℂ)) where
  passage : ι → Set ℂ
  chamber : ι → Set ℂ
  passage_compact : ∀ i, IsCompact (passage i)
  passage_nonempty : ∀ i, (passage i).Nonempty
  chamber_compact : ∀ i, IsCompact (chamber i)
  chamber_nonempty : ∀ i, (chamber i).Nonempty
  closed_bound : ι → ℝ
  passage_floor : ι → ℝ
  separated : ∀ i, closed_bound i < passage_floor i
  passage_witness : ∀ i δ, ∃ z ∈ passage i, passage_floor i ≤ logModulus (F δ) z
  closed_face : ∀ i δ, (δ i : ℝ) = a i →
    ∀ z ∈ chamber i, logModulus (F δ) z ≤ closed_bound i
  open_face : ∀ i δ, (δ i : ℝ) = b i → ∃ z ∈ chamber i,
    ∀ w ∈ passage i, logModulus (F δ) w < logModulus (F δ) z

/-- Nearly closed gates force the chamber maximum strictly below the passage maximum. -/
theorem GateComparison.closed_face_comparison {ι : Type u} {a b : ι → ℝ}
    {F : ParameterBox a b → C(ℂ, ℂ)} (D : GateComparison a b F)
    (i : ι) (δ : ParameterBox a b) (hδ : (δ i : ℝ) = a i) :
    compactMaximum (logModulus (F δ)) (D.chamber i) <
      compactMaximum (logModulus (F δ)) (D.passage i) := by
  obtain ⟨z, hz, hfloor⟩ := D.passage_witness i δ
  calc
    compactMaximum (logModulus (F δ)) (D.chamber i) ≤ D.closed_bound i :=
      compactMaximum_le (D.chamber_nonempty i) (D.closed_face i δ hδ)
    _ < D.passage_floor i := D.separated i
    _ ≤ logModulus (F δ) z := hfloor
    _ ≤ compactMaximum (logModulus (F δ)) (D.passage i) :=
      le_compactMaximum (D.passage_compact i) (continuous_logModulus (F δ)).continuousOn hz

/-- Open gates force the opposite strict comparison. -/
theorem GateComparison.open_face_comparison {ι : Type u} {a b : ι → ℝ}
    {F : ParameterBox a b → C(ℂ, ℂ)} (D : GateComparison a b F)
    (i : ι) (δ : ParameterBox a b) (hδ : (δ i : ℝ) = b i) :
    compactMaximum (logModulus (F δ)) (D.passage i) <
      compactMaximum (logModulus (F δ)) (D.chamber i) := by
  obtain ⟨z, hz, hdom⟩ := D.open_face i δ hδ
  obtain ⟨w, hw, hmax⟩ := exists_compactMaximum (D.passage_compact i)
    (D.passage_nonempty i) (continuous_logModulus (F δ)).continuousOn
  calc
    compactMaximum (logModulus (F δ)) (D.passage i) = logModulus (F δ) w := hmax.symm
    _ < logModulus (F δ) z := hdom w hw
    _ ≤ compactMaximum (logModulus (F δ)) (D.chamber i) :=
      le_compactMaximum (D.chamber_compact i) (continuous_logModulus (F δ)).continuousOn hz

/-- The simultaneous equality in Corollary 4.6, derived from compact-open
continuity and the analytic pointwise face estimates. -/
theorem GateComparison.balance {ι : Type u} {a b : ι → ℝ}
    (hab : ∀ i, a i ≤ b i) {F : ParameterBox a b → C(ℂ, ℂ)}
    (hF : Continuous F) (D : GateComparison a b F) :
    ∃ δ, ∀ i, compactMaximum (logModulus (F δ)) (D.chamber i) =
      compactMaximum (logModulus (F δ)) (D.passage i) := by
  let φ : ι → ParameterBox a b → ℝ := fun i δ =>
    compactMaximum (logModulus (F δ)) (D.passage i) -
      compactMaximum (logModulus (F δ)) (D.chamber i)
  have hφ (i : ι) : Continuous (φ i) :=
    (continuous_logarithmicMaximum hF (D.passage_compact i)).sub
      (continuous_logarithmicMaximum hF (D.chamber_compact i))
  obtain ⟨δ, hδ⟩ := infinite_box_shooting finiteBoxFixedPoint a b hab φ hφ
    (fun i δ hi => sub_nonneg.mpr (D.closed_face_comparison i δ hi).le)
    (fun i δ hi => sub_nonpos.mpr (D.open_face_comparison i δ hi).le)
  exact ⟨δ, fun i => (sub_eq_zero.mp (hδ i)).symm⟩

#print axioms continuous_logarithmicMaximum
#print axioms logarithmicMaximum_conj
#print axioms GateComparison.closed_face_comparison
#print axioms GateComparison.open_face_comparison
#print axioms GateComparison.balance

end

end MaxModulusPoints.Construction
