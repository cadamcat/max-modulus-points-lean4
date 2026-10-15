import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
/-!
# Simultaneous shooting on products of intervals

The compactness step of Pardo-Simón–Sixsmith, Lemma 2.4, works for an arbitrary
index set. Finite-dimensional Brouwer is recorded explicitly as an input;
the reduction to face signs and the passage to infinitely many equations are proved here.
-/

namespace MaxModulusPoints.Construction

open Set

universe u v

/-- The gate parameters carry the product topology, including for infinitely many gates. -/
abbrev ParameterBox {ι : Type u} (a b : ι → ℝ) := ∀ i, Icc (a i) (b i)

/-- The finite-dimensional fixed-point theorem for boxes. This is precisely the
topological input used to obtain the finite Poincaré–Miranda theorem in Lemma 2.4. -/
def FiniteBoxFixedPoint : Prop :=
  ∀ (ι : Type u) [Fintype ι] (a b : ι → ℝ), (∀ i, a i ≤ b i) →
    ∀ T : ParameterBox a b → ParameterBox a b, Continuous T → ∃ x, T x = x

/-- Closed zero sets in a compact space have a common point if every finite
subfamily does. No sequential or countability assumption is needed. -/
theorem exists_common_zero_of_finite {P : Type v} [TopologicalSpace P] [CompactSpace P]
    {ι : Type u} (φ : ι → P → ℝ) (hφ : ∀ i, Continuous (φ i))
    (hfinite : ∀ s : Finset ι, ∃ p, ∀ i ∈ s, φ i p = 0) :
    ∃ p, ∀ i, φ i p = 0 := by
  have hc (i : ι) : IsClosed {p | φ i p = 0} := isClosed_eq (hφ i) continuous_const
  obtain ⟨p, _, hp⟩ := isCompact_univ.inter_iInter_nonempty
    (fun i => {p | φ i p = 0}) hc (by
      intro s
      obtain ⟨p, hp⟩ := hfinite s
      exact ⟨p, mem_univ _, mem_iInter₂.mpr hp⟩)
  exact ⟨p, fun i => mem_iInter.mp hp i⟩

/-- The finite shooting argument: project `x + φ(x)` back to the box and
use the face signs to show that a fixed point is a zero. Degenerate intervals are allowed. -/
theorem finite_box_shooting (hfixed : FiniteBoxFixedPoint.{u})
    {ι : Type u} [Fintype ι] (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (φ : ι → ParameterBox a b → ℝ) (hφ : ∀ i, Continuous (φ i))
    (hlo : ∀ i x, (x i : ℝ) = a i → 0 ≤ φ i x)
    (hhi : ∀ i x, (x i : ℝ) = b i → φ i x ≤ 0) :
    ∃ x, ∀ i, φ i x = 0 := by
  let T : ParameterBox a b → ParameterBox a b :=
    fun x i => projIcc (a i) (b i) (hab i) ((x i : ℝ) + φ i x)
  have hT : Continuous T := continuous_pi fun i =>
    continuous_projIcc.comp (((continuous_apply i).subtype_val).add (hφ i))
  obtain ⟨x, hx⟩ := hfixed ι a b hab T hT
  refine ⟨x, fun i => ?_⟩
  have heq : max (a i) (min (b i) ((x i : ℝ) + φ i x)) = (x i : ℝ) :=
    congrArg (fun y : ParameterBox a b => (y i : ℝ)) hx
  have hleft := (x i).property.1
  have hright := (x i).property.2
  rcases lt_trichotomy (φ i x) 0 with hneg | hzero | hpos
  · have hax : a i < (x i : ℝ) := lt_of_le_of_ne hleft (by
      intro ha
      have := hlo i x ha.symm
      linarith)
    have hsmall : min (b i) ((x i : ℝ) + φ i x) < (x i : ℝ) :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have := max_lt hax hsmall
    linarith
  · exact hzero
  · have hxb : (x i : ℝ) < b i := lt_of_le_of_ne hright (by
      intro hb
      have := hhi i x hb
      linarith)
    have hlarge : (x i : ℝ) < min (b i) ((x i : ℝ) + φ i x) :=
      lt_min hxb (by linarith)
    have := lt_of_lt_of_le hlarge (le_max_right (a i) _)
    linarith

/-- Freeze all parameters outside a finite set at their lower endpoints.
The finite shooting conclusion remains uniform over those frozen coordinates. -/
theorem finite_coordinates_shooting (hfixed : FiniteBoxFixedPoint.{u})
    {ι : Type u} (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (φ : ι → ParameterBox a b → ℝ) (hφ : ∀ i, Continuous (φ i))
    (hlo : ∀ i x, (x i : ℝ) = a i → 0 ≤ φ i x)
    (hhi : ∀ i x, (x i : ℝ) = b i → φ i x ≤ 0) (s : Finset ι) :
    ∃ x, ∀ i ∈ s, φ i x = 0 := by
  classical
  let extend : ParameterBox (fun i : s => a i) (fun i : s => b i) → ParameterBox a b :=
    fun y i => if hi : i ∈ s then y ⟨i, hi⟩ else ⟨a i, le_rfl, hab i⟩
  have hext : Continuous extend := by
    apply continuous_pi
    intro i
    dsimp [extend]
    split_ifs with hi
    · exact continuous_apply (⟨i, hi⟩ : s)
    · exact continuous_const
  obtain ⟨y, hy⟩ := finite_box_shooting hfixed
    (fun i : s => a i) (fun i : s => b i) (fun i => hab i)
    (fun i y => φ i (extend y)) (fun i => (hφ i).comp hext)
    (fun i y hi => hlo i (extend y) (by simpa [extend, i.property] using hi))
    (fun i y hi => hhi i (extend y) (by simpa [extend, i.property] using hi))
  exact ⟨extend y, fun i hi => hy ⟨i, hi⟩⟩

/-- Infinite shooting, as in Pardo-Simón–Sixsmith, Lemma 2.4.
The only topological input beyond compactness is finite-dimensional Brouwer. -/
theorem infinite_box_shooting (hfixed : FiniteBoxFixedPoint.{u})
    {ι : Type u} (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (φ : ι → ParameterBox a b → ℝ) (hφ : ∀ i, Continuous (φ i))
    (hlo : ∀ i x, (x i : ℝ) = a i → 0 ≤ φ i x)
    (hhi : ∀ i x, (x i : ℝ) = b i → φ i x ≤ 0) :
    ∃ x, ∀ i, φ i x = 0 :=
  exists_common_zero_of_finite φ hφ (finite_coordinates_shooting hfixed a b hab φ hφ hlo hhi)

/-- The sign orientation may depend on the coordinate, as in Lemma 2.4. -/
theorem signed_infinite_box_shooting (hfixed : FiniteBoxFixedPoint.{u})
    {ι : Type u} (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (φ : ι → ParameterBox a b → ℝ) (hφ : ∀ i, Continuous (φ i))
    (σ : ι → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (hlo : ∀ i x, (x i : ℝ) = a i → 0 ≤ σ i * φ i x)
    (hhi : ∀ i x, (x i : ℝ) = b i → σ i * φ i x ≤ 0) :
    ∃ x, ∀ i, φ i x = 0 := by
  obtain ⟨x, hx⟩ := infinite_box_shooting hfixed a b hab
    (fun i x => σ i * φ i x) (fun i => continuous_const.mul (hφ i)) hlo hhi
  exact ⟨x, fun i => (mul_eq_zero.mp (hx i)).resolve_left (hσ i)⟩

#print axioms exists_common_zero_of_finite
#print axioms finite_box_shooting
#print axioms infinite_box_shooting
#print axioms signed_infinite_box_shooting

end MaxModulusPoints.Construction
