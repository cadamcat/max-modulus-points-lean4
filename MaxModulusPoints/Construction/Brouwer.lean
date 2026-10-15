import FixedPointTheorems.brouwer
import MaxModulusPoints.Construction.Shooting
/-!
# Brouwer's theorem supplies finite shooting

The product of interval subtypes is homeomorphic to the corresponding compact
convex box in a finite-dimensional real vector space. This supplies the finite
topological input in Pardo-Simón–Sixsmith, Lemma 2.4.
-/

namespace MaxModulusPoints.Construction

open Set

universe u

/-- Brouwer's theorem in the product-of-intervals formulation. -/
theorem finiteBoxFixedPoint : FiniteBoxFixedPoint.{u} := by
  intro ι inst a b hab T hT
  let K : Set (ι → ℝ) := Set.univ.pi (fun i => Icc (a i) (b i))
  let e : ParameterBox a b ≃ₜ K :=
    { toFun := fun x => ⟨fun i => (x i : ℝ), mem_univ_pi.mpr (fun i => (x i).property)⟩
      invFun := fun x i => ⟨x.val i, mem_univ_pi.mp x.property i⟩
      left_inv := fun x => by ext i; rfl
      right_inv := fun x => by ext i; rfl
      continuous_toFun := (continuous_pi (fun i => (continuous_apply i).subtype_val)).subtype_mk _
      continuous_invFun := continuous_pi (fun i =>
        ((continuous_apply i).comp continuous_subtype_val).subtype_mk _) }
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hconv : Convex ℝ K := convex_pi (fun _ _ => convex_Icc _ _)
  have hne : K.Nonempty := ⟨fun i => a i, mem_univ_pi.mpr (fun i => ⟨le_rfl, hab i⟩)⟩
  let F : C(K, K) := ⟨fun x => e (T (e.symm x)),
    e.continuous.comp (hT.comp e.symm.continuous)⟩
  obtain ⟨x, hx⟩ := brouwer_fixed_point K hconv hK hne F
  refine ⟨e.symm x, ?_⟩
  have h := congrArg e.symm hx
  simpa [F] using h

/-- Pardo-Simón–Sixsmith, Lemma 2.4, with arbitrary index type and a prescribed
coordinatewise orientation. In particular, signs in `{−1, 1}` are permitted. -/
theorem shooting {ι : Type u} (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (φ : ι → ParameterBox a b → ℝ) (hφ : ∀ i, Continuous (φ i))
    (σ : ι → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (hlo : ∀ i x, (x i : ℝ) = a i → 0 ≤ σ i * φ i x)
    (hhi : ∀ i x, (x i : ℝ) = b i → σ i * φ i x ≤ 0) :
    ∃ x, ∀ i, φ i x = 0 :=
  signed_infinite_box_shooting finiteBoxFixedPoint a b hab φ hφ σ hσ hlo hhi

#print axioms finiteBoxFixedPoint
#print axioms shooting

end MaxModulusPoints.Construction
