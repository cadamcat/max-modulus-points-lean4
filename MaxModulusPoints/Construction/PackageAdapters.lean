module

public import Mathlib.Data.Fintype.Option
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Challenge
public import MaxModulusPoints.Construction.Brouwer
public import MaxModulusPoints.Construction.CirclePoints
public import MaxModulusPoints.Construction.Maxima
public import MaxModulusPoints.Construction.Shooting

/-!

# Simultaneous shooting and global maximum counts

The simultaneous-zero theorem supplies Lemma 2.4 of Pardo-Simón–Sixsmith.
For Corollary 4.6, disjoint exponential images of compact segments directly
give distinct global maximum-modulus points once all segment maxima agree.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set

universe u

/-- Count exact maximum-modulus points using compact segments with disjoint
exponential images and a strict upper bound on the rest of the circle. -/
theorem count_equal_compact_segments {ι : Type u} [Fintype ι]
    (f : C(ℂ, ℂ)) (x : ℝ) (K : ι → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i)) (hne : ∀ i, (K i).Nonempty)
    (hvertical : ∀ i z, z ∈ K i → z.re = x)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Complex.exp '' K i) (Complex.exp '' K j))
    {B L : ℝ} (hBL : B < L)
    (houtside : ∀ w : ℂ, ‖w‖ = Real.exp x →
      w ∉ ⋃ i, Complex.exp '' K i → ‖f w‖ ≤ B)
    (hequal : ∀ i, compactMaximum (logModulus f) (K i) = L) :
    (Fintype.card ι : ℕ∞) ≤ ν f (Real.exp x) := by
  classical
  have hchoose (i : ι) : ∃ z ∈ K i, logModulus f z = L := by
    obtain ⟨z, hz, hmax⟩ := exists_compactMaximum (hcompact i) (hne i)
      (continuous_logModulus f).continuousOn
    exact ⟨z, hz, hmax.trans (hequal i)⟩
  choose z hz hmax using hchoose
  let p : ι → ℂ := fun i => Complex.exp (z i)
  have hp : Function.Injective p := by
    intro i j hij
    by_contra hneij
    have hpi : p i ∈ Complex.exp '' K i := ⟨z i, hz i, rfl⟩
    have hpj : p i ∈ Complex.exp '' K j := ⟨z j, hz j, hij.symm⟩
    exact disjoint_left.mp (hdisjoint i j hneij) hpi hpj
  have hbound (w : ℂ) (hw : ‖w‖ = Real.exp x) : ‖f w‖ ≤ L := by
    by_cases hwin : w ∈ ⋃ i, Complex.exp '' K i
    · obtain ⟨i, v, hv, rfl⟩ := mem_iUnion.mp hwin
      calc
        ‖f (Complex.exp v)‖ ≤ compactMaximum (logModulus f) (K i) :=
          le_compactMaximum (hcompact i) (continuous_logModulus f).continuousOn hv
        _ = L := hequal i
    · exact (houtside w hw hwin).trans hBL.le
  have hmem (i : ι) : p i ∈ maximumPoints f (Real.exp x) := by
    refine ⟨?_, ?_⟩
    · dsimp [p]
      rw [Complex.norm_exp, hvertical i (z i) (hz i)]
    · intro w hw
      change ‖f w‖ ≤ logModulus f (z i)
      rw [hmax i]
      exact hbound w hw
  have hsubset : range p ⊆ maximumPoints f (Real.exp x) := by
    rintro _ ⟨i, rfl⟩
    exact hmem i
  change (Fintype.card ι : ℕ∞) ≤ (maximumPoints f (Real.exp x)).encard
  calc
    (Fintype.card ι : ℕ∞) = (range p).encard := by
      rw [hp.encard_range, ENat.card_eq_coe_fintype_card]
    _ ≤ _ := encard_le_encard hsubset

#print axioms count_equal_compact_segments

end MaxModulusPoints.Construction

namespace MaxModulusPoints.Blueprint.Packages

open Set

/-- Simultaneous zeros with the face signs of Pardo-Simón–Sixsmith, Lemma 2.4. -/
theorem shooting_proof (a b : GateIndex → ℝ) (hab : ∀ i, a i < b i)
    (φ : GateIndex → ParameterBox a b → ℝ)
    (hcontinuous : ∀ i, Continuous (φ i))
    (hlower : ∀ i δ, (δ i : ℝ) = a i → 0 ≤ φ i δ)
    (hupper : ∀ i δ, (δ i : ℝ) = b i → φ i δ ≤ 0) :
    ∃ δ, ∀ i, φ i δ = 0 :=
  Construction.infinite_box_shooting Construction.finiteBoxFixedPoint
    a b (fun i => (hab i).le) φ hcontinuous hlower hupper

/-- Equal compact-slice maxima give the exact global count in Corollary 4.6. -/
theorem global_maxima_proof (C : ShootingFamily) (δ : ParameterBox C.lower C.upper)
    (hequal : ∀ i : GateIndex,
      sliceMaximum (C.segment i.1 (some (i.2, true))) (C.F δ) =
        sliceMaximum (C.segment i.1 none) (C.F δ)) :
    ∀ n, ((2 * (n + 1) + 1 : ℕ) : ℕ∞) ≤ ν (C.F δ) (Real.exp (C.x n)) := by
  intro n
  let f : C(ℂ, ℂ) := ⟨C.F δ, (C.entire δ).continuous⟩
  have hall (i : SliceIndex n) :
      Construction.compactMaximum (Construction.logModulus f) (C.segment n i) =
        sliceMaximum (C.segment n none) (C.F δ) := by
    change sliceMaximum (C.segment n i) (C.F δ) = _
    rcases i with _ | ⟨m, j⟩
    · rfl
    · cases j
      · exact (C.reflected_maxima δ n m).trans (hequal ⟨n, m⟩)
      · exact hequal ⟨n, m⟩
  have hcount := Construction.count_equal_compact_segments f (C.x n) (C.segment n)
    (C.compact_segment n) (C.nonempty_segment n) (C.vertical_segment n)
    (C.disjoint_images n)
    (lt_of_lt_of_le C.ceiling_lt_floor (C.passage_lower δ n))
    (C.outside_upper δ n) hall
  simpa [f, SliceIndex, Fintype.card_prod, Nat.add_comm, mul_comm] using hcount

#print axioms shooting_proof
#print axioms global_maxima_proof

end MaxModulusPoints.Blueprint.Packages
