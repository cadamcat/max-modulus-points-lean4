module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Construction.LiteralSlices
public import MaxModulusPoints.Construction.Maxima
public import MaxModulusPoints.Construction.OpenChamberGeometry
public import MaxModulusPoints.Construction.OpenChamberLocalization
public import MaxModulusPoints.Construction.StarredSegments
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# Compact segments indexed by passage and chamber labels

The fixed starred segments satisfy the geometric fields of the shooting
family. The label convention here agrees with the paired-gate indices:
`true` selects an upper chamber and `false` its reflection.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set
open scoped ComplexConjugate

noncomputable section

def sliceLabelEquiv (n : ℕ) : Blueprint.SliceIndex n ≃ SliceIndex n where
  toFun
    | none => none
    | some (m, j) => some (!j, m)
  invFun
    | none => none
    | some (j, m) => some (m, !j)
  left_inv := by
    rintro (_ | ⟨m, j⟩)
    · rfl
    · cases j <;> rfl
  right_inv := by
    rintro (_ | ⟨j, m⟩)
    · rfl
    · cases j <;> rfl

def familySegment (p : Blueprint.BlockParameters) (q : SliceCutoffs) (n : ℕ)
    (i : Blueprint.SliceIndex n) : Set ℂ :=
  starSlice (blockParametersLayout p) q n (sliceLabelEquiv n i)

theorem familySegment_compact (p : Blueprint.BlockParameters) (q : SliceCutoffs)
    (n : ℕ) (i : Blueprint.SliceIndex n) : IsCompact (familySegment p q n i) :=
  starSlice_compact _ _ _ _

theorem familySegment_nonempty (p : Blueprint.BlockParameters) (q : SliceCutoffs)
    (n : ℕ) (i : Blueprint.SliceIndex n) : (familySegment p q n i).Nonempty :=
  starSlice_nonempty _ _ _ _

theorem familySegment_vertical (p : Blueprint.BlockParameters) (q : SliceCutoffs)
    (n : ℕ) (i : Blueprint.SliceIndex n) {z : ℂ} (hz : z ∈ familySegment p q n i) :
    z.re = Blueprint.slicePosition p n := hz.1

/-- Distinct compact slices remain disjoint after exponentiation. -/
theorem starSlice_disjoint_exp_images (L : BlockLayout) (q : SliceCutoffs)
    (n : ℕ) {i j : SliceIndex n} (hij : i ≠ j) :
    Disjoint (Complex.exp '' starSlice L q n i) (Complex.exp '' starSlice L q n j) := by
  rw [disjoint_left]
  rintro w ⟨z, hz, rfl⟩ ⟨v, hv, he⟩
  have hzf := starSlice_subset_full L q n i hz
  have hvf := starSlice_subset_full L q n j hv
  have hbz := slice_bounds n i
  have hbv := slice_bounds n j
  have hzeqv : z = v := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by linarith [hzf.2.1, hbz.2.1, Real.pi_pos])
    (by linarith [hzf.2.2, hbz.2.2, Real.pi_pos])
    (by linarith [hvf.2.1, hbv.2.1, Real.pi_pos])
    (by linarith [hvf.2.2, hbv.2.2, Real.pi_pos]) he.symm
  subst v
  exact Set.disjoint_left.mp (fullSlice_pairwise L n hij) hzf hvf

theorem familySegment_disjoint_images (p : Blueprint.BlockParameters) (q : SliceCutoffs)
    (n : ℕ) {i j : Blueprint.SliceIndex n} (hij : i ≠ j) :
    Disjoint (Complex.exp '' familySegment p q n i) (Complex.exp '' familySegment p q n j) :=
  starSlice_disjoint_exp_images _ _ _ ((sliceLabelEquiv n).injective.ne hij)

theorem familySegment_reflected_maxima (p : Blueprint.BlockParameters) (q : SliceCutoffs)
    (f : ℂ → ℂ) (hsym : ∀ z, f (star z) = star (f z))
    (n : ℕ) (m : Fin (n + 1)) :
    Blueprint.sliceMaximum (familySegment p q n (some (m, false))) f =
      Blueprint.sliceMaximum (familySegment p q n (some (m, true))) f := by
  change compactMaximum (logModulus f) (starSlice (blockParametersLayout p) q n (some (true, m))) =
    compactMaximum (logModulus f) (starSlice (blockParametersLayout p) q n (some (false, m)))
  rw [show starSlice (blockParametersLayout p) q n (some (true, m)) =
      conj '' starSlice (blockParametersLayout p) q n (some (false, m)) from
    starSlice_reflect _ _ _ (some (false, m))]
  exact logarithmicMaximum_conj f (by simpa only [Complex.star_def] using hsym) _

theorem familySegment_exp_union (p : Blueprint.BlockParameters) (q : SliceCutoffs) (n : ℕ) :
    (⋃ i : Blueprint.SliceIndex n, Complex.exp '' familySegment p q n i) =
      ⋃ i : SliceIndex n, Complex.exp '' starSlice (blockParametersLayout p) q n i := by
  ext w
  constructor
  · intro hw
    obtain ⟨i, hi⟩ := mem_iUnion.mp hw
    exact mem_iUnion.mpr ⟨sliceLabelEquiv n i, hi⟩
  · intro hw
    obtain ⟨i, hi⟩ := mem_iUnion.mp hw
    refine mem_iUnion.mpr ⟨(sliceLabelEquiv n).symm i, ?_⟩
    simpa only [familySegment, Equiv.apply_symm_apply] using hi

theorem upperChamberCentre_mem_fullSlice (p : Blueprint.BlockParameters) (i : GateIndex) :
    upperChamberCentre p i ∈ fullSlice (blockParametersLayout p) i.1 (some (false, i.2)) := by
  refine ⟨rfl, ?_, ?_⟩
  · change chamberBottom i.1 i.2 < upperChamberHeight i
    dsimp [upperChamberHeight]
    linarith [chamberWidth_pos i.1]
  · change upperChamberHeight i < chamberTop i.1 i.2
    dsimp [upperChamberHeight, chamberBottom, chamberTop]
    linarith [chamberWidth_pos i.1]

#print axioms familySegment_disjoint_images
#print axioms familySegment_reflected_maxima
#print axioms familySegment_exp_union

end

end MaxModulusPoints.Construction
