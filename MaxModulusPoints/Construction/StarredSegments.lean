import MaxModulusPoints.Construction.CirclePoints
import MaxModulusPoints.Construction.Tract
/-!

# Fixed compact starred segments

The geometric part of Pardo-Simón–Sixsmith, Proposition 4.4: the full slices
are disjoint, their compact subsegments can be chosen symmetrically, and shortening
the deleted endpieces preserves uniform endpoint bounds and prescribed witnesses.
-/

namespace MaxModulusPoints.Construction

open Set
open scoped ComplexConjugate

noncomputable section

theorem chamberTop_le_bottom {n : ℕ} {m k : Fin (n + 1)} (hmk : m < k) :
    chamberTop n m ≤ chamberBottom n k := by
  have hmk' : (m.val : ℝ) + 1 ≤ k.val := by
    exact_mod_cast Nat.succ_le_of_lt hmk
  have hmul := mul_le_mul_of_nonneg_right hmk' (chamberWidth_pos n).le
  dsimp [chamberTop, chamberBottom]
  linarith

/-- Any two different slice intervals are separated, possibly by one common endpoint. -/
theorem sliceBounds_separated (n : ℕ) {i j : SliceIndex n} (hij : i ≠ j) :
    sliceTop n i ≤ sliceBottom n j ∨ sliceTop n j ≤ sliceBottom n i := by
  rcases i with _ | ⟨s, m⟩ <;> rcases j with _ | ⟨r, k⟩
  · exact (hij rfl).elim
  · cases r <;> dsimp only [sliceTop, sliceBottom]
    · exact Or.inl (chamber_bounds n k).1
    · exact Or.inr (neg_le_neg (chamber_bounds n k).1)
  · cases s <;> dsimp only [sliceTop, sliceBottom]
    · exact Or.inr (chamber_bounds n m).1
    · exact Or.inl (neg_le_neg (chamber_bounds n m).1)
  · have hm := (chamber_bounds n m).1
    have hk := (chamber_bounds n k).1
    have hp := passageHalfHeight_pos
    cases s <;> cases r <;> dsimp only [sliceTop, sliceBottom]
    · have hmk : m ≠ k := fun h => hij (congrArg (fun a => some (false, a)) h)
      rcases lt_or_gt_of_ne hmk with h | h
      · exact Or.inl (chamberTop_le_bottom h)
      · exact Or.inr (chamberTop_le_bottom h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · have hmk : m ≠ k := fun h => hij (congrArg (fun a => some (true, a)) h)
      rcases lt_or_gt_of_ne hmk with h | h
      · exact Or.inr (neg_le_neg (chamberTop_le_bottom h))
      · exact Or.inl (neg_le_neg (chamberTop_le_bottom h))

theorem fullSlice_pairwise (L : BlockLayout) (n : ℕ) :
    Pairwise (fun i j : SliceIndex n => Disjoint (fullSlice L n i) (fullSlice L n j)) := by
  intro i j hij
  rw [disjoint_left]
  intro z hzi hzj
  rcases sliceBounds_separated n hij with h | h
    <;> linarith [hzi.2.1, hzi.2.2, hzj.2.1, hzj.2.2]

/-- A passage cutoff is symmetric about the real axis; a pair of chambers
shares one cutoff. The inequalities ensure nondegenerate closed segments. -/
structure SliceCutoffs where
  passage : ℕ → ℝ
  passage_pos : ∀ n, 0 < passage n
  passage_small : ∀ n, passage n < passageHalfHeight
  chamber : GateIndex → ℝ
  chamber_pos : ∀ i, 0 < chamber i
  chamber_small : ∀ i, 2 * chamber i < chamberWidth i.1

def SliceCutoffs.amount (q : SliceCutoffs) (n : ℕ) : SliceIndex n → ℝ
  | none => q.passage n
  | some (_, m) => q.chamber ⟨n, m⟩

theorem SliceCutoffs.amount_pos (q : SliceCutoffs) (n : ℕ) (i : SliceIndex n) :
    0 < q.amount n i := by
  rcases i with _ | ⟨s, m⟩
  · exact q.passage_pos n
  · exact q.chamber_pos ⟨n, m⟩

theorem SliceCutoffs.amount_small (q : SliceCutoffs) (n : ℕ) (i : SliceIndex n) :
    2 * q.amount n i < sliceTop n i - sliceBottom n i := by
  rcases i with _ | ⟨s, m⟩
  · dsimp [SliceCutoffs.amount, sliceTop, sliceBottom]
    linarith [q.passage_small n]
  · have hsmall := q.chamber_small ⟨n, m⟩
    cases s <;> dsimp [SliceCutoffs.amount, sliceTop, sliceBottom, chamberBottom, chamberTop]
      <;> nlinarith

/-- A closed vertical segment strictly inside the corresponding open slice. -/
def starSlice (L : BlockLayout) (q : SliceCutoffs) (n : ℕ) (i : SliceIndex n) : Set ℂ :=
  {z | z.re = L.sample n ∧ sliceBottom n i + q.amount n i ≤ z.im ∧
    z.im ≤ sliceTop n i - q.amount n i}

theorem starSlice_subset_full (L : BlockLayout) (q : SliceCutoffs) (n : ℕ)
    (i : SliceIndex n) : starSlice L q n i ⊆ fullSlice L n i := by
  intro z hz
  have hpos := q.amount_pos n i
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

theorem starSlice_nonempty (L : BlockLayout) (q : SliceCutoffs) (n : ℕ)
    (i : SliceIndex n) : (starSlice L q n i).Nonempty := by
  have hsmall := q.amount_small n i
  refine ⟨⟨L.sample n, (sliceBottom n i + sliceTop n i) / 2⟩, rfl, ?_, ?_⟩
    <;> dsimp <;> linarith

theorem starSlice_compact (L : BlockLayout) (q : SliceCutoffs) (n : ℕ)
    (i : SliceIndex n) : IsCompact (starSlice L q n i) := by
  have heq : starSlice L q n i =
      (fun y : ℝ => (L.sample n : ℂ) + (y : ℂ) * Complex.I) ''
        Icc (sliceBottom n i + q.amount n i) (sliceTop n i - q.amount n i) := by
    ext z
    constructor
    · intro hz
      refine ⟨z.im, hz.2, ?_⟩
      simpa only [hz.1] using Complex.re_add_im z
    · rintro ⟨y, hy, rfl⟩
      exact ⟨by simp, by simpa using hy.1, by simpa using hy.2⟩
  rw [heq]
  exact isCompact_Icc.image (continuous_const.add (Complex.continuous_ofReal.mul_const _))

def reflectSlice (n : ℕ) : SliceIndex n → SliceIndex n
  | none => none
  | some (s, m) => some (!s, m)

theorem reflectSlice_bottom (n : ℕ) (i : SliceIndex n) :
    sliceBottom n (reflectSlice n i) = -sliceTop n i := by
  rcases i with _ | ⟨s, m⟩
  · rfl
  · cases s <;> simp [reflectSlice, sliceBottom, sliceTop]

theorem reflectSlice_top (n : ℕ) (i : SliceIndex n) :
    sliceTop n (reflectSlice n i) = -sliceBottom n i := by
  rcases i with _ | ⟨s, m⟩
  · simp [reflectSlice, sliceBottom, sliceTop]
  · cases s <;> simp [reflectSlice, sliceBottom, sliceTop]

theorem SliceCutoffs.amount_reflect (q : SliceCutoffs) (n : ℕ) (i : SliceIndex n) :
    q.amount n (reflectSlice n i) = q.amount n i := by
  rcases i with _ | ⟨s, m⟩ <;> rfl

/-- Reflection exchanges chamber stars and preserves the passage star. -/
theorem starSlice_reflect (L : BlockLayout) (q : SliceCutoffs) (n : ℕ)
    (i : SliceIndex n) : starSlice L q n (reflectSlice n i) = conj '' starSlice L q n i := by
  ext z
  constructor
  · intro hz
    have hz' : z.re = L.sample n ∧ -sliceTop n i + q.amount n i ≤ z.im ∧
        z.im ≤ -sliceBottom n i - q.amount n i := by
      simpa only [starSlice, mem_setOf_eq, reflectSlice_bottom, reflectSlice_top,
        SliceCutoffs.amount_reflect] using hz
    refine ⟨conj z, ?_, by simp⟩
    change (conj z).re = L.sample n ∧ sliceBottom n i + q.amount n i ≤ (conj z).im ∧
      (conj z).im ≤ sliceTop n i - q.amount n i
    simp only [Complex.conj_re, Complex.conj_im]
    exact ⟨hz'.1, by linarith [hz'.2.2], by linarith [hz'.2.1]⟩
  · rintro ⟨w, hw, rfl⟩
    simp only [starSlice, mem_setOf_eq, reflectSlice_bottom, reflectSlice_top,
      SliceCutoffs.amount_reflect, Complex.conj_re, Complex.conj_im]
    exact ⟨hw.1, by linarith [hw.2.2], by linarith [hw.2.1]⟩

/-- The concrete tract geometry supplies all the structural hypotheses of
the global maximum-point transfer theorem. -/
def concreteVerticalSlices (L : BlockLayout) (q : SliceCutoffs) (t : ℕ → ℝ)
    (δ : GateIndex → ℝ) (n : ℕ) :
    VerticalSlices (SliceIndex n) (chamberTract L t δ) (L.sample n) where
  slice := fullSlice L n
  star := starSlice L q n
  star_compact := starSlice_compact L q n
  star_nonempty := starSlice_nonempty L q n
  star_subset := starSlice_subset_full L q n
  slice_subset := fullSlice_subset_tract L t δ n
  slice_re := fun _ _ hz => hz.1
  slice_cover := by
    intro z hz hx
    obtain ⟨i, hi⟩ := (mem_chamberTract_at_sample L t δ n hx).mp hz
    exact ⟨i, hx, hi⟩
  star_disjoint := by
    intro i j hij
    rw [disjoint_left]
    intro z hzi hzj
    exact disjoint_left.mp (fullSlice_pairwise L n hij)
      (starSlice_subset_full L q n i hzi) (starSlice_subset_full L q n j hzj)

/-- A cutoff can be shortened to retain any prescribed interior witness. -/
theorem exists_witness_cutoff {a b y η : ℝ} (hay : a < y) (hyb : y < b) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε < b - a ∧ ε ≤ η ∧ a + ε ≤ y ∧ y ≤ b - ε := by
  let ε := min (η / 2) (min ((b - a) / 4) (min ((y - a) / 2) ((b - y) / 2)))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have h1 : ε ≤ η / 2 := min_le_left _ _
  have h2 : ε ≤ (b - a) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : ε ≤ (y - a) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : ε ≤ (b - y) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨ε, hε, by linarith, by linarith, by linarith, by linarith⟩

/-- Cutoffs exist below any positive uniform endpoint radii while retaining
one prescribed point in every upper chamber. Lower chambers use their reflections. -/
theorem exists_sliceCutoffs (L : BlockLayout) (ηP : ℕ → ℝ) (hηP : ∀ n, 0 < ηP n)
    (ηC : GateIndex → ℝ) (hηC : ∀ i, 0 < ηC i) (ξ : GateIndex → ℂ)
    (hξ : ∀ i, ξ i ∈ fullSlice L i.1 (some (false, i.2))) :
    ∃ q : SliceCutoffs, (∀ n, q.passage n ≤ ηP n) ∧
      (∀ i, q.chamber i ≤ ηC i) ∧
      ∀ i, ξ i ∈ starSlice L q i.1 (some (false, i.2)) := by
  have hchoose (i : GateIndex) : ∃ ε : ℝ, 0 < ε ∧ 2 * ε < chamberWidth i.1 ∧
      ε ≤ ηC i ∧ chamberBottom i.1 i.2 + ε ≤ (ξ i).im ∧
        (ξ i).im ≤ chamberTop i.1 i.2 - ε := by
    obtain ⟨ε, hpos, hsmall, hle, hlo, hhi⟩ :=
      exists_witness_cutoff (hξ i).2.1 (hξ i).2.2 (hηC i)
    have hlen : chamberTop i.1 i.2 - chamberBottom i.1 i.2 = chamberWidth i.1 := by
      dsimp [chamberTop, chamberBottom]
      ring
    exact ⟨ε, hpos, by simpa only [sliceTop, sliceBottom, hlen] using hsmall, hle, hlo, hhi⟩
  choose c hcpos hcsmall hcle hclo hchi using hchoose
  let q : SliceCutoffs :=
    { passage := fun n => min (passageHalfHeight / 2) (ηP n / 2)
      passage_pos := fun n => lt_min (half_pos passageHalfHeight_pos) (half_pos (hηP n))
      passage_small := fun n => lt_of_le_of_lt (min_le_left _ _) (half_lt_self passageHalfHeight_pos)
      chamber := c
      chamber_pos := hcpos
      chamber_small := hcsmall }
  refine ⟨q, ?_, hcle, ?_⟩
  · intro n
    exact (min_le_right _ _).trans (half_le_self (hηP n).le)
  · intro i
    exact ⟨(hξ i).1, hclo i, hchi i⟩

/-- On a full slice, precisely the points near an endpoint are deleted by trimming. -/
theorem not_mem_starSlice_iff (L : BlockLayout) (q : SliceCutoffs) (n : ℕ)
    (i : SliceIndex n) {z : ℂ} (hz : z ∈ fullSlice L n i) :
    z ∉ starSlice L q n i ↔ z.im < sliceBottom n i + q.amount n i ∨
      sliceTop n i - q.amount n i < z.im := by
  simp only [starSlice, mem_setOf_eq, hz.1, true_and, not_and_or, not_le]

/-- Uniform bounds near the endpoints remain valid after any smaller
cutoff is chosen. The parameter quantifier is preserved without a limiting argument. -/
theorem endpiece_bound_of_endpoint_bound {P : Type*} (L : BlockLayout) (q : SliceCutoffs)
    (n : ℕ) (i : SliceIndex n) (U : P → ℂ → ℝ) {η B : ℝ}
    (hsmall : q.amount n i ≤ η)
    (hbound : ∀ p z, z ∈ fullSlice L n i →
      (z.im < sliceBottom n i + η ∨ sliceTop n i - η < z.im) → U p z ≤ B) :
    ∀ p z, z ∈ fullSlice L n i \ starSlice L q n i → U p z ≤ B := by
  intro p z hz
  apply hbound p z hz.1
  rcases (not_mem_starSlice_iff L q n i hz.1).mp hz.2 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

#print axioms fullSlice_pairwise
#print axioms starSlice_compact
#print axioms starSlice_reflect
#print axioms concreteVerticalSlices
#print axioms exists_sliceCutoffs
#print axioms endpiece_bound_of_endpoint_bound

end

end MaxModulusPoints.Construction
