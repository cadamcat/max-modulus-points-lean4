module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.CompactEscape

/-!
# Lipschitz potentials in a strip slab

Two nonnegative potentials measure distance from the real axis and from
the strip boundary, truncated by the vertical sides of a slab.
Their values sum to one half on the central real-coordinate interval.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set Filter Blueprint
open scoped Topology

/-- The smaller signed horizontal distance to the slab's vertical sides. -/
def slabMargin (a b : ℝ) (z : ℂ) : ℝ :=
  min (z.re - (a - 1 / 2)) (b + 1 / 2 - z.re)

/-- Distance from the real axis, truncated by the slab's vertical sides. -/
def slabBasePotential (a b : ℝ) (z : ℂ) : ℝ :=
  max 0 (min |z.im| (slabMargin a b z))

/-- Distance from the strip boundary, truncated by the vertical sides. -/
def slabRoofPotential (a b : ℝ) (z : ℂ) : ℝ :=
  max 0 (min (1 / 2 - |z.im|) (slabMargin a b z))

/-- Both slab potentials are globally 1-Lipschitz for the Euclidean metric. -/
theorem slab_potentials_lipschitz (a b : ℝ) :
    LipschitzWith 1 (slabBasePotential a b) ∧
      LipschitzWith 1 (slabRoofPotential a b) := by
  have hre : LipschitzWith 1 Complex.re := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro z w
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs,
      ← Complex.sub_re]
      using Complex.abs_re_le_norm (z - w)
  have him : LipschitzWith 1 Complex.im := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro z w
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs,
      ← Complex.sub_im]
      using Complex.abs_im_le_norm (z - w)
  have habsim : LipschitzWith 1 (fun z : ℂ => |z.im|) := by
    simpa only [Function.comp_def, Real.dist_eq, sub_zero, one_mul] using
      (LipschitzWith.dist_left (0 : ℝ)).comp him
  have hsub (f : ℂ → ℝ) (hf : LipschitzWith 1 f) (c : ℝ) :
      LipschitzWith 1 (fun z => f z - c) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro z w
    calc
      dist (f z - c) (f w - c) = dist (f z) (f w) := by
        simp only [Real.dist_eq]
        congr 1
        ring
      _ ≤ _ := hf.dist_le_mul z w
  have hcsub (f : ℂ → ℝ) (hf : LipschitzWith 1 f) (c : ℝ) :
      LipschitzWith 1 (fun z => c - f z) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro z w
    calc
      dist (c - f z) (c - f w) = dist (f z) (f w) := by
        simp only [Real.dist_eq]
        rw [show c - f z - (c - f w) = -(f z - f w) by ring, abs_neg]
      _ ≤ _ := hf.dist_le_mul z w
  have hmargin : LipschitzWith 1 (slabMargin a b) := by
    change LipschitzWith 1 (fun z : ℂ => min (z.re - (a - 1 / 2)) (b + 1 / 2 - z.re))
    simpa only [max_self] using
      (hsub Complex.re hre (a - 1 / 2)).min (hcsub Complex.re hre (b + 1 / 2))
  constructor
  · change LipschitzWith 1 (fun z : ℂ => max 0 (min |z.im| (slabMargin a b z)))
    simpa only [max_self] using (habsim.min hmargin).const_max 0
  · change LipschitzWith 1 (fun z : ℂ => max 0 (min (1 / 2 - |z.im|) (slabMargin a b z)))
    simpa only [max_self] using
      ((hcsub (fun z : ℂ => |z.im|) habsim (1 / 2)).min hmargin).const_max 0

/-- The potentials are nonnegative at every complex point. -/
theorem slab_potentials_nonneg (a b : ℝ) (z : ℂ) :
    0 ≤ slabBasePotential a b z ∧ 0 ≤ slabRoofPotential a b z :=
  ⟨le_max_left _ _, le_max_left _ _⟩

/-- Both potentials vanish on and outside the vertical sides of the support slab. -/
theorem slab_potentials_zero_outside (a b : ℝ) (z : ℂ)
    (hz : z.re ≤ a - 1 / 2 ∨ b + 1 / 2 ≤ z.re) :
    slabBasePotential a b z = 0 ∧ slabRoofPotential a b z = 0 := by
  have hm : slabMargin a b z ≤ 0 := by
    rcases hz with hz | hz
    · exact (min_le_left _ _).trans (sub_nonpos.mpr hz)
    · exact (min_le_right _ _).trans (sub_nonpos.mpr hz)
  exact ⟨max_eq_left ((min_le_right _ _).trans hm),
    max_eq_left ((min_le_right _ _).trans hm)⟩

/-- The base potential vanishes on the whole real axis. -/
theorem slab_base_on_real (a b x : ℝ) : slabBasePotential a b (x : ℂ) = 0 := by
  unfold slabBasePotential
  simp only [Complex.ofReal_im, abs_zero]
  exact max_eq_left (min_le_left _ _)

/-- On the central interval in the closed strip, the potentials give the
distances to the real axis and the nearer horizontal strip boundary. -/
theorem slab_potentials_core_values_abs (a b : ℝ) (z : ℂ)
    (hz : z.re ∈ Icc a b) (hy : |z.im| ≤ 1 / 2) :
    slabBasePotential a b z = |z.im| ∧ slabRoofPotential a b z = 1 / 2 - |z.im| := by
  have hm : (1 / 2 : ℝ) ≤ slabMargin a b z :=
    le_min (by linarith [hz.1]) (by linarith [hz.2])
  constructor
  · rw [slabBasePotential, min_eq_left (hy.trans hm), max_eq_right (abs_nonneg _)]
  · rw [slabRoofPotential, min_eq_left (by linarith [abs_nonneg z.im]),
      max_eq_right (by linarith)]

/-- The core-value formulas on the closed upper half-strip. -/
theorem slab_potentials_core_values (a b : ℝ) (z : ℂ)
    (hz : z.re ∈ Icc a b) (hy : z.im ∈ Icc (0 : ℝ) (1 / 2)) :
    slabBasePotential a b z = z.im ∧ slabRoofPotential a b z = 1 / 2 - z.im := by
  have habs : |z.im| ≤ 1 / 2 := by simpa only [abs_of_nonneg hy.1] using hy.2
  simpa only [abs_of_nonneg hy.1] using slab_potentials_core_values_abs a b z hz habs

/-- Along a source-boundary approach, the roof potential tends
to zero because its positive level sets lie in compact subsets of the strip. -/
theorem slab_roof_tendsto_zero {ι : Type*} {l : Filter ι}
    (U : Set ℂ) (φ : ConformalEquivalence U strip) (u : ι → ℂ) (ζ : ℂ)
    (hu : ∀ᶠ i in l, u i ∈ U) (hζ : ζ ∉ U) (huz : Tendsto u l (𝓝 ζ)) (a b : ℝ) :
    Tendsto (fun i => slabRoofPotential a b (φ.toFun (u i))) l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall fun i => hc.trans_le (slab_potentials_nonneg a b _).2
  · intro ε hε
    let K : Set ℂ := {z : ℂ | z.re ∈ Icc (a - 1 / 2 + ε) (b + 1 / 2 - ε) ∧
      z.im ∈ Icc (-(1 / 2 - ε)) (1 / 2 - ε)}
    have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
    have hKS : K ⊆ strip := by
      intro z hz
      change |z.im| < 1 / 2
      have him := abs_le.mpr hz.2
      linarith
    have havoid := conformal_boundary_avoids_compact U strip φ u ζ hu hζ huz K hK hKS
    filter_upwards [havoid] with i hni
    by_contra hbad
    have hlarge : ε ≤ slabRoofPotential a b (φ.toFun (u i)) := le_of_not_gt hbad
    change ε ≤ max 0 (min (1 / 2 - |(φ.toFun (u i)).im|)
      (slabMargin a b (φ.toFun (u i)))) at hlarge
    have hmin : ε ≤ min (1 / 2 - |(φ.toFun (u i)).im|)
        (slabMargin a b (φ.toFun (u i))) := by
      rcases le_max_iff.mp hlarge with hzero | hmin
      · exact False.elim (hε.not_ge hzero)
      · exact hmin
    have hroof := (le_min_iff.mp hmin).1
    have hmargin := le_min_iff.mp (le_min_iff.mp hmin).2
    apply hni
    refine ⟨⟨?_, ?_⟩, abs_le.mp ?_⟩ <;> linarith [hmargin.1, hmargin.2]

end MaxModulusPoints.CrosscutDistortion
