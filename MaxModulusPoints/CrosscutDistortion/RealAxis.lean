module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.TractSymmetry

/-!
# Real-axis orientation of normalized tract maps

The real interval to the right of `-2` remains in the tract. A normalized
tract-to-strip equivalence is real and strictly increasing on this interval.
-/


@[expose] public section

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint
open scoped Topology

/-- The real axis lies in the tract to the right of its left endpoint, and
the positive derivative normalization orients its real image increasingly. -/
theorem tract_strip_real_axis (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0) :
    (∀ x : ℝ, -2 < x → (x : ℂ) ∈ tract p δ ∧ (φ.toFun x).im = 0) ∧
      StrictMonoOn (fun x : ℝ => (φ.toFun x).re) (Ioi (-2)) := by
  have hcb : 0 < chamberBase := by
    dsimp [chamberBase]
    linarith [Real.pi_gt_three]
  have hheight (n : ℕ) : 0 < p.tunnelHeight n / 2 := half_pos (p.tunnel_pos n)
  have hrealmem (x : ℝ) (hx : -2 < x) : (x : ℂ) ∈ tract p δ := by
    have hreal_front (l r h : ℝ) (hh : 0 < h)
        (hfront : (x : ℂ) ∈ frontier {q : ℂ | l ≤ q.re ∧ q.re ≤ r ∧ |q.im| ≤ h}) :
        x = l ∨ x = r := by
      have hclosed : IsClosed {q : ℂ | l ≤ q.re ∧ q.re ≤ r ∧ |q.im| ≤ h} :=
        (isClosed_le continuous_const Complex.continuous_re).inter
          ((isClosed_le Complex.continuous_re continuous_const).inter
            (isClosed_le Complex.continuous_im.abs continuous_const))
      have hm := hclosed.frontier_subset hfront
      by_cases hxl : x = l
      · exact Or.inl hxl
      by_cases hxr : x = r
      · exact Or.inr hxr
      have hl : l < x := lt_of_le_of_ne hm.1 (Ne.symm hxl)
      have hr : x < r := lt_of_le_of_ne hm.2.1 hxr
      have hint : (x : ℂ) ∈ interior {q : ℂ | l ≤ q.re ∧ q.re ≤ r ∧ |q.im| ≤ h} := by
        refine mem_interior.mpr
          ⟨{q : ℂ | l < q.re ∧ q.re < r ∧ |q.im| < h},
            (fun _ hq => ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩), ?_, ?_⟩
        · exact (isOpen_lt continuous_const Complex.continuous_re).inter
            ((isOpen_lt Complex.continuous_re continuous_const).inter
              (isOpen_lt Complex.continuous_im.abs continuous_const))
        · exact ⟨hl, hr, by simpa using hh⟩
      exact False.elim ((mem_frontier_iff_notMem_interior hm).mp hfront hint)
    by_cases ho : ∃ n, (x : ℂ) ∈ openings p n
    · exact Or.inl (Or.inr (mem_iUnion.mpr ho))
    refine Or.inl (Or.inl ⟨⟨hx, ?_⟩, ?_⟩)
    · simpa using half_pos Real.pi_pos
    · intro hw
      rcases mem_iUnion.mp hw with ⟨n, hn⟩
      rcases hn with (hn | hn) | hn
      · rcases hreal_front (blockPosition p n) (blockPosition p n + 1 / 2)
          chamberBase hcb hn with heq | heq
        · exact ho ⟨n, Or.inl ⟨heq, by simpa using hcb⟩⟩
        · exact ho ⟨n, Or.inr (Or.inl ⟨heq, by simpa using hheight n⟩)⟩
      · rcases hreal_front (blockPosition p n + 1 / 2) (blockPosition p n + 1)
          (p.tunnelHeight n / 2) (hheight n) hn with heq | heq
        · exact ho ⟨n, Or.inr (Or.inl ⟨heq, by simpa using hheight n⟩)⟩
        · exact ho ⟨n, Or.inr (Or.inr ⟨heq, by simpa using hheight n⟩)⟩
      · rcases mem_iUnion.mp hn with ⟨m, hm⟩
        rcases mem_iUnion.mp hm with ⟨j, hj⟩
        have hl : chamberBase + (m.val : ℝ) / ((n : ℝ) + 1) ≤ sideSign j * (x : ℂ).im :=
          closure_minimal (fun _ hq => hq.2.2.1)
            (isClosed_le continuous_const (continuous_const.mul Complex.continuous_im))
            (frontier_subset_closure hj)
        simp only [Complex.ofReal_im, mul_zero] at hl
        have hfrac : 0 ≤ (m.val : ℝ) / ((n : ℝ) + 1) := by positivity
        linarith
  have him (x : ℝ) (hx : -2 < x) : (φ.toFun x).im = 0 := by
    have hh := congrArg Complex.im
      (tract_strip_equivalence_conj p δ φ hφ0 hφre hφim (x : ℂ) (hrealmem x hx))
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_im] at hh
    linarith
  refine ⟨fun x hx => ⟨hrealmem x hx, him x hx⟩, ?_⟩
  let f : ℝ → ℝ := fun x => (φ.toFun x).re
  have hcontC : ContinuousOn (fun x : ℝ => φ.toFun x) (Ioi (-2)) :=
    φ.holomorphic.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun x hx => hrealmem x hx)
  have hcont : ContinuousOn f (Ioi (-2)) :=
    Complex.continuous_re.comp_continuousOn hcontC
  have hinj : InjOn f (Ioi (-2)) := by
    intro x hx y hy heq
    have he : φ.toFun x = φ.toFun y := Complex.ext heq (by rw [him x hx, him y hy])
    have hi := congrArg φ.invFun he
    simp only [φ.left_inv (x : ℂ) (hrealmem x hx),
      φ.left_inv (y : ℂ) (hrealmem y hy)] at hi
    exact_mod_cast hi
  have hφne : deriv φ.toFun (-1) ≠ 0 := by
    intro heq
    rw [heq] at hφre
    norm_num at hφre
  have hφd := differentiableAt_of_deriv_ne_zero hφne
  have hcomplex : HasDerivAt φ.toFun (deriv φ.toFun (-1)) ((-1 : ℝ) : ℂ) := by
    simpa using hφd.hasDerivAt
  have hfd : HasDerivAt f (deriv φ.toFun (-1)).re (-1 : ℝ) := hcomplex.real_of_complex
  intro x hx y hy hxy
  let a : ℝ := min x (-3 / 2)
  let b : ℝ := max y 0
  have hal : -2 < a := lt_min hx (by norm_num)
  have hab : a ≤ b := (min_le_left _ _).trans (hxy.le.trans (le_max_left _ _))
  have hsub : Icc a b ⊆ Ioi (-2) := fun t ht => hal.trans_le ht.1
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' hab (hcont.mono hsub) (hinj.mono hsub)
      with hm | hm
  · exact hm ⟨min_le_left _ _, hxy.le.trans (le_max_left _ _)⟩
      ⟨(min_le_left _ _).trans hxy.le, le_max_left _ _⟩ hxy
  · have hmem : Icc a b ∈ 𝓝 (-1 : ℝ) := Icc_mem_nhds
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (le_max_right _ _))
    have hnonpos : derivWithin f (Icc a b) (-1) ≤ 0 := hm.antitoneOn.derivWithin_nonpos
    rw [derivWithin_of_mem_nhds hmem, hfd.deriv] at hnonpos
    linarith

end MaxModulusPoints.CrosscutDistortion
