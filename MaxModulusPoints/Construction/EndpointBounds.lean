module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
public import MaxModulusPoints.Blueprint.Interfaces.BoundaryUpper
public import MaxModulusPoints.Blueprint.Interfaces.HalfDisc
public import MaxModulusPoints.Blueprint.Interfaces.HalfDiscBarriers
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.BoundaryLimits
public import MaxModulusPoints.Construction.ClosedGate
public import MaxModulusPoints.Construction.SliceWindows
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership
public import MaxModulusPoints.Construction.UniformLeftBound

/-!
# Uniform bounds on deleted slice endpieces

Pardo-Simón–Sixsmith, Proposition 4.4, uses fixed half-discs at slice
endpoints. The uniform left-region bound controls their interiors and
the removed horizontal walls have nonpositive boundary upper limits.
The resulting endpoint radii are independent of every gate parameter.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set
open scoped Topology

noncomputable section

theorem SliceWindow.uniform_lower_endpoint_bound
    (hbottleneck : Blueprint.BottleneckEstimates) (hhalf : Blueprint.HalfDiscBarriers)
    (ψ : Blueprint.StripMapData) {p : Blueprint.BlockParameters} {n : ℕ} {a b : ℝ}
    (W : SliceWindow p n a b) :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : Blueprint.GateIndex → ℝ),
      (∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i) →
      ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
      ∀ z : ℂ, z.re = Blueprint.slicePosition p n → a < z.im → z.im < a + η →
        (G.toFun z).re ≤ 1 := by
  let r := min (1 / 16 : ℝ) ((b - a) / 2)
  have hr : 0 < r := lt_min (by norm_num) (by linarith [W.height_pos])
  have hrx : r ≤ 1 / 16 := min_le_left _ _
  have hry : r ≤ (b - a) / 2 := min_le_right _ _
  let e : ℂ := ⟨Blueprint.slicePosition p n, a⟩
  let T : ℂ → ℂ := fun z => e + (r : ℂ) * z
  have hTdiff : Differentiable ℂ T := (differentiable_id.const_mul (r : ℂ)).const_add e
  have hTx (z : ℂ) (hz : ‖z‖ < 1) : |(T z).re - Blueprint.slicePosition p n| < 1 / 8 := by
    have hzr : |z.re| < 1 := (Complex.abs_re_le_norm z).trans_lt hz
    have heq : (T z).re - Blueprint.slicePosition p n = r * z.re := by simp [T, e]
    rw [heq, abs_mul, abs_of_pos hr]
    nlinarith
  have hTy (z : ℂ) (hz : z ∈ Blueprint.halfDisc) : a < (T z).im ∧ (T z).im < b := by
    have hzi : z.im < 1 := (le_abs_self z.im).trans_lt ((Complex.abs_im_le_norm z).trans_lt hz.1)
    have heq : (T z).im = a + r * z.im := by simp [T, e]
    rw [heq]
    constructor <;> nlinarith [hz.2, W.height_pos]
  obtain ⟨B, hB, hleft⟩ := uniform_left_value_bound hbottleneck ψ p (Blueprint.slicePosition p n + 1)
  obtain ⟨η₀, hη₀, hbarrier⟩ := hhalf B 1 hB (by norm_num)
  let η := r * min η₀ 1 / 2
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro δ hδ G z hx hlo hhi
  have hmap : MapsTo T Blueprint.halfDisc (Blueprint.tract p δ) := by
    intro w hw
    exact W.inside δ G (T w) (hTx w hw.1) (hTy w hw).1 (hTy w hw).2
  have hbound (w : ℂ) (hw : w ∈ Blueprint.halfDisc) : ((G.toFun ∘ T) w).re ≤ B := by
    apply hleft δ hδ G (T w) (hmap hw)
    linarith [(abs_lt.mp (hTx w hw.1)).2]
  have hboundary (ζ : ℂ) (hζ : ‖ζ‖ < 1) (him : ζ.im = 0) :
      Blueprint.BoundaryUpper Blueprint.halfDisc (G.toFun ∘ T) ζ 0 := by
    apply boundaryUpper_comp hTdiff.continuous.continuousAt.continuousWithinAt hmap
    apply logModel_boundaryUpper_of_not_mem G
    apply W.wall δ (fun i => (hδ i).2) G (T ζ) (hTx ζ hζ)
    exact Or.inl (by simp [T, e, him])
  let t := (z.im - a) / r
  have htpos : 0 < t := div_pos (sub_pos.mpr hlo) hr
  have ht : t < min η₀ 1 := by
    apply (div_lt_iff₀ hr).mpr
    have hmin : 0 < min η₀ 1 := lt_min hη₀ (by norm_num)
    dsimp [η] at hhi
    nlinarith
  let w : ℂ := (t : ℂ) * Complex.I
  have hwnorm : ‖w‖ = t := by
    simp [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hw : w ∈ Blueprint.halfDisc := by
    refine ⟨?_, ?_⟩
    · rw [hwnorm]
      exact ht.trans_le (min_le_right _ _)
    · simpa [w] using htpos
  have hTw : T w = z := by
    apply Complex.ext
    · simpa [T, e, w] using hx.symm
    · have htprod : r * t = z.im - a := by dsimp [t]; field_simp [hr.ne']
      simpa [T, e, w] using (show a + r * t = z.im by linarith)
  have h := hbarrier (G.toFun ∘ T) (G.holomorphic.comp hTdiff.differentiableOn hmap)
    hbound hboundary w hw (by rw [hwnorm]; exact ht.trans_le (min_le_left _ _))
  simpa only [Function.comp_apply, hTw] using h

theorem SliceWindow.uniform_endpoint_bound
    (hbottleneck : Blueprint.BottleneckEstimates) (hhalf : Blueprint.HalfDiscBarriers)
    (ψ : Blueprint.StripMapData) {p : Blueprint.BlockParameters} {n : ℕ} {a b : ℝ}
    (W : SliceWindow p n a b) :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : Blueprint.GateIndex → ℝ),
      (∀ i, 0 < δ i ∧ δ i ≤ Blueprint.gateUpper i) →
      ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
      ∀ z : ℂ, z.re = Blueprint.slicePosition p n → a < z.im → z.im < b →
        (z.im < a + η ∨ b - η < z.im) → (G.toFun z).re ≤ 1 := by
  obtain ⟨η₁, hη₁, hbottom⟩ := W.uniform_lower_endpoint_bound hbottleneck hhalf ψ
  obtain ⟨η₂, hη₂, htop⟩ := W.reflect.uniform_lower_endpoint_bound hbottleneck hhalf ψ
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  intro δ hδ G z hx hlo hhi hnear
  rcases hnear with hnear | hnear
  · exact hbottom δ hδ G z hx hlo (by linarith [min_le_left η₁ η₂])
  · have h := htop δ hδ G (star z) (by simpa using hx)
      (by simpa using neg_lt_neg hhi) (by
        simp only [Complex.star_def, Complex.conj_im]
        linarith [min_le_right η₁ η₂])
    have hzV := W.inside δ G z (by simp [hx]) hlo hhi
    rw [G.symmetric_map z hzV] at h
    simpa using h

/-- Each full passage or chamber slice has gate-independent endpoint radii. -/
theorem uniform_slice_endpoint_bound (hbottleneck : Blueprint.BottleneckEstimates)
    (hhalf : Blueprint.HalfDiscBarriers) (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (n : ℕ) (i : SliceIndex n) :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : Blueprint.GateIndex → ℝ),
      (∀ k, 0 < δ k ∧ δ k ≤ Blueprint.gateUpper k) →
      ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
      ∀ z ∈ fullSlice (blockParametersLayout p) n i,
        (z.im < sliceBottom n i + η ∨ sliceTop n i - η < z.im) → (G.toFun z).re ≤ 1 := by
  obtain ⟨η, hη, hbound⟩ := (fullSliceWindow p n i).uniform_endpoint_bound hbottleneck hhalf ψ
  exact ⟨η, hη, fun δ hδ G z hz hnear => hbound δ hδ G z hz.1 hz.2.1 hz.2.2 hnear⟩

#print axioms SliceWindow.uniform_lower_endpoint_bound
#print axioms SliceWindow.uniform_endpoint_bound
#print axioms uniform_slice_endpoint_bound

end

end MaxModulusPoints.Construction
