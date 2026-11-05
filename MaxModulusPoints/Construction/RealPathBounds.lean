module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.StripClearance
public import MaxModulusPoints.Construction.StripCoordinates
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# Uniform bounds along finite real paths

The real-axis path estimate in Pardo-Simón–Sixsmith, Proposition 4.2,
uses the passage and tunnel openings. On each fixed finite interval,
only finitely many positive tunnel heights determine a clearance radius.
This gives bounds independent of every gate parameter.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set Metric

noncomputable section

theorem central_wall_mem_openings (p : Blueprint.BlockParameters) (n : ℕ) {z : ℂ}
    (hw : z ∈ frontier (Blueprint.passage p n) ∪ frontier (Blueprint.tunnel p n) ∪
      ⋃ m : Fin (n + 1), ⋃ j : Bool, frontier (Blueprint.chamber p ⟨n, m⟩ j))
    (hp : |z.im| < Blueprint.chamberBase) (ht : |z.im| < p.tunnelHeight n / 2) :
    z ∈ Blueprint.openings p n := by
  rcases hw with (hpass | htunnel) | hc
  · have h := frontier_absRectangle_bounds hpass
    rcases h.2.2.2 with ha | hb | hh
    · exact Or.inl ⟨ha, hp⟩
    · exact Or.inr (Or.inl ⟨hb, ht⟩)
    · linarith
  · have h := frontier_absRectangle_bounds htunnel
    rcases h.2.2.2 with ha | hb | hh
    · exact Or.inr (Or.inl ⟨ha, ht⟩)
    · exact Or.inr (Or.inr ⟨hb, ht⟩)
    · linarith
  · obtain ⟨m, hm⟩ := mem_iUnion.mp hc
    obtain ⟨j, hj⟩ := mem_iUnion.mp hm
    linarith [(chamber_frontier_bounds p ⟨n, m⟩ j hj).2.2]

theorem exists_finite_tunnel_clearance (p : Blueprint.BlockParameters) (N : ℕ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ k < N, r ≤ p.tunnelHeight k / 2 := by
  induction N with
  | zero => exact ⟨1 / 4, by norm_num, le_rfl, by simp⟩
  | succ N ih =>
    obtain ⟨r, hr, hrq, hrt⟩ := ih
    refine ⟨min r (p.tunnelHeight N / 2), lt_min hr (half_pos (p.tunnel_pos N)),
      (min_le_left _ _).trans hrq, ?_⟩
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact (min_le_left _ _).trans (hrt k hk)
    · subst k
      exact min_le_right _ _

/-- One physical clearance radius works along the entire finite interval
and for every gate function. -/
theorem exists_real_interval_clearance (p : Blueprint.BlockParameters) (R : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (δ : Blueprint.GateIndex → ℝ) (x : ℝ),
      x ∈ Icc (-1 : ℝ) R → ball (x : ℂ) r ⊆ Blueprint.tract p δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R + 1)
  obtain ⟨r, hr, hrq, hrt⟩ := exists_finite_tunnel_clearance p N
  refine ⟨r, hr, ?_⟩
  intro δ x hx z hz
  have hn : ‖z - (x : ℂ)‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
  have hreal := (Complex.abs_re_le_norm (z - (x : ℂ))).trans_lt hn
  have him := (Complex.abs_im_le_norm (z - (x : ℂ))).trans_lt hn
  simp only [Complex.sub_re, Complex.ofReal_re] at hreal
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  have hpass : |z.im| < Blueprint.chamberBase := by
    dsimp [Blueprint.chamberBase]
    linarith [Real.pi_gt_three]
  by_cases hw : z ∈ Blueprint.walls p
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hw
    have hkN : k < N := by
      by_contra hnot
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast Nat.le_of_not_gt hnot
      have hbase := (blockParametersLayout p).base_lower k
      change 2 * (k : ℝ) ≤ Blueprint.blockPosition p k at hbase
      have hs := (block_wall_support p k hk).1
      linarith [(abs_lt.mp hreal).2, hx.2, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have ht : |z.im| < p.tunnelHeight k / 2 := him.trans_le (hrt k hkN)
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨k, central_wall_mem_openings p k hk hpass ht⟩))
  · refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, hw⟩)
    · linarith [(abs_lt.mp hreal).1, hx.1]
    · linarith [Real.pi_gt_three]

def realSegment (x t : ℝ) : ℂ := ((-1 + (x + 1) * t : ℝ) : ℂ)

theorem hasDerivAt_realSegment (x t : ℝ) :
    HasDerivAt (realSegment x) ((x + 1 : ℝ) : ℂ) t := by
  simpa only [realSegment, mul_one, id_eq] using!
    (((hasDerivAt_id t).const_mul (x + 1)).const_add (-1)).ofReal_comp

theorem realSegment_endpoints (x : ℝ) :
    realSegment x 0 = -1 ∧ realSegment x 1 = (x : ℂ) := by
  simp [realSegment]

/-- A fixed finite real interval has a common strip-coordinate bound for
all gate parameters and all normalized conformal maps. -/
theorem uniform_real_strip_bound (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) {R : ℝ} (hR : -1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : Blueprint.GateIndex → ℝ)
      (G : Blueprint.LogModel (Blueprint.tract p δ)) (x : ℝ), x ∈ Icc (-1 : ℝ) R →
      ‖(stripCoordinates ψ G).toFun (x : ℂ)‖ ≤ C := by
  obtain ⟨r, hr, hclear⟩ := exists_real_interval_clearance p R
  let C := ((128 * Real.pi / r) * (R + 1)) / 2
  have hV : 0 ≤ R + 1 := by linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro δ G x hx
  let φ := stripCoordinates ψ G
  let α := realSegment x
  have hsegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      -1 + (x + 1) * t ∈ Icc (-1 : ℝ) R := by
    have hx1 : 0 ≤ x + 1 := by linarith [hx.1]
    exact ⟨by nlinarith [mul_nonneg hx1 ht.1],
      by nlinarith [mul_le_mul_of_nonneg_left ht.2 hx1, hx.2]⟩
  have hinj : InjOn φ.toFun (Blueprint.tract p δ) := by
    intro z hz w hw he
    calc
      z = φ.invFun (φ.toFun z) := (φ.left_inv z hz).symm
      _ = φ.invFun (φ.toFun w) := congrArg φ.invFun he
      _ = w := φ.left_inv w hw
  have hzero : φ.toFun (α 0) = 0 := by
    change φ.toFun (realSegment x 0) = 0
    rw [(realSegment_endpoints x).1]
    exact (stripCoordinates_normalized ψ G).1
  have hend : α 1 = (x : ℂ) := (realSegment_endpoints x).2
  have hstart : (φ.toFun (α 0)).im = 0 := by rw [hzero]; rfl
  have hspeed (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : ‖deriv α t‖ ≤ R + 1 := by
    rw [(hasDerivAt_realSegment x t).deriv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hx.1] : 0 ≤ x + 1)]
    linarith [hx.2]
  have hc := strip_map_curve_confinement hr hV φ.holomorphic hinj φ.mapsTo
    (fun t ht => hclear δ _ (hsegment t ht))
    (fun t _ => (hasDerivAt_realSegment x t).differentiableAt) hspeed hstart
  have h := hc (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hb := mem_closedBall_zero_iff.mp h.1
  change ‖φ.toFun (α 1) - ((φ.toFun (α 0)).re : ℂ)‖ ≤ C at hb
  simpa only [hend, hzero, Complex.zero_re, Complex.ofReal_zero,
    sub_zero] using hb

/-- The strip growth estimate turns the preceding compact real-path bound
into one real-part bound for the original conformal maps. -/
theorem uniform_real_value_bound (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) {R : ℝ} (hR : -1 ≤ R) :
    ∃ A : ℝ, 0 < A ∧ ∀ (δ : Blueprint.GateIndex → ℝ)
      (G : Blueprint.LogModel (Blueprint.tract p δ)) (x : ℝ), x ∈ Icc (-1 : ℝ) R →
      (G.toFun (x : ℂ)).re ≤ A := by
  obtain ⟨C, hC, hbound⟩ := uniform_real_strip_bound ψ p hR
  refine ⟨Real.exp (ψ.upperRate * C), Real.exp_pos _, ?_⟩
  intro δ G x hx
  let φ := stripCoordinates ψ G
  have hxmem : (x : ℂ) ∈ Blueprint.tract p δ := real_mem_tract p δ (by linarith [hx.1])
  have hφ := φ.mapsTo hxmem
  have he : ψ.toFun (φ.toFun (x : ℂ)) = G.toFun (x : ℂ) :=
    ψ.right_inv _ (G.mapsTo hxmem)
  have hvert := ψ.vertical_maximum ((φ.toFun (x : ℂ)).re) ((φ.toFun (x : ℂ)).im) hφ
  simp only [Complex.re_add_im, he] at hvert
  have hcoord : (φ.toFun (x : ℂ)).re ≤ C :=
    (Complex.re_le_norm _).trans (hbound δ G x hx)
  have hmono := (strip_real_strictMono ψ).monotone hcoord
  have hgrowth := (ψ.growth 0 C hC).2
  simp only [zero_add, Complex.ofReal_zero, ψ.base_value, Complex.one_re, mul_one] at hgrowth
  exact hvert.trans (hmono.trans hgrowth)

#print axioms exists_real_interval_clearance
#print axioms uniform_real_strip_bound
#print axioms uniform_real_value_bound

end

end MaxModulusPoints.Construction
