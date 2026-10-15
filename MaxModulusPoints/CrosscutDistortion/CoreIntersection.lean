import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.CrosscutDistortion.InverseRealAxis
import MaxModulusPoints.CrosscutDistortion.RealAxis
import MaxModulusPoints.CrosscutDistortion.Separation
import MaxModulusPoints.CrosscutDistortion.TunnelSlice
/-!
# Intersection of tunnel images with a real-coordinate interval

Each tunnel crosscut meets the vertical slab determined by a passage point
and a clean-slice point. When their image real parts occur in reversed
order, the slab reduces to the real coordinate of the passage image.
-/

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint

private theorem strip_segment_preimage {U : Set ℂ}
    (φ : ConformalEquivalence U strip) (u v : ℂ) (hu : u ∈ strip) (hv : v ∈ strip) :
    ∃ K : Set ℂ, IsPreconnected K ∧ K ⊆ U ∧ φ.invFun u ∈ K ∧ φ.invFun v ∈ K ∧
      ∀ q ∈ K, (φ.toFun q).re ∈ Icc (min u.re v.re) (max u.re v.re) := by
  have hconv : Convex ℝ strip := by
    simpa only [strip, abs_lt, ofPred_and] using
      (convex_halfSpace_im_gt (-(1 / 2 : ℝ))).inter
        (convex_halfSpace_im_lt (1 / 2 : ℝ))
  let f : ℝ → ℂ := fun t => (1 - t) • u + t • v
  have hf : Continuous f := by fun_prop
  have hfs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t ∈ strip :=
    hconv hu hv (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let g : ℝ → ℂ := fun t => φ.invFun (f t)
  have hg : ContinuousOn g (Icc 0 1) :=
    φ.inverse_holomorphic.continuousOn.comp hf.continuousOn hfs
  refine ⟨g '' Icc 0 1, isPreconnected_Icc.image g hg, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact φ.inverse_mapsTo (hfs t ht)
  · exact ⟨0, by norm_num, by simp [g, f]⟩
  · exact ⟨1, by norm_num, by simp [g, f]⟩
  · rintro _ ⟨t, ht, rfl⟩
    change (φ.toFun (φ.invFun (f t))).re ∈ _
    rw [φ.right_inv _ (hfs t ht)]
    have hreal := (convex_Icc (min u.re v.re) (max u.re v.re))
      ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
      (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    simpa [f] using hreal

private theorem tunnel_separates_real_endpoint (p : BlockParameters) (δ : GateIndex → ℝ)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    (haxis : ∀ x : ℝ, -2 < x → (x : ℂ) ∈ tract p δ)
    {K : Set ℂ} (hK : IsPreconnected K) (hKV : K ⊆ tract p δ)
    (r : ℝ) (hr : -2 < r) (hrK : (r : ℂ) ∈ K)
    {u : ℂ} (huK : u ∈ K)
    (hside : (u ∈ passageSlice p n ∧ s < r) ∨ (u ∈ cleanSlice p n ∧ r < s)) :
    ∃ q ∈ K, q.re = s ∧ |q.im| < p.tunnelHeight n / 2 := by
  have hposition : 0 ≤ blockPosition p n := by
    unfold blockPosition
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => le_trans zero_le_one (p.gap_ge_one k))
      (Nat.cast_nonneg n)
  have happend (c : ℝ) (hc : -2 < c) :
      IsPreconnected (K ∪ Complex.ofReal '' uIcc r c) ∧
        K ∪ Complex.ofReal '' uIcc r c ⊆ tract p δ := by
    constructor
    · exact IsPreconnected.union (r : ℂ) hrK ⟨r, left_mem_uIcc, rfl⟩ hK
        (isPreconnected_uIcc.image Complex.ofReal Complex.continuous_ofReal.continuousOn)
    · refine union_subset hKV ?_
      rintro _ ⟨t, ht, rfl⟩
      exact haxis t ((lt_min hr hc).trans_le ht.1)
  rcases hside with ⟨hu, hsr⟩ | ⟨hu, hrs⟩
  · let c : ℝ := blockPosition p n + 3 / 2
    have hc : -2 < c := by dsimp [c]; linarith
    have hsc : s < c := by dsimp [c]; linarith [hs.2]
    obtain ⟨q, hq, hcut⟩ := tunnel_slice_separates p δ n s hs
      (happend c hc).1 (happend c hc).2 (Or.inl huK) hu
      (Or.inr ⟨c, right_mem_uIcc, rfl⟩)
      (show (c : ℂ) ∈ cleanSlice p n from ⟨rfl, by simpa using half_pos Real.pi_pos⟩)
    rcases hq with hq | ⟨t, ht, rfl⟩
    · exact ⟨q, hq, hcut⟩
    · have hgt : s < t := (lt_min hsr hsc).trans_le ht.1
      have heq : t = s := hcut.1
      exact False.elim (hgt.ne heq.symm)
  · let c : ℝ := blockPosition p n + 1 / 4
    have hc : -2 < c := by dsimp [c]; linarith
    have hcs : c < s := by dsimp [c]; linarith [hs.1]
    have hcb : 0 < chamberBase := by
      dsimp [chamberBase]
      linarith [Real.pi_gt_three]
    obtain ⟨q, hq, hcut⟩ := tunnel_slice_separates p δ n s hs
      (happend c hc).1 (happend c hc).2
      (Or.inr ⟨c, right_mem_uIcc, rfl⟩)
      (show (c : ℂ) ∈ passageSlice p n from ⟨rfl, by simpa using hcb⟩)
      (Or.inl huK) hu
    rcases hq with hq | ⟨t, ht, rfl⟩
    · exact ⟨q, hq, hcut⟩
    · have hlt : t < s := ht.2.trans_lt (max_lt hrs hcs)
      have heq : t = s := hcut.1
      exact False.elim (hlt.ne heq)

/-- A normalized tunnel-crosscut image meets the slab from the passage image's
real coordinate to the larger of the passage and clean image coordinates. -/
theorem tunnel_image_meets_real_core (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    (w z : ℂ) (hw : w ∈ passageSlice p n) (hz : z ∈ cleanSlice p n)
    (hwV : w ∈ tract p δ) (hzV : z ∈ tract p δ) :
    ∃ q : ℂ, q.re = s ∧ |q.im| < p.tunnelHeight n / 2 ∧
      (φ.toFun q).re ∈ Icc (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re) := by
  have hforward := tract_strip_real_axis p δ φ hφ0 hφre hφim
  have hinverse := tract_strip_inverse_real_axis p δ φ hφ0 hφre hφim
  have haxis (x : ℝ) (hx : -2 < x) : (x : ℂ) ∈ tract p δ := (hforward.1 x hx).1
  have hreal_eq (x : ℝ) : ((φ.invFun x).re : ℂ) = φ.invFun x := by
    apply Complex.ext
    · simp
    · simpa using (hinverse.1 x).1.symm
  have hstrip (x : ℝ) : (x : ℂ) ∈ strip := by simp [strip]
  have hposition : 0 ≤ blockPosition p n := by
    unfold blockPosition
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => le_trans zero_le_one (p.gap_ge_one k))
      (Nat.cast_nonneg n)
  have hspos : -2 < s := by linarith [hs.1]
  have hφsreal : ((φ.toFun s).re : ℂ) = φ.toFun s := by
    apply Complex.ext
    · simp
    · simpa using (hforward.1 s hspos).2.symm
  have hinvs : φ.invFun ((φ.toFun s).re : ℂ) = (s : ℂ) := by
    rw [hφsreal, φ.left_inv _ (haxis s hspos)]
  by_cases horder : (φ.toFun w).re ≤ (φ.toFun z).re
  · obtain ⟨K, hK, hKV, hwK, hzK, hcoords⟩ := strip_segment_preimage φ
      (φ.toFun w) (φ.toFun z) (φ.mapsTo hwV) (φ.mapsTo hzV)
    rw [φ.left_inv _ hwV] at hwK
    rw [φ.left_inv _ hzV] at hzK
    obtain ⟨q, hq, hcut⟩ := tunnel_slice_separates p δ n s hs hK hKV hwK hw hzK hz
    exact ⟨q, hcut.1, hcut.2, by simpa only [min_eq_left horder] using hcoords q hq⟩
  · have hreverse : (φ.toFun z).re < (φ.toFun w).re := lt_of_not_ge horder
    have hmax : max (φ.toFun w).re (φ.toFun z).re = (φ.toFun w).re :=
      max_eq_left hreverse.le
    rw [hmax]
    by_cases hcentre : (φ.toFun s).re < (φ.toFun w).re
    · obtain ⟨K, hK, hKV, hwK, hrK, hcoords⟩ := strip_segment_preimage φ
        (φ.toFun w) ((φ.toFun w).re : ℂ) (φ.mapsTo hwV) (hstrip _)
      rw [φ.left_inv _ hwV] at hwK
      have hrgt : s < (φ.invFun ((φ.toFun w).re : ℂ)).re := by
        have hh := hinverse.2 hcentre
        dsimp only at hh
        simpa only [hinvs, Complex.ofReal_re] using hh
      have hrmem : (((φ.invFun ((φ.toFun w).re : ℂ)).re : ℝ) : ℂ) ∈ K := by
        rw [hreal_eq]
        exact hrK
      obtain ⟨q, hq, hcut⟩ := tunnel_separates_real_endpoint p δ n s hs haxis hK hKV
        _ (hinverse.1 _).2 hrmem hwK (Or.inl ⟨hw, hrgt⟩)
      have hh := hcoords q hq
      simp only [Complex.ofReal_re, min_self, max_self, mem_Icc] at hh
      have heq := le_antisymm hh.2 hh.1
      exact ⟨q, hcut.1, hcut.2, by simp [heq]⟩
    · obtain ⟨K, hK, hKV, hrK, hzK, hcoords⟩ := strip_segment_preimage φ
        ((φ.toFun z).re : ℂ) (φ.toFun z) (hstrip _) (φ.mapsTo hzV)
      rw [φ.left_inv _ hzV] at hzK
      have hrlt : (φ.invFun ((φ.toFun z).re : ℂ)).re < s := by
        have hh := hinverse.2 (hreverse.trans_le (le_of_not_gt hcentre))
        dsimp only at hh
        simpa only [hinvs, Complex.ofReal_re] using hh
      have hrmem : (((φ.invFun ((φ.toFun z).re : ℂ)).re : ℝ) : ℂ) ∈ K := by
        rw [hreal_eq]
        exact hrK
      obtain ⟨q, hq, hcut⟩ := tunnel_separates_real_endpoint p δ n s hs haxis hK hKV
        _ (hinverse.1 _).2 hrmem hzK (Or.inr ⟨hz, hrlt⟩)
      have hh := hcoords q hq
      simp only [Complex.ofReal_re, min_self, max_self, mem_Icc] at hh
      have heq := le_antisymm hh.2 hh.1
      let S : Set ℂ := {v : ℂ | v.re = s ∧ |v.im| < p.tunnelHeight n / 2}
      have hcomponent : connectedComponentIn (tract p δ ∩ {v : ℂ | v.re = s})
          (s : ℂ) = S := tunnel_vertical_component p δ n s hs
      have hSpre : IsPreconnected S := by
        rw [← hcomponent]
        exact isPreconnected_connectedComponentIn
      have hSV : S ⊆ tract p δ := by
        intro v hv
        rw [← hcomponent] at hv
        exact (connectedComponentIn_subset _ _ hv).1
      have hScentre : (s : ℂ) ∈ S := by simpa [S] using half_pos (p.tunnel_pos n)
      have hFcont : ContinuousOn (fun v : ℂ => (φ.toFun v).re) S :=
        Complex.continuous_re.comp_continuousOn (φ.holomorphic.continuousOn.mono hSV)
      obtain ⟨q', hq', heq'⟩ := hSpre.intermediate_value hcut hScentre hFcont
        ⟨by rw [heq]; exact hreverse.le, le_of_not_gt hcentre⟩
      exact ⟨q', hq'.1, hq'.2, by simp [heq']⟩

end MaxModulusPoints.CrosscutDistortion
