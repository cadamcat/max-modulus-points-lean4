import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.CrosscutDistortion.TunnelSlice
/-!
# Separation by a tunnel crosscut

Every connected subset of the chamber and gate tract that joins the passage
slice to the clean slice meets each central vertical tunnel segment.
-/

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint

/-- A central tunnel segment separates the passage and clean slices, expressed
as intersection with every preconnected set joining those slices. -/
theorem tunnel_slice_separates (p : BlockParameters) (δ : GateIndex → ℝ)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    {K : Set ℂ} (hK : IsPreconnected K) (hKV : K ⊆ tract p δ)
    {w z : ℂ} (hw : w ∈ K) (hwpassage : w ∈ passageSlice p n)
    (hz : z ∈ K) (hzclean : z ∈ cleanSlice p n) :
    ∃ q ∈ K, q.re = s ∧ |q.im| < p.tunnelHeight n / 2 := by
  let R : ℝ := blockPosition p n
  let a : ℝ := R + 1 / 2
  let H : ℝ := p.tunnelHeight n / 2
  have hsL : a < s := hs.1
  have hsU : s < R + 1 := hs.2
  have hH : 0 < H := half_pos (p.tunnel_pos n)
  have hHbase : H < chamberBase := by
    dsimp [H, chamberBase]
    linarith [Real.pi_gt_three, p.tunnel_le_quarter n]
  have hstep (k : ℕ) : blockPosition p k + 2 ≤ blockPosition p (k + 1) := by
    simp only [blockPosition, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    linarith [p.gap_ge_one (k + 1)]
  have hmono : Monotone (blockPosition p) :=
    monotone_nat_of_le_succ fun k => by linarith [hstep k]
  have hindex {t : ℝ} (htl : R ≤ t) (htu : t ≤ R + 1)
      (k : ℕ) (hkl : blockPosition p k ≤ t) (hku : t ≤ blockPosition p k + 1) :
      k = n := by
    rcases lt_trichotomy k n with hk | hk | hk
    · have hm := hmono (Nat.succ_le_of_lt hk)
      change blockPosition p n ≤ t at htl
      linarith [hstep k]
    · exact hk
    · have hm := hmono (Nat.succ_le_of_lt hk)
      change t ≤ blockPosition p n + 1 at htu
      linarith [hstep n]
  have hfront_re_le {T : Set ℂ} {q : ℂ} {c : ℝ} (hq : q ∈ T)
      (hT : T ⊆ {r : ℂ | r.re ≤ c}) (hqc : q.re = c) : q ∈ frontier T := by
    apply (mem_frontier_iff_notMem_interior hq).mpr
    intro hint
    have hm := interior_mono hT hint
    rw [Complex.interior_setOfPred_re_le] at hm
    exact (ne_of_lt hm) hqc
  have hfront_abs {T : Set ℂ} {q : ℂ} {c : ℝ} (hq : q ∈ T)
      (hT : T ⊆ {r : ℂ | |r.im| ≤ c}) (hqc : |q.im| = c) : q ∈ frontier T := by
    apply (mem_frontier_iff_notMem_interior hq).mpr
    intro hint
    have hm : q ∈ interior (Complex.im ⁻¹' Icc (-c) c) :=
      interior_mono (fun r hr => abs_le.mp (hT hr)) hint
    rw [Complex.interior_preimage_im, interior_Icc] at hm
    exact (ne_of_lt (abs_lt.mpr hm)) hqc
  have hwall_opening {q : ℂ} (hq : q ∈ tract p δ) (hwall : q ∈ walls p)
      (hql : R ≤ q.re) (hqu : q.re < R + 1) : q ∈ openings p n := by
    rcases hq with (hq | hq) | hq
    · exact False.elim (hq.2 hwall)
    · rcases mem_iUnion.mp hq with ⟨k, hk⟩
      have hbox : blockPosition p k ≤ q.re ∧ q.re ≤ blockPosition p k + 1 := by
        rcases hk with hk | hk | hk <;>
          exact ⟨by linarith [hk.1], by linarith [hk.1]⟩
      have hkn := hindex hql hqu.le k hbox.1 hbox.2
      subst k
      exact hk
    · rcases mem_iUnion.mp hq with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨j, hj⟩
      have hkn := hindex hql hqu.le i.1 (by linarith [hj.1]) (by linarith [hj.1])
      have heq : q.re = R + 1 := by simpa [hkn, R] using hj.1
      exact False.elim (hqu.ne heq)
  have hleft {q : ℂ} (hq : q ∈ tract p δ) (hqre : q.re = R) :
      |q.im| < chamberBase := by
    rcases hq with (hq | hq) | hq
    · by_contra hn
      have hy : chamberBase ≤ |q.im| := le_of_not_gt hn
      let u : ℝ := (|q.im| - chamberBase) * ((n : ℝ) + 1)
      have hN : 0 < (n : ℝ) + 1 := by positivity
      have hu0 : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hy) hN.le
      have huN : u < (n : ℝ) + 1 := by
        have hy1 : |q.im| - chamberBase < 1 := by
          dsimp [chamberBase]
          linarith [hq.1.2]
        simpa [u] using mul_lt_mul_of_pos_right hy1 hN
      have hm : Nat.floor u < n + 1 := by
        apply (Nat.floor_lt hu0).mpr
        simpa only [Nat.cast_add, Nat.cast_one] using huN
      let m : Fin (n + 1) := ⟨Nat.floor u, hm⟩
      have hlow : chamberBase + (m.val : ℝ) / ((n : ℝ) + 1) ≤ |q.im| := by
        have hdiv : (m.val : ℝ) / ((n : ℝ) + 1) ≤ |q.im| - chamberBase :=
          (div_le_iff₀ hN).mpr (Nat.floor_le hu0)
        linarith
      have hupp : |q.im| ≤ chamberBase + ((m.val : ℝ) + 1) / ((n : ℝ) + 1) := by
        have hdiv : |q.im| - chamberBase ≤ ((m.val : ℝ) + 1) / ((n : ℝ) + 1) :=
          (le_div_iff₀ hN).mpr (Nat.lt_floor_add_one u).le
        linarith
      obtain ⟨j, hj⟩ : ∃ j : Bool, sideSign j * q.im = |q.im| := by
        by_cases hy0 : 0 ≤ q.im
        · exact ⟨true, by simp [sideSign, abs_of_nonneg hy0]⟩
        · exact ⟨false, by simp [sideSign, abs_of_neg (lt_of_not_ge hy0)]⟩
      have hqch : q ∈ chamber p ⟨n, m⟩ j :=
        ⟨by change blockPosition p n ≤ q.re; linarith,
          by change q.re ≤ blockPosition p n + 1; linarith,
          by simpa [hj] using hlow, by simpa [hj] using hupp⟩
      have hqfront : q ∈ frontier (chamber p ⟨n, m⟩ j) := by
        apply (mem_frontier_iff_notMem_interior hqch).mpr
        intro hint
        have hm : q ∈ interior {r : ℂ | R ≤ r.re} :=
          interior_mono (fun r (hr : r ∈ chamber p ⟨n, m⟩ j) => hr.1) hint
        rw [Complex.interior_setOfPred_le_re] at hm
        exact (ne_of_lt hm) hqre.symm
      exact hq.2 (mem_iUnion.mpr ⟨n,
        Or.inr (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨j, hqfront⟩⟩)⟩)
    · rcases mem_iUnion.mp hq with ⟨k, hk⟩
      have hbox : blockPosition p k ≤ q.re ∧ q.re ≤ blockPosition p k + 1 := by
        rcases hk with hk | hk | hk <;>
          exact ⟨by linarith [hk.1], by linarith [hk.1]⟩
      have hkn := hindex (by linarith) (by linarith) k hbox.1 hbox.2
      subst k
      rcases hk with hk | hk | hk
      · exact hk.2
      · change q.re = R + 1 / 2 ∧ _ at hk
        linarith [hk.1]
      · change q.re = R + 1 ∧ _ at hk
        linarith [hk.1]
    · rcases mem_iUnion.mp hq with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨j, hj⟩
      have hkn := hindex (by linarith) (by linarith) i.1
        (by linarith [hj.1]) (by linarith [hj.1])
      have heq : q.re = R + 1 := by simpa [hkn, R] using hj.1
      linarith
  have hpassage_top {q : ℂ} (hq : q ∈ tract p δ)
      (hql : R ≤ q.re) (hqu : q.re ≤ a) (hqim : |q.im| = chamberBase) : False := by
    have hm : q ∈ passage p n := ⟨hql, hqu, hqim.le⟩
    have hf := hfront_abs hm (fun r (hr : r ∈ passage p n) => hr.2.2) hqim
    have ho := hwall_opening hq (mem_iUnion.mpr ⟨n, Or.inl (Or.inl hf)⟩)
      hql (by dsimp [a] at hqu; linarith)
    rcases ho with ho | ho | ho
    · linarith [ho.2]
    · change _ ∧ |q.im| < H at ho
      linarith [ho.2]
    · change q.re = R + 1 ∧ _ at ho
      dsimp [a] at hqu
      linarith [ho.1]
  have hpassage_right {q : ℂ} (hq : q ∈ tract p δ) (hqre : q.re = a)
      (hqlo : H ≤ |q.im|) (hqup : |q.im| ≤ chamberBase) : False := by
    have hm : q ∈ passage p n :=
      ⟨by dsimp [a] at hqre; linarith, hqre.le, hqup⟩
    have hf := hfront_re_le hm (fun r (hr : r ∈ passage p n) => hr.2.1) hqre
    have ho := hwall_opening hq (mem_iUnion.mpr ⟨n, Or.inl (Or.inl hf)⟩)
      (by dsimp [a] at hqre; linarith) (by dsimp [a] at hqre; linarith)
    rcases ho with ho | ho | ho
    · change q.re = R ∧ _ at ho
      dsimp [a] at hqre
      linarith [ho.1]
    · change _ ∧ |q.im| < H at ho
      linarith [ho.2]
    · change q.re = R + 1 ∧ _ at ho
      dsimp [a] at hqre
      linarith [ho.1]
  have htunnel_top {q : ℂ} (hq : q ∈ tract p δ)
      (hql : a ≤ q.re) (hqu : q.re ≤ s) (hqim : |q.im| = H) : False := by
    have hm : q ∈ tunnel p n := ⟨hql, by linarith, hqim.le⟩
    have hf := hfront_abs hm (fun r (hr : r ∈ tunnel p n) => hr.2.2) hqim
    have ho := hwall_opening hq (mem_iUnion.mpr ⟨n, Or.inl (Or.inr hf)⟩)
      (by dsimp [a] at hql; linarith) (by linarith)
    rcases ho with ho | ho | ho
    · change q.re = R ∧ _ at ho
      dsimp [a] at hql
      linarith [ho.1]
    · change _ ∧ |q.im| < H at ho
      linarith [ho.2]
    · change q.re = R + 1 ∧ _ at ho
      linarith [ho.1]
  let F : ℂ → ℝ := fun q => min (q.re - R)
    (min (max (q.re - a) (|q.im| - chamberBase)) (max (q.re - s) (|q.im| - H)))
  have hFcont : Continuous F := by dsimp [F]; fun_prop
  have hzero {q : ℂ} (hq : q ∈ tract p δ) (hFq : F q = 0) :
      q.re = s ∧ |q.im| < H := by
    have hnonneg : 0 ≤ q.re - R ∧
        0 ≤ max (q.re - a) (|q.im| - chamberBase) ∧
        0 ≤ max (q.re - s) (|q.im| - H) := by
      have hh : 0 ≤ F q := hFq.ge
      simpa only [F, le_min_iff] using hh
    change min (q.re - R)
      (min (max (q.re - a) (|q.im| - chamberBase))
        (max (q.re - s) (|q.im| - H))) = 0 at hFq
    have hcases : q.re - R = 0 ∨ max (q.re - a) (|q.im| - chamberBase) = 0 ∨
        max (q.re - s) (|q.im| - H) = 0 := by
      rcases min_eq_iff.mp hFq with h | h
      · exact Or.inl h.1
      · rcases min_eq_iff.mp h.1 with h | h
        · exact Or.inr (Or.inl h.1)
        · exact Or.inr (Or.inr h.1)
    rcases hcases with hA | hB | hC
    · have hre : q.re = R := by linarith
      have habs : |q.im| < chamberBase := hleft hq hre
      rcases le_max_iff.mp hnonneg.2.1 with h | h
      · dsimp [a] at h
        linarith
      · linarith
    · have hBbound := max_le_iff.mp hB.le
      rcases max_eq_iff.mp hB with h | h
      · have hre : q.re = a := by linarith [h.1]
        have hlo : H ≤ |q.im| := by
          rcases le_max_iff.mp hnonneg.2.2 with h | h <;> linarith
        exact False.elim (hpassage_right hq hre hlo (by linarith [hBbound.2]))
      · exact False.elim (hpassage_top hq (by linarith [hnonneg.1])
          (by linarith [hBbound.1]) (by linarith [h.1]))
    · have hCbound := max_le_iff.mp hC.le
      rcases max_eq_iff.mp hC with h | h
      · have hre : q.re = s := by linarith [h.1]
        refine ⟨hre, ?_⟩
        by_contra hn
        have heq : |q.im| = H := by linarith [hCbound.2, le_of_not_gt hn]
        exact htunnel_top hq (by linarith) hre.le heq
      · have heq : |q.im| = H := by linarith [h.1]
        have hlo : a ≤ q.re := by
          rcases le_max_iff.mp hnonneg.2.1 with h | h <;> linarith
        exact False.elim (htunnel_top hq hlo (by linarith [hCbound.1]) heq)
  have hwre : w.re = R + 1 / 4 := hwpassage.1
  have hzim : |w.im| < chamberBase := hwpassage.2
  have hzre : z.re = R + 3 / 2 := hzclean.1
  have hFw : F w < 0 := by
    apply lt_of_le_of_lt (min_le_right _ _)
    apply lt_of_le_of_lt (min_le_left _ _)
    apply max_lt_iff.mpr
    constructor
    · dsimp [a]
      linarith
    · linarith
  have hFz : 0 < F z := by
    apply lt_min
    · linarith
    · apply lt_min
      · exact lt_of_lt_of_le (by dsimp [a]; linarith) (le_max_left _ _)
      · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  obtain ⟨q, hq, hqF⟩ := hK.intermediate_value hw hz hFcont.continuousOn ⟨hFw.le, hFz.le⟩
  exact ⟨q, hq, hzero (hKV hq) hqF⟩

end MaxModulusPoints.CrosscutDistortion
