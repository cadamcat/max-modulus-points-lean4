module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.ConformalKernel.KernelConvergence
public import MaxModulusPoints.ConformalKernel.TractGateWalls
public import MaxModulusPoints.ConformalKernel.VerticalGates

/-!
# Kernel convergence of the chamber tracts

Each tract is the fully open tract with the closed portions of its variable
chamber walls removed. The vertical-wall kernel theorem then applies to
coordinatewise convergent gate parameters.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.ConformalKernel

open Set Filter Blueprint
open scoped Topology

/-- Enlarging the gates enlarges the tract. -/
theorem tract_mono (p : BlockParameters) {δ ε : GateIndex → ℝ}
    (h : ∀ i, δ i ≤ ε i) : tract p δ ⊆ tract p ε := by
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · rcases mem_iUnion.mp hz with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨j, hj⟩
    exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j,
      hj.1, lt_of_lt_of_le hj.2 (div_le_div_of_nonneg_right (h i) (by norm_num))⟩⟩)

/-- A point on a variable chamber wall belongs to the tract exactly when it
belongs to that wall's gate. -/
theorem tractGateWall_mem_tract_iff (p : BlockParameters) {δ : GateIndex → ℝ}
    (hδ : ∀ i, δ i ≤ gateUpper i) {q : GateIndex × Bool} {z : ℂ}
    (hz : z ∈ tractGateWall p q) :
    z ∈ tract p δ ↔ z ∈ gate p δ q.1 q.2 := by
  constructor
  · intro ht
    rcases ht with (ht | ht) | ht
    · exact False.elim (ht.2 (tractGateWall_subset_walls p q hz))
    · obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      exact False.elim (tractGateWall_not_mem_openings p q hz n hn)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp ht
      obtain ⟨j, hj⟩ := mem_iUnion.mp hi
      have he := tractGateWall_gate_unique p hδ (r := (i, j)) hz hj
      rw [congrArg Prod.fst he, congrArg Prod.snd he]
      exact hj
  · intro hg
    exact Or.inr (mem_iUnion.mpr ⟨q.1, mem_iUnion.mpr ⟨q.2, hg⟩⟩)

/-- The endpoints of each chamber wall are excluded even when every gate is fully open. -/
theorem tractGateWall_endpoints_excluded (p : BlockParameters) {q : GateIndex × Bool}
    {z : ℂ} (hU : z ∈ tract p gateUpper) (hz : z ∈ tractGateWall p q) :
    |z.im - gateWallCenter q| < gateWallRadius q :=
  ((tractGateWall_mem_tract_iff p (fun _ => le_rfl) hz).mp hU).2

/-- The variable-wall presentation of a tract, relative to the fully open tract. -/
def tractGateFamily (p : BlockParameters) (hU : IsOpen (tract p gateUpper)) :
    GateFamily ℂ (GateIndex × Bool) :=
  verticalGateFamily (tract p gateUpper) (gateWallPosition p) gateWallCenter gateWallRadius
    hU (locallyFinite_tractGateWall p)

/-- The concrete tract agrees exactly with its variable-wall presentation. -/
theorem tract_eq_gateFamily_domain (p : BlockParameters) (hU : IsOpen (tract p gateUpper))
    {δ : GateIndex → ℝ} (hδ : ∀ i, δ i ≤ gateUpper i) :
    tract p δ = (tractGateFamily p hU).domain (fun q => δ q.1 / 2) := by
  ext z
  change z ∈ tract p δ ↔ z ∈ tract p gateUpper ∧
    z ∉ ⋃ q, tractGateWall p q ∩ {w | δ q.1 / 2 ≤ |w.im - gateWallCenter q|}
  constructor
  · intro hz
    refine ⟨tract_mono p hδ hz, ?_⟩
    rintro hw
    obtain ⟨q, hq, hlevel⟩ := mem_iUnion.mp hw
    have hg := (tractGateWall_mem_tract_iff p hδ hq).mp hz
    exact (not_lt_of_ge hlevel) hg.2
  · rintro ⟨hz, hnot⟩
    rcases hz with hz | hz
    · exact Or.inl hz
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hi
      have hw : z ∈ tractGateWall p (i, j) := ⟨hj.1, hj.2.le⟩
      have hlevel : |z.im - gateWallCenter (i, j)| < δ i / 2 := by
        apply lt_of_not_ge
        intro hle
        exact hnot (mem_iUnion.mpr ⟨(i, j), hw, hle⟩)
      exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hj.1, hlevel⟩⟩)

/-- Coordinatewise convergence of admissible gates gives pointed kernel
convergence, provided the limiting tract is connected and the fully open tract is open. -/
theorem tract_kernelConverges (p : BlockParameters) (hU : IsOpen (tract p gateUpper))
    {δseq : ℕ → GateIndex → ℝ} {δ : GateIndex → ℝ}
    (hδseq : ∀ n i, δseq n i ≤ gateUpper i) (hδ : ∀ i, δ i ≤ gateUpper i)
    (hlim : ∀ i, Tendsto (fun n => δseq n i) atTop (𝓝 (δ i)))
    (ha : (-1 : ℂ) ∈ tract p δ) (hc : IsPreconnected (tract p δ)) :
    KernelConverges (-1) (tract p δ) (fun n => tract p (δseq n)) := by
  let J := tractGateFamily p hU
  have hdom : J.domain (fun q => δ q.1 / 2) = tract p δ :=
    (tract_eq_gateFamily_domain p hU hδ).symm
  have hdomseq : (fun n => J.domain (fun q => δseq n q.1 / 2)) =
      (fun n => tract p (δseq n)) :=
    funext fun n => (tract_eq_gateFamily_domain p hU (hδseq n)).symm
  have hbase : (-1 : ℂ) ∈ J.domain (fun q => δ q.1 / 2) := by rwa [hdom]
  have hconn : IsPreconnected (J.domain (fun q => δ q.1 / 2)) := by rwa [hdom]
  have hk := verticalGateFamily_kernelConverges hU (locallyFinite_tractGateWall p)
    (fun q z hz hw => tractGateWall_endpoints_excluded p hz hw)
    (fun q => (hlim q.1).div_const 2) hbase hconn
  change KernelConverges (-1) (J.domain (fun q => δ q.1 / 2))
    (fun n => J.domain (fun q => δseq n q.1 / 2)) at hk
  rwa [hdom, hdomseq] at hk

#print axioms tract_mono
#print axioms tractGateWall_mem_tract_iff
#print axioms tractGateWall_endpoints_excluded
#print axioms tract_eq_gateFamily_domain
#print axioms tract_kernelConverges

end MaxModulusPoints.ConformalKernel
