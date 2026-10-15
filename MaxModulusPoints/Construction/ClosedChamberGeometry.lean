import Mathlib.Analysis.Complex.ReImTopology
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.BottleneckEstimates
import MaxModulusPoints.Blueprint.Interfaces.ClosedGateInterval
import MaxModulusPoints.Blueprint.Interfaces.Rectangle
import MaxModulusPoints.Construction.OpenChamberGeometry
import MaxModulusPoints.Construction.PassageCut
import MaxModulusPoints.Construction.StarredSegments
import MaxModulusPoints.Construction.Tract
/-!
# Chamber rectangles with arbitrary gate heights

The fixed rectangle in Pardo-Simón–Sixsmith, Proposition 4.3, lies in
every tract. Its frontier is removed except at its own right-hand gate.
These statements refer to the literal union-of-frontiers tract.
-/

namespace MaxModulusPoints.Construction

open Set Filter
open scoped Topology

noncomputable section

theorem upper_chamber_interior (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) :
    interior (Blueprint.chamber p i true) =
      {z : ℂ | Blueprint.blockPosition p i.1 < z.re ∧
        z.re < Blueprint.blockPosition p i.1 + 1 ∧
        chamberBottom i.1 i.2 < z.im ∧ z.im < chamberTop i.1 i.2} := by
  have heq : Blueprint.chamber p i true =
      Complex.re ⁻¹' Icc (Blueprint.blockPosition p i.1) (Blueprint.blockPosition p i.1 + 1) ∩
        Complex.im ⁻¹' Icc (chamberBottom i.1 i.2) (chamberTop i.1 i.2) := by
    ext z
    simp only [mem_chamber_iff_coordinates, Blueprint.sideSign, ite_true, one_mul,
      mem_inter_iff, mem_preimage, mem_Icc]
    tauto
  rw [heq, interior_inter, Complex.interior_preimage_re, Complex.interior_preimage_im,
    interior_Icc, interior_Icc]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_Ioo, mem_ofPred_eq]
  tauto

/-- Chamber interiors are independent of every gate parameter. -/
theorem upper_chamber_interior_subset_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex) :
    interior (Blueprint.chamber p i true) ⊆ Blueprint.tract p δ := by
  intro z hz
  rw [upper_chamber_interior] at hz
  have hmem := open_chamber_corridor_mem p Blueprint.gateUpper i rfl
    ⟨hz.1, by linarith [hz.2.1]⟩ hz.2.2
  rcases hmem with (hb | ho) | hg
  · exact Or.inl (Or.inl hb)
  · exact Or.inl (Or.inr ho)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hg
    obtain ⟨j, hj⟩ := mem_iUnion.mp hk
    have hki := block_support_unique p
      (gate_support p Blueprint.gateUpper k j hj) ⟨hz.1.le, hz.2.1.le⟩
    have he := hj.1
    rw [hki] at he
    linarith [hz.2.1]

theorem gate_height_bounds (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex) (j : Bool)
    (hδ : δ i ≤ Blueprint.gateUpper i) {z : ℂ}
    (hz : z ∈ Blueprint.gate p δ i j) :
    chamberBottom i.1 i.2 < Blueprint.sideSign j * z.im ∧
      Blueprint.sideSign j * z.im < chamberTop i.1 i.2 := by
  have hy := hz.2
  rw [← upperChamberHeight_gate_center] at hy
  rw [gateUpper_eq_chamberWidth] at hδ
  have habs := abs_lt.mp hy
  cases j <;> simp only [Blueprint.sideSign, Bool.false_eq_true, ite_false, ite_true,
    neg_mul, one_mul] at *
    <;> dsimp [upperChamberHeight, chamberBottom, chamberTop] at *
    <;> constructor <;> linarith [habs.1, habs.2]

/-- No other opening or gate restores a point on this chamber's frontier. -/
theorem upper_chamber_frontier_not_mem_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (hδ : ∀ k, δ k ≤ Blueprint.gateUpper k)
    (i : Blueprint.GateIndex) {z : ℂ}
    (hz : z ∈ frontier (Blueprint.chamber p i true))
    (hgate : z ∉ Blueprint.gate p δ i true) : z ∉ Blueprint.tract p δ := by
  have hc := chamber_frontier_coordinates p i true hz
  simp only [Blueprint.sideSign, ite_true, one_mul] at hc
  have hbase : Blueprint.chamberBase ≤ z.im := (chamber_bounds i.1 i.2).1.trans hc.2.2.1
  have hypos : 0 < z.im := passageHalfHeight_pos.trans_le hbase
  have hsupport : Blueprint.blockPosition p i.1 ≤ z.re ∧
      z.re ≤ Blueprint.blockPosition p i.1 + 1 := ⟨hc.1, hc.2.1⟩
  intro hmem
  rcases hmem with (hb | ho) | hg
  · apply hb.2
    exact mem_iUnion.mpr ⟨i.1, Or.inr
      (mem_iUnion.mpr ⟨i.2, mem_iUnion.mpr ⟨true, hz⟩⟩)⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.mp ho
    have hin := block_support_unique p hsupport (opening_support p n hn)
    subst n
    rcases hn with ⟨_, hy⟩ | ⟨_, hy⟩ | ⟨_, hy⟩
    · linarith [le_abs_self z.im]
    · have hsmall : p.tunnelHeight i.1 / 2 < Blueprint.chamberBase := by
        dsimp [Blueprint.chamberBase]
        linarith [p.tunnel_le_quarter i.1, Real.pi_gt_three]
      linarith [le_abs_self z.im]
    · have hsmall : p.tunnelHeight i.1 / 2 < Blueprint.chamberBase := by
        dsimp [Blueprint.chamberBase]
        linarith [p.tunnel_le_quarter i.1, Real.pi_gt_three]
      linarith [le_abs_self z.im]
  · obtain ⟨⟨n, m⟩, hm⟩ := mem_iUnion.mp hg
    obtain ⟨j, hj⟩ := mem_iUnion.mp hm
    have hin := block_support_unique p hsupport (gate_support p δ ⟨n, m⟩ j hj)
    change i.1 = n at hin
    subst n
    have hh := gate_height_bounds p δ ⟨i.1, m⟩ j (hδ _) hj
    cases j
    · simp only [Blueprint.sideSign, Bool.false_eq_true, ite_false, neg_mul, one_mul] at hh
      linarith [(chamber_bounds i.1 m).1, passageHalfHeight_pos]
    · simp only [Blueprint.sideSign, ite_true, one_mul] at hh
      rcases lt_trichotomy m i.2 with hmi | hmi | him
      · linarith [chamberTop_le_bottom hmi, hh.2, hc.2.2.1]
      · subst m
        exact hgate hj
      · linarith [chamberTop_le_bottom him, hh.1, hc.2.2.2.1]

/-- Translation from the fixed rectangle to an upper chamber. -/
def chamberTranslation (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) (z : ℂ) : ℂ :=
  z + (⟨Blueprint.blockPosition p i.1, chamberBottom i.1 i.2⟩ : ℂ)

theorem chamberTranslation_continuous (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) :
    Continuous (chamberTranslation p i) := continuous_id.add continuous_const

theorem chamberTranslation_mapsTo (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) :
    MapsTo (chamberTranslation p i) (Blueprint.rectangle (chamberWidth i.1))
      (interior (Blueprint.chamber p i true)) := by
  intro z hz
  rw [upper_chamber_interior]
  dsimp [Blueprint.rectangle] at hz
  simp only [mem_ofPred_eq, chamberTranslation, Complex.add_re, Complex.add_im]
  refine ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], ?_⟩
  dsimp [chamberBottom, chamberTop] at *
  linarith [hz.2.2.2]

theorem rectangle_frontier_bounds {h : ℝ} {z : ℂ}
    (hz : z ∈ frontier (Blueprint.rectangle h)) :
    0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ h ∧
      (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = h) := by
  have hclosed : IsClosed {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ 0 ≤ w.im ∧ w.im ≤ h} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  have hc := hclosed.closure_subset_iff.mpr (show Blueprint.rectangle h ⊆
      {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ 0 ≤ w.im ∧ w.im ≤ h} from
    fun w hw => ⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.le⟩)
  have hb := hc (frontier_subset_closure hz)
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, ?_⟩
  by_contra hs
  push Not at hs
  have hstrict : z ∈ Blueprint.rectangle h :=
    ⟨lt_of_le_of_ne hb.1 hs.1.symm, lt_of_le_of_ne hb.2.1 hs.2.1,
      lt_of_le_of_ne hb.2.2.1 hs.2.2.1.symm, lt_of_le_of_ne hb.2.2.2 hs.2.2.2⟩
  exact hz.2 (((isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))).interior_eq ▸ hstrict)

theorem chamberTranslation_frontier (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex)
    {z : ℂ} (hz : z ∈ frontier (Blueprint.rectangle (chamberWidth i.1))) :
    chamberTranslation p i z ∈ frontier (Blueprint.chamber p i true) := by
  have hb := rectangle_frontier_bounds hz
  refine ⟨subset_closure ?_, ?_⟩
  · rw [mem_chamber_iff_coordinates]
    simp only [chamberTranslation, Complex.add_re, Complex.add_im, Blueprint.sideSign,
      ite_true, one_mul]
    refine ⟨by linarith [hb.1], by linarith [hb.2.1], by linarith [hb.2.2.1], ?_⟩
    dsimp [chamberBottom, chamberTop] at *
    linarith [hb.2.2.2.1]
  · rw [upper_chamber_interior]
    intro hin
    simp only [chamberTranslation, Complex.add_re, Complex.add_im, mem_ofPred_eq] at hin
    rcases hb.2.2.2.2 with hx | hx | hy | hy
    · linarith [hin.1]
    · linarith [hin.2.1]
    · linarith [hin.2.2.1]
    · dsimp [chamberBottom, chamberTop] at hin
      linarith [hin.2.2.2]

theorem chamberTranslation_boundary_not_mem_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (hδ : ∀ k, δ k ≤ Blueprint.gateUpper k)
    (i : Blueprint.GateIndex) {z : ℂ}
    (hz : z ∈ frontier (Blueprint.rectangle (chamberWidth i.1)) \
      Blueprint.closedGateInterval (chamberWidth i.1 / 2) (δ i)) :
    chamberTranslation p i z ∉ Blueprint.tract p δ := by
  apply upper_chamber_frontier_not_mem_tract p δ hδ i (chamberTranslation_frontier p i hz.1)
  intro hgate
  apply hz.2
  have hx := hgate.1
  have hy := hgate.2
  rw [← upperChamberHeight_gate_center] at hy
  simp only [chamberTranslation, Complex.add_re, Complex.add_im, Blueprint.sideSign,
    ite_true, one_mul] at hx hy
  refine ⟨by linarith, ?_⟩
  have he : z.im + chamberBottom i.1 i.2 - upperChamberHeight i =
      z.im - chamberWidth i.1 / 2 := by dsimp [upperChamberHeight]; ring
  rw [he] at hy
  exact hy.le

#print axioms upper_chamber_interior_subset_tract
#print axioms upper_chamber_frontier_not_mem_tract
#print axioms chamberTranslation_boundary_not_mem_tract

end

end MaxModulusPoints.Construction
