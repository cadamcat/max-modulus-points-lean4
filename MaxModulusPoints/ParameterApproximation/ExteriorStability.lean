import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.ConformalKernel.TractGateKernel
import MaxModulusPoints.ConformalKernel.TractGateWalls
import MaxModulusPoints.ParameterApproximation.Limits
import MaxModulusPoints.TractGeometry.StripContainment
/-!
# Persistent exterior points of the chamber tracts

A removed gate endpoint is approached along its vertical wall by points
strictly beyond the limiting opening. Points outside the fully open tract
remain outside every admissible tract. Exponential injectivity on that tract
transfers the resulting exterior approximation to the plane.
-/

noncomputable section

namespace MaxModulusPoints.ParameterApproximation

open Set Filter Blueprint ConformalKernel
open scoped Topology

universe u

/-- A point before the end of a vertical interval can be approached by points
strictly farther from its center, while staying before the end. -/
theorem vertical_displacement_mem_closure {x c h r : ℝ} {z : ℂ}
    (hx : z.re = x) (hh : |z.im - c| < h) (hr : r ≤ |z.im - c|) :
    z ∈ closure {w : ℂ | w.re = x ∧ r < |w.im - c| ∧ |w.im - c| < h} := by
  let line : ℝ → ℂ := fun y => ⟨z.re, y⟩
  have hline : Continuous line :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk continuous_id)
  by_cases hd : 0 ≤ z.im - c
  · rw [abs_of_nonneg hd] at hh hr
    have hzh : z.im < c + h := by linarith
    have hzcl : z.im ∈ closure (Ioo z.im (c + h)) := by
      rw [closure_Ioo hzh.ne]
      exact ⟨le_rfl, hzh.le⟩
    have hsub : line '' Ioo z.im (c + h) ⊆
        {w : ℂ | w.re = x ∧ r < |w.im - c| ∧ |w.im - c| < h} := by
      rintro _ ⟨y, hy, rfl⟩
      have hyd : 0 ≤ y - c := by linarith [hy.1]
      change z.re = x ∧ r < |y - c| ∧ |y - c| < h
      rw [abs_of_nonneg hyd]
      exact ⟨hx, by linarith [hy.1], by linarith [hy.2]⟩
    have himage := mem_closure_image hline.continuousAt hzcl
    have heq : line z.im = z := Complex.eta z
    rw [heq] at himage
    exact closure_mono hsub himage
  · have hd' : z.im - c ≤ 0 := le_of_not_ge hd
    rw [abs_of_nonpos hd'] at hh hr
    have hhz : c - h < z.im := by linarith
    have hzcl : z.im ∈ closure (Ioo (c - h) z.im) := by
      rw [closure_Ioo hhz.ne]
      exact ⟨hhz.le, le_rfl⟩
    have hsub : line '' Ioo (c - h) z.im ⊆
        {w : ℂ | w.re = x ∧ r < |w.im - c| ∧ |w.im - c| < h} := by
      rintro _ ⟨y, hy, rfl⟩
      have hyd : y - c ≤ 0 := by linarith [hy.2]
      change z.re = x ∧ r < |y - c| ∧ |y - c| < h
      rw [abs_of_nonpos hyd]
      exact ⟨hx, by linarith [hy.2], by linarith [hy.1]⟩
    have himage := mem_closure_image hline.continuousAt hzcl
    have heq : line z.im = z := Complex.eta z
    rw [heq] at himage
    exact closure_mono hsub himage

/-- Removed points inside the fully open tract are approached by points
of that tract which are eventually exterior to the varying tracts. -/
theorem tract_exterior_mem_closure {ι : Type u} {l : Filter ι}
    (p : BlockParameters) {δseq : ι → GateIndex → ℝ} {δ : GateIndex → ℝ}
    (hseq : ∀ k i, δseq k i ≤ gateUpper i) (hδ : ∀ i, δ i ≤ gateUpper i)
    (hlim : ∀ i, Tendsto (fun k => δseq k i) l (𝓝 (δ i)))
    {z : ℂ} (hzU : z ∈ tract p gateUpper) (hz : z ∉ tract p δ) :
    z ∈ closure {w : ℂ | w ∈ tract p gateUpper ∧
      ∀ᶠ k in l, w ∉ tract p (δseq k)} := by
  rcases hzU with hfixed | hopen
  · exact False.elim (hz (Or.inl hfixed))
  obtain ⟨i, hi⟩ := mem_iUnion.mp hopen
  obtain ⟨j, hj⟩ := mem_iUnion.mp hi
  have hw : z ∈ tractGateWall p (i, j) := ⟨hj.1, hj.2.le⟩
  have hlevel : δ i / 2 ≤ |z.im - gateWallCenter (i, j)| := by
    apply le_of_not_gt
    intro h
    exact hz ((tractGateWall_mem_tract_iff p hδ hw).mpr ⟨hj.1, h⟩)
  have hcl := vertical_displacement_mem_closure hj.1 hj.2 hlevel
  apply closure_mono _ hcl
  intro w hw'
  have hwall : w ∈ tractGateWall p (i, j) := ⟨hw'.1, hw'.2.2.le⟩
  have hU : w ∈ tract p gateUpper :=
    (tractGateWall_mem_tract_iff p (fun _ => le_rfl) hwall).mpr ⟨hw'.1, hw'.2.2⟩
  refine ⟨hU, ?_⟩
  filter_upwards [(hlim i).div_const 2 |>.eventually (gt_mem_nhds hw'.2.1)] with k hk
  intro hmem
  have hg := (tractGateWall_mem_tract_iff p (hseq k) hwall).mp hmem
  exact (not_lt_of_ge hk.le) hg.2

/-- The planar exterior of a limiting tract is approximated, outside the unit
disk, by points which remain exterior as the gate parameters converge. -/
theorem exp_tract_exterior_mem_closure {ι : Type u} {l : Filter ι}
    (p : BlockParameters) {δseq : ι → GateIndex → ℝ} {δ : GateIndex → ℝ}
    (hseq : ∀ k i, δseq k i ≤ gateUpper i) (hδ : ∀ i, δ i ≤ gateUpper i)
    (hlim : ∀ i, Tendsto (fun k => δseq k i) l (𝓝 (δ i)))
    {z : ℂ} (hz : z ∉ Complex.exp '' tract p δ) (hnorm : 1 < ‖z‖) :
    z ∈ closure {w : ℂ | 1 < ‖w‖ ∧
      ∀ᶠ k in l, w ∉ Complex.exp '' tract p (δseq k)} := by
  have hc : z ∈ closure {w : ℂ | ∀ᶠ k in l,
      w ∉ Complex.exp '' tract p (δseq k)} := by
    by_cases hzU : z ∈ Complex.exp '' tract p gateUpper
    · obtain ⟨v, hvU, rfl⟩ := hzU
      have hv : v ∉ tract p δ := fun h => hz (mem_image_of_mem _ h)
      have hlog := tract_exterior_mem_closure p hseq hδ hlim hvU hv
      have himage := mem_closure_image Complex.continuous_exp.continuousAt hlog
      apply closure_mono _ himage
      rintro _ ⟨w, hw, rfl⟩
      filter_upwards [hw.2] with k hk
      rintro ⟨v', hv', heq⟩
      have hveq : v' = w :=
        TractGeometry.tract_exp_injective p gateUpper (fun _ => le_rfl)
          (tract_mono p (hseq k) hv') hw.1 heq
      exact hk (hveq ▸ hv')
    · apply subset_closure
      exact Eventually.of_forall fun k hk =>
        hzU ((image_mono (tract_mono p (hseq k))) hk)
  apply mem_closure_iff_nhds.mpr
  intro N hN
  have hopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  obtain ⟨w, hw, hstable⟩ := mem_closure_iff_nhds.mp hc
    (N ∩ {w : ℂ | 1 < ‖w‖}) (inter_mem hN (hopen.mem_nhds hnorm))
  exact ⟨w, hw.1, hw.2, hstable⟩

#print axioms vertical_displacement_mem_closure
#print axioms tract_exterior_mem_closure
#print axioms exp_tract_exterior_mem_closure

end MaxModulusPoints.ParameterApproximation
