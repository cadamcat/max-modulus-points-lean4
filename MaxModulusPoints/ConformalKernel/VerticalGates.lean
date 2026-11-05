module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Tactic.Linarith
public import MaxModulusPoints.ConformalKernel.KernelConvergence

/-!
# Kernel convergence for vertical chamber gates

A fixed open ambient set contains the interiors of the passages and chambers.
The remaining variable walls are locally finite vertical segments. A gate of
half-height `δ i` consists of the points on wall `i` with imaginary displacement
strictly less than `δ i`. Wall endpoints belong to the fixed boundary.
-/


@[expose] public section

open Set Filter
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

universe u

/-- A vertical wall of half-height `h`, centered at `x + c I`. -/
def verticalWall (x c h : ℝ) : Set ℂ :=
  {z | z.re = x ∧ |z.im - c| ≤ h}

private theorem verticalWall_strict_dense {x c h r : ℝ} {z : ℂ}
    (hzx : z.re = x) (hzh : |z.im - c| < h) (hr : r ≤ |z.im - c|) :
    z ∈ closure {w | w ∈ verticalWall x c h ∧ r < |w.im - c|} := by
  let line : ℝ → ℂ := fun y => ⟨z.re, y⟩
  have hline : Continuous line := by
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk continuous_id)
  by_cases hd : 0 ≤ z.im - c
  · rw [abs_of_nonneg hd] at hzh hr
    have hyh : z.im < c + h := by linarith
    have hzcl : z.im ∈ closure (Ioo z.im (c + h)) := by
      rw [closure_Ioo hyh.ne]
      exact ⟨le_rfl, hyh.le⟩
    have hsub : line '' Ioo z.im (c + h) ⊆
        {w | w ∈ verticalWall x c h ∧ r < |w.im - c|} := by
      rintro _ ⟨y, hy, rfl⟩
      have hyd : 0 ≤ y - c := by linarith [hy.1]
      change (z.re = x ∧ |y - c| ≤ h) ∧ r < |y - c|
      rw [abs_of_nonneg hyd]
      exact ⟨⟨hzx, by linarith [hy.2]⟩, by linarith [hy.1]⟩
    have himage := mem_closure_image hline.continuousAt hzcl
    have : line z.im = z := Complex.eta z
    rw [this] at himage
    exact closure_mono hsub himage
  · have hd' : z.im - c ≤ 0 := le_of_not_ge hd
    rw [abs_of_nonpos hd'] at hzh hr
    have hyh : c - h < z.im := by linarith
    have hzcl : z.im ∈ closure (Ioo (c - h) z.im) := by
      rw [closure_Ioo hyh.ne]
      exact ⟨hyh.le, le_rfl⟩
    have hsub : line '' Ioo (c - h) z.im ⊆
        {w | w ∈ verticalWall x c h ∧ r < |w.im - c|} := by
      rintro _ ⟨y, hy, rfl⟩
      have hyd : y - c ≤ 0 := by linarith [hy.2]
      change (z.re = x ∧ |y - c| ≤ h) ∧ r < |y - c|
      rw [abs_of_nonpos hyd]
      exact ⟨⟨hzx, by linarith [hy.1]⟩, by linarith [hy.2]⟩
    have himage := mem_closure_image hline.continuousAt hzcl
    have : line z.im = z := Complex.eta z
    rw [this] at himage
    exact closure_mono hsub himage

/-- The gate family formed from vertical walls in a fixed open ambient set. -/
def verticalGateFamily {ι : Type u} (U : Set ℂ) (x c h : ι → ℝ)
    (hU : IsOpen U) (hfinite : LocallyFinite (fun i => verticalWall (x i) (c i) (h i))) :
    GateFamily ℂ ι where
  ambient := U
  wall i := verticalWall (x i) (c i) (h i)
  level i z := |z.im - c i|
  isOpen_ambient := hU
  isClosed_wall i := by
    change IsClosed {z : ℂ | z.re = x i ∧ |z.im - c i| ≤ h i}
    exact (isClosed_eq Complex.continuous_re continuous_const).inter
      (isClosed_le (Complex.continuous_im.sub continuous_const).abs continuous_const)
  locallyFinite_wall := hfinite
  continuous_level i := by
    change Continuous (fun z : ℂ => |z.im - c i|)
    exact (Complex.continuous_im.sub continuous_const).abs

/-- Coordinatewise convergence of the gate half-heights gives kernel convergence
when the limiting gate domain is connected and contains the fixed base point. -/
theorem verticalGateFamily_kernelConverges {ι : Type u} {U : Set ℂ}
    {x c h : ι → ℝ} (hU : IsOpen U)
    (hfinite : LocallyFinite (fun i => verticalWall (x i) (c i) (h i)))
    (hends : ∀ i z, z ∈ U → z ∈ verticalWall (x i) (c i) (h i) → |z.im - c i| < h i)
    {δseq : ℕ → ι → ℝ} {δ : ι → ℝ}
    (hδ : ∀ i, Tendsto (fun n => δseq n i) atTop (𝓝 (δ i))) {a : ℂ}
    (ha : a ∈ (verticalGateFamily U x c h hU hfinite).domain δ)
    (hc : IsPreconnected ((verticalGateFamily U x c h hU hfinite).domain δ)) :
    KernelConverges a ((verticalGateFamily U x c h hU hfinite).domain δ)
      (fun n => (verticalGateFamily U x c h hU hfinite).domain (δseq n)) := by
  apply GateFamily.kernelConverges _ (tendsto_pi_nhds.mpr hδ) ha hc
  intro i z hzU hzw hr
  change z ∈ U at hzU
  change z ∈ verticalWall (x i) (c i) (h i) at hzw
  change δ i ≤ |z.im - c i| at hr
  exact verticalWall_strict_dense hzw.1 (hends i z hzU hzw) hr

#print axioms verticalGateFamily_kernelConverges

end MaxModulusPoints.ConformalKernel
