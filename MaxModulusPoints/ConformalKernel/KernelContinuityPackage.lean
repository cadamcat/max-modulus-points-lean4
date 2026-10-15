import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.Blueprint.Interfaces.KernelContinuity
import MaxModulusPoints.ConformalKernel.KernelConvergence
import MaxModulusPoints.ConformalKernel.LogModelContinuity
import MaxModulusPoints.ConformalKernel.TargetDomain
import MaxModulusPoints.ConformalKernel.TractGateKernel
import MaxModulusPoints.TractGeometry.StripContainment
/-!
# Continuity of the normalized chamber-tract maps

The chamber tracts have jointly open incidence and converge in the pointed
kernel sense as their gate parameters converge. Their positive normalization
therefore gives locally uniform dependence of the forward maps, specified
inverses and derivatives, as used in Pardo-Simón–Sixsmith, Observation 2.3.
-/

noncomputable section

namespace MaxModulusPoints.ConformalKernel

open Set Filter Blueprint
open scoped Topology

/-- A fixed proper strip containing all admissible chamber tracts. -/
def tractAmbientStrip : Set ℂ := {z | |z.im| < Real.pi / 2}

/-- The common ambient strip is open. -/
theorem isOpen_tractAmbientStrip : IsOpen tractAmbientStrip :=
  isOpen_lt Complex.continuous_im.abs continuous_const

/-- The common ambient strip is a proper plane domain. -/
theorem tractAmbientStrip_ne_univ : tractAmbientStrip ≠ univ := by
  intro h
  have hz : (⟨0, Real.pi / 2⟩ : ℂ) ∈ tractAmbientStrip := h ▸ mem_univ _
  change |Real.pi / 2| < Real.pi / 2 at hz
  rw [abs_of_pos (half_pos Real.pi_pos)] at hz
  exact (lt_irrefl _) hz

/-- Convexity makes the common ambient strip simply connected. -/
theorem isSimplyConnected_tractAmbientStrip : IsSimplyConnected tractAmbientStrip := by
  have heq : tractAmbientStrip =
      {z : ℂ | -(Real.pi / 2) < z.im} ∩ {z : ℂ | z.im < Real.pi / 2} := by
    ext z
    change |z.im| < Real.pi / 2 ↔ -(Real.pi / 2) < z.im ∧ z.im < Real.pi / 2
    exact abs_lt
  have hconv : Convex ℝ tractAmbientStrip := by
    rw [heq]
    exact (convex_halfSpace_gt (𝕜 := ℝ) Complex.imLm.isLinear (-(Real.pi / 2))).inter
      (convex_halfSpace_lt (𝕜 := ℝ) Complex.imLm.isLinear (Real.pi / 2))
  have hzero : (0 : ℂ) ∈ tractAmbientStrip := by
    change |(0 : ℂ).im| < Real.pi / 2
    simpa only [Complex.zero_im, abs_zero] using half_pos Real.pi_pos
  let : ContractibleSpace tractAmbientStrip := hconv.contractibleSpace ⟨0, hzero⟩
  change SimplyConnectedSpace tractAmbientStrip
  infer_instance

/-- A logarithmic conformal equivalence has a connected source because its
specified inverse maps the connected target onto that source. -/
theorem logModel_isPreconnected {V : Set ℂ} (G : LogModel V) : IsPreconnected V := by
  have heq : G.invFun '' target = V := by
    apply Subset.antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact G.inverse_mapsTo hw
    · intro z hz
      exact ⟨G.toFun z, G.mapsTo hz, G.left_inv z hz⟩
  rw [← heq]
  exact isSimplyConnected_modelTarget.isPathConnected.isConnected.isPreconnected.image
    G.invFun G.inverse_holomorphic.continuousOn

/-- Gate incidence is jointly open on every closed admissible parameter box,
assuming only that the fully open tract is open. -/
theorem isOpen_tract_parameterSpace (p : BlockParameters) (a : GateIndex → ℝ)
    (hU : IsOpen (tract p gateUpper)) :
    IsOpen {v : ParameterBox a gateUpper × ℂ |
      v.2 ∈ tract p (fun i => (v.1 i : ℝ))} := by
  have hcoord (i : GateIndex) :
      Continuous (fun e : ParameterBox a gateUpper => (e i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hparam : Continuous (fun v : ParameterBox a gateUpper × ℂ =>
      (fun q : GateIndex × Bool => (v.1 q.1 : ℝ) / 2)) :=
    continuous_pi fun q => ((hcoord q.1).comp continuous_fst).div_const 2
  have ho := (tractGateFamily p hU).isOpen_totalSpace.preimage
    (hparam.prodMk continuous_snd)
  convert ho using 1
  ext v
  change v.2 ∈ tract p (fun i => (v.1 i : ℝ)) ↔
    v.2 ∈ (tractGateFamily p hU).domain (fun q => (v.1 q.1 : ℝ) / 2)
  rw [tract_eq_gateFamily_domain p hU (fun i => (v.1 i).property.2)]

#print axioms isOpen_tractAmbientStrip
#print axioms tractAmbientStrip_ne_univ
#print axioms isSimplyConnected_tractAmbientStrip
#print axioms logModel_isPreconnected
#print axioms isOpen_tract_parameterSpace

end MaxModulusPoints.ConformalKernel

namespace MaxModulusPoints.Blueprint.Packages

open Set Filter ConformalKernel
open scoped Topology

/-- Normalized chamber-tract maps, their specified inverses and their derivatives
depend locally uniformly on the positive gate parameters. -/
theorem kernel_continuity_proof : KernelContinuity := by
  intro p a ha G
  let upper : ParameterBox a gateUpper := fun i => ⟨gateUpper i, (ha i).2, le_rfl⟩
  have hU : IsOpen (tract p gateUpper) := (G upper).open_domain
  refine ⟨isOpen_tract_parameterSpace p a hU, ?_⟩
  intro δ
  apply logModels_tendsto_of_seq_kernel G ?_ isOpen_tractAmbientStrip
    isSimplyConnected_tractAmbientStrip tractAmbientStrip_ne_univ ?_
  · intro v hv
    apply tract_kernelConverges p hU (fun n i => (v n i).property.2)
      (fun i => (δ i).property.2) ?_ (G δ).base_mem (logModel_isPreconnected (G δ))
    intro i
    have hcoord : Continuous (fun e : ParameterBox a gateUpper => (e i : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply i)
    exact (hcoord.tendsto δ).comp hv
  · intro ε z hz
    exact TractGeometry.tract_im_lt p _ (fun i => (ε i).property.2) hz

#print axioms kernel_continuity_proof

end MaxModulusPoints.Blueprint.Packages
