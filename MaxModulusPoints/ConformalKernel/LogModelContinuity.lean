module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.ConformalKernel.KernelConvergence
public import MaxModulusPoints.ConformalKernel.NormalizedMaps
public import MaxModulusPoints.ConformalKernel.ParameterKernelTheorem
public import MaxModulusPoints.ConformalKernel.TargetDomain

/-!
# Kernel continuity of logarithmic conformal maps

The explicit inverse of a normalized logarithmic conformal map agrees on its
target with the canonical inverse. The parameter kernel theorem therefore gives
simultaneous convergence of the specified forward maps, inverses and derivatives.
-/


@[expose] public section

open Set Filter Function
open scoped Topology ComplexOrder

namespace MaxModulusPoints.ConformalKernel

universe u

/-- A normalized logarithmic map has the positive normalization used by the
fixed-target kernel theorem. -/
theorem logModel_isNormalizedConformalMap {V : Set ℂ} (G : Blueprint.LogModel V) :
    IsNormalizedConformalMap V Blueprint.target (-1) 1 G.toFun := by
  have hleft : LeftInvOn G.invFun G.toFun V := G.left_inv
  have hright : RightInvOn G.invFun G.toFun Blueprint.target := G.right_inv
  exact ⟨G.base_mem, one_mem_modelTarget, G.holomorphic,
    ⟨G.mapsTo, hleft.injOn, hright.surjOn G.inverse_mapsTo⟩,
    G.base_value, Complex.pos_iff.mpr ⟨G.positive_derivative, G.real_derivative.symm⟩⟩

/-- The canonical inverse agrees with the specified inverse on the target. -/
theorem logModel_invFun_eqOn {V : Set ℂ} (G : Blueprint.LogModel V) :
    EqOn (invFunOn G.toFun V) G.invFun Blueprint.target :=
  eqOn_of_leftInvOn_of_rightInvOn
    (logModel_isNormalizedConformalMap G).bijOn.injOn.leftInvOn_invFunOn
    G.right_inv G.inverse_mapsTo

/-- Sequential kernel convergence of a logarithmic conformal family gives
local uniform parameter dependence, including its specified inverses and derivatives. -/
theorem logModels_tendsto_of_seq_kernel
    {P : Type u} [TopologicalSpace P] [FirstCountableTopology P]
    {domains : P → Set ℂ} (G : ∀ p, Blueprint.LogModel (domains p)) {p₀ : P}
    (hkernel : ∀ v : ℕ → P, Tendsto v atTop (𝓝 p₀) →
      KernelConverges (-1) (domains p₀) (fun n => domains (v n)))
    {A : Set ℂ} (hA : IsOpen A) (hsA : IsSimplyConnected A) (hpA : A ≠ univ)
    (hsource : ∀ p, domains p ⊆ A) :
    TendstoLocallyUniformlyOn (fun p => (G p).toFun) (G p₀).toFun (𝓝 p₀) (domains p₀) ∧
      TendstoLocallyUniformlyOn (fun p => (G p).invFun) (G p₀).invFun
        (𝓝 p₀) Blueprint.target ∧
      TendstoLocallyUniformlyOn (fun p => deriv (G p).toFun) (deriv (G p₀).toFun)
        (𝓝 p₀) (domains p₀) := by
  obtain ⟨hf, hi, hd⟩ := conformal_maps_tendsto_of_seq_kernel (G p₀).open_domain
    hkernel hA hsA hpA isOpen_modelTarget isSimplyConnected_modelTarget modelTarget_ne_univ
    hsource (fun p => (G p).open_domain) (fun p => logModel_isNormalizedConformalMap (G p))
    (logModel_isNormalizedConformalMap (G p₀))
  exact ⟨hf, (hi.congr (fun p => logModel_invFun_eqOn (G p))).congr_right
    (logModel_invFun_eqOn (G p₀)), hd⟩

#print axioms logModel_isNormalizedConformalMap
#print axioms logModel_invFun_eqOn
#print axioms logModels_tendsto_of_seq_kernel

end MaxModulusPoints.ConformalKernel
