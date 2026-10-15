import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Group.Bounded
import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.CauchyApproximation.AdapterContract
import MaxModulusPoints.CauchyApproximation.Model
open Complex ComplexConjugate Filter Set
open scoped Topology

noncomputable section

namespace MaxModulusPoints.CauchyApproximation

private def targetShear : ℂ ≃ₜ ℂ where
  toFun z := z + (14 * Real.posLog |z.im| : ℝ)
  invFun z := z - (14 * Real.posLog |z.im| : ℝ)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_id.add
    (continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_posLog.comp continuous_im.abs)))
  continuous_invFun := continuous_id.sub
    (continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_posLog.comp continuous_im.abs)))

private theorem target_simplyConnected : IsSimplyConnected modelHalfPlane := by
  have hc : Convex ℝ {z : ℂ | 0 < z.re} :=
    convex_halfSpace_gt reCLM.isLinear 0
  have hn : ({z : ℂ | 0 < z.re} : Set ℂ).Nonempty := ⟨1, by simp⟩
  have := hc.contractibleSpace hn
  have hs : IsSimplyConnected {z : ℂ | 0 < z.re} := by
    change SimplyConnectedSpace _
    infer_instance
  have he : targetShear ⁻¹' {z : ℂ | 0 < z.re} = modelHalfPlane := by
    ext z
    change (0 < (z + (14 * Real.posLog |z.im| : ℝ)).re) ↔
      -14 * Real.posLog |z.im| < z.re
    simp only [add_re, ofReal_re]
    constructor <;> intro h <;> linarith
  rw [← he]
  exact targetShear.isSimplyConnected_preimage.mpr hs

private def exponentialChart (V : Set ℂ) (G : Blueprint.LogModel V) :
    OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofContinuousOpen
    (G.exp_injective.toPartialEquiv Complex.exp V)
    continuous_exp.continuousOn Complex.isOpenMap_exp G.open_domain

private theorem exponentialChart_symm_exp (V : Set ℂ) (G : Blueprint.LogModel V)
    (z : ℂ) (hz : z ∈ V) : (exponentialChart V G).symm (Complex.exp z) = z :=
  (exponentialChart V G).left_inv hz

private theorem exponentialChart_differentiable (V : Set ℂ) (G : Blueprint.LogModel V) :
    DifferentiableOn ℂ (exponentialChart V G).symm (Complex.exp '' V) := by
  intro z hz
  exact ((exponentialChart V G).hasDerivAt_symm hz
    (Complex.exp_ne_zero _) (Complex.hasDerivAt_exp _)).differentiableAt.differentiableWithinAt

private def logarithmicHomeomorph (V : Set ℂ) (G : Blueprint.LogModel V) :
    V ≃ₜ modelHalfPlane where
  toFun z := ⟨G.toFun z, G.mapsTo z.property⟩
  invFun w := ⟨G.invFun w, G.inverse_mapsTo w.property⟩
  left_inv z := Subtype.ext (G.left_inv z z.property)
  right_inv w := Subtype.ext (G.right_inv w w.property)
  continuous_toFun := G.holomorphic.continuousOn.domRestrict.subtype_mk _
  continuous_invFun := G.inverse_holomorphic.continuousOn.domRestrict.subtype_mk _

private theorem exponentialImage_simplyConnected (V : Set ℂ) (G : Blueprint.LogModel V) :
    IsSimplyConnected (Complex.exp '' V) := by
  have : SimplyConnectedSpace modelHalfPlane := target_simplyConnected
  exact (((exponentialChart V G).toHomeomorphSourceTarget.symm.trans
    (logarithmicHomeomorph V G)).toHomotopyEquiv).simplyConnectedSpace

private theorem exponentialInverse_escape (V : Set ℂ) (G : Blueprint.LogModel V)
    (w : ℕ → ℂ) (hw : ∀ n, w n ∈ modelHalfPlane)
    (h : Tendsto (fun n ↦ ‖w n‖) atTop atTop) :
    Tendsto (fun n ↦ ‖Complex.exp (G.invFun (w n))‖) atTop atTop := by
  simpa only [Complex.norm_exp, Function.comp_def] using
    Real.tendsto_exp_atTop.comp (G.escape w hw h)

private theorem exponentialImage_unbounded (V : Set ℂ) (G : Blueprint.LogModel V) :
    ¬ Bornology.IsBounded (Complex.exp '' V) := by
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  let w : ℕ → ℂ := fun n ↦ (n : ℂ) + 1
  have hw (n : ℕ) : w n ∈ modelHalfPlane := by
    simp [w, modelHalfPlane]
    positivity
  have ht : Tendsto (fun n ↦ ‖w n‖) atTop atTop := by
    have he (n : ℕ) : ‖w n‖ = (n : ℝ) + 1 := by
      have heq : w n = (((n : ℝ) + 1 : ℝ) : ℂ) := by simp [w]
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp_rw [he]
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := ((exponentialInverse_escape V G w hw ht).eventually
    (eventually_gt_atTop C)).exists
  exact (not_lt_of_ge (hC _ ⟨G.invFun (w n), G.inverse_mapsTo (hw n), rfl⟩)) hn

private def planarModel (V : Set ℂ) (G : Blueprint.LogModel V) : NormalizedModel where
  domain := Complex.exp '' V
  isOpen_domain := Complex.isOpenMap_exp V G.open_domain
  simplyConnected_domain := exponentialImage_simplyConnected V G
  unbounded_domain := exponentialImage_unbounded V G
  zero_not_mem := by
    rintro ⟨z, _, hz⟩
    exact Complex.exp_ne_zero z hz
  forward := G.toFun ∘ (exponentialChart V G).symm
  inverse := Complex.exp ∘ G.invFun
  holomorphic_forward := G.holomorphic.comp (exponentialChart_differentiable V G)
    (fun _ hz ↦ (exponentialChart V G).map_target hz)
  holomorphic_inverse := Complex.differentiable_exp.comp_differentiableOn G.inverse_holomorphic
  forward_mem := fun _ hz ↦ G.mapsTo ((exponentialChart V G).map_target hz)
  inverse_mem := fun w hw ↦ ⟨G.invFun w, G.inverse_mapsTo hw, rfl⟩
  left_inverse := by
    intro z hz
    change Complex.exp (G.invFun (G.toFun ((exponentialChart V G).symm z))) = z
    rw [G.left_inv _ ((exponentialChart V G).map_target hz)]
    exact (exponentialChart V G).right_inv hz
  right_inverse := by
    intro w hw
    change G.toFun ((exponentialChart V G).symm (Complex.exp (G.invFun w))) = w
    rw [exponentialChart_symm_exp V G _ (G.inverse_mapsTo hw)]
    exact G.right_inv w hw
  base_mem := ⟨-1, G.base_mem, rfl⟩
  base_value := by
    change G.toFun ((exponentialChart V G).symm (Complex.exp (-1))) = 1
    rw [exponentialChart_symm_exp V G _ G.base_mem]
    exact G.base_value
  inverse_infinity := exponentialInverse_escape V G

private theorem planarModel_forward_exp (V : Set ℂ) (G : Blueprint.LogModel V)
    (z : ℂ) (hz : z ∈ V) : (planarModel V G).forward (Complex.exp z) = G.toFun z := by
  change G.toFun ((exponentialChart V G).symm (Complex.exp z)) = G.toFun z
  rw [exponentialChart_symm_exp V G z hz]

private theorem planarModel_realSymmetric (V : Set ℂ) (G : Blueprint.LogModel V) :
    (planarModel V G).IsRealSymmetric := by
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨conj z, G.symmetric_domain z hz, Complex.exp_conj z⟩
  · intro x hx
    obtain ⟨z, hz, he⟩ := hx
    rw [← he, planarModel_forward_exp V G z hz]
    apply Complex.conj_eq_iff_im.mp
    change star (G.toFun z) = G.toFun z
    rw [← G.symmetric_map z hz]
    congr 1
    apply G.exp_injective (G.symmetric_domain z hz) hz
    change Complex.exp (conj z) = Complex.exp z
    rw [Complex.exp_conj, he, Complex.conj_ofReal]

/-- Exponentiation carries normalized logarithmic conformal data to planar conformal data. -/
theorem logModelAdapter : LogModelAdapterStatement := by
  intro V G
  refine ⟨planarModel V G, rfl, planarModel_forward_exp V G, ?_,
    planarModel_realSymmetric V G⟩
  intro w _
  rfl

end MaxModulusPoints.CauchyApproximation
