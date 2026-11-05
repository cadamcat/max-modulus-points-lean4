module

public import Mathlib.Analysis.Complex.RealDeriv
public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.PotentialSpeed
public import MaxModulusPoints.CrosscutDistortion.TunnelLength
public import MaxModulusPoints.CrosscutDistortion.TunnelSlice

/-!
# Conformal pullback density for a vertical slab

The density is the norm of the complex derivative where the image lies
between the vertical sides of the target slab, and zero elsewhere.
Its vertical slice integral equals the slab-weighted image-curve length.
-/


@[expose] public section

noncomputable section

namespace MaxModulusPoints.CrosscutDistortion

open Set MeasureTheory Blueprint
open scoped Topology

/-- The inverse holomorphic map makes the source of a strip equivalence open. -/
theorem strip_equivalence_source_isOpen {U : Set ℂ} (φ : ConformalEquivalence U strip) :
    IsOpen U := by
  have hSo : IsOpen strip := isOpen_lt Complex.continuous_im.abs continuous_const
  have h0S : (0 : ℂ) ∈ strip := by norm_num [strip]
  have h1S : (1 : ℂ) ∈ strip := by norm_num [strip]
  have hconv : Convex ℝ strip := by
    simpa only [strip, abs_lt, ofPred_and] using
      (convex_halfSpace_im_gt (-(1 / 2 : ℝ))).inter
        (convex_halfSpace_im_lt (1 / 2 : ℝ))
  have hnonconstant : ¬ ∃ c : ℂ, ∀ q ∈ strip, φ.invFun q = c := by
    rintro ⟨c, hc⟩
    have hh := congrArg φ.toFun ((hc 0 h0S).trans (hc 1 h1S).symm)
    simp only [φ.right_inv 0 h0S, φ.right_inv 1 h1S] at hh
    exact zero_ne_one hh
  have hopen := ((φ.inverse_holomorphic.analyticOnNhd hSo).is_constant_or_isOpen
    hconv.isPreconnected).resolve_left hnonconstant
  have himage : φ.invFun '' strip = U := by
    apply subset_antisymm
    · rintro q ⟨v, hv, rfl⟩
      exact φ.inverse_mapsTo hv
    · intro q hq
      exact ⟨φ.toFun q, φ.mapsTo hq, φ.left_inv q hq⟩
  rw [← himage]
  exact hopen strip subset_rfl hSo

/-- Pullback of unit density on the open target slab by a holomorphic map. -/
def slabPullbackDensity (a b : ℝ) (f : ℂ → ℂ) (q : ℂ) : ℝ :=
  if (f q).re ∈ Ioo (a - 1 / 2) (b + 1 / 2) then ‖deriv f q‖ else 0

/-- The speed of a vertical image curve is the complex-derivative norm,
including the common restriction to the target slab. -/
theorem vertical_slab_speed_eq (a b s t : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableAt ℂ f ((s : ℂ) + t * Complex.I)) :
    slabWeightedSpeed a b (fun u : ℝ => f ((s : ℂ) + u * Complex.I)) t =
      slabPullbackDensity a b f ((s : ℂ) + t * Complex.I) := by
  have hcast : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := t))
  have hline : HasDerivAt (fun u : ℝ => (s : ℂ) + u * Complex.I) Complex.I t := by
    simpa using (hcast.mul_const Complex.I).const_add (s : ℂ)
  have hcomp := hf.hasDerivAt.scomp t hline
  have hderiv : deriv (fun u : ℝ => f ((s : ℂ) + u * Complex.I)) t =
      Complex.I * deriv f ((s : ℂ) + t * Complex.I) := by
    simpa only [Function.comp_def, smul_eq_mul] using! hcomp.deriv
  have hnorm : ‖deriv (fun u : ℝ => f ((s : ℂ) + u * Complex.I)) t‖ =
      ‖deriv f ((s : ℂ) + t * Complex.I)‖ := by
    rw [hderiv, norm_mul, Complex.norm_I, one_mul]
  unfold slabWeightedSpeed slabPullbackDensity
  rw [hnorm]

/-- The conformal pullback density has integral at least one across every interior
tunnel slice for which that density is interval-integrable. -/
theorem tunnel_density_length (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip)
    (hφ0 : φ.toFun (-1) = 0) (hφre : 0 < (deriv φ.toFun (-1)).re)
    (hφim : (deriv φ.toFun (-1)).im = 0)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    (w z : ℂ) (hw : w ∈ passageSlice p n) (hz : z ∈ cleanSlice p n)
    (hwV : w ∈ tract p δ) (hzV : z ∈ tract p δ)
    (hdensity : IntervalIntegrable
      (fun t : ℝ => slabPullbackDensity (φ.toFun w).re
        (max (φ.toFun w).re (φ.toFun z).re) φ.toFun ((s : ℂ) + t * Complex.I))
      volume (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2)) :
    1 ≤ ∫ t in (-p.tunnelHeight n / 2)..(p.tunnelHeight n / 2),
      slabPullbackDensity (φ.toFun w).re (max (φ.toFun w).re (φ.toFun z).re)
        φ.toFun ((s : ℂ) + t * Complex.I) := by
  let a : ℝ := (φ.toFun w).re
  let b : ℝ := max a (φ.toFun z).re
  let γ : ℝ → ℂ := fun t => φ.toFun ((s : ℂ) + t * Complex.I)
  let ρ : ℝ → ℝ := fun t => slabPullbackDensity a b φ.toFun ((s : ℂ) + t * Complex.I)
  have hUo := strip_equivalence_source_isOpen φ
  have hheight := p.tunnel_pos n
  have hle : -p.tunnelHeight n / 2 ≤ p.tunnelHeight n / 2 := by linarith
  have heq : EqOn (slabWeightedSpeed a b γ) ρ
      (uIoo (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2)) := by
    intro t ht
    rw [uIoo_of_le hle] at ht
    apply vertical_slab_speed_eq
    apply φ.holomorphic.differentiableAt
    apply hUo.mem_nhds
    have hcomponent := tunnel_vertical_component p δ n s hs
    have hq : (s : ℂ) + t * Complex.I ∈
        connectedComponentIn (tract p δ ∩ {q : ℂ | q.re = s}) (s : ℂ) := by
      rw [hcomponent]
      have him : |t| < p.tunnelHeight n / 2 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      exact ⟨by simp, by simpa using him⟩
    exact (connectedComponentIn_subset _ _ hq).1
  have hspeed : IntervalIntegrable (slabWeightedSpeed a b γ) volume
      (-p.tunnelHeight n / 2) (p.tunnelHeight n / 2) :=
    hdensity.congr_uIoo heq.symm
  have hlength := tunnel_weighted_length p δ φ hφ0 hφre hφim n s hs w z hw hz
    hwV hzV hspeed
  rw [intervalIntegral.integral_congr_uIoo heq] at hlength
  exact hlength

end MaxModulusPoints.CrosscutDistortion
