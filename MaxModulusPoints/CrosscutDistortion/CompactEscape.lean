import MaxModulusPoints.Blueprint.Data
import MaxModulusPoints.CrosscutDistortion.TunnelBoundary
/-!
# Compact-target escape at excluded source endpoints

Along an approach to a point outside the source of a conformal equivalence,
the images eventually avoid every compact subset of the target. This does
not require the images to have a boundary limit.
-/

namespace MaxModulusPoints.CrosscutDistortion

open Set Filter Blueprint
open scoped Topology

/-- Compact target sets have compact inverse images, which an approach to an
excluded source point must eventually avoid. -/
theorem conformal_boundary_avoids_compact {ι : Type*} {l : Filter ι}
    (U W : Set ℂ) (φ : ConformalEquivalence U W) (u : ι → ℂ) (ζ : ℂ)
    (hu : ∀ᶠ i in l, u i ∈ U) (hζ : ζ ∉ U) (huz : Tendsto u l (𝓝 ζ))
    (K : Set ℂ) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∀ᶠ i in l, φ.toFun (u i) ∉ K := by
  have hKinv : IsCompact (φ.invFun '' K) :=
    hK.image_of_continuousOn (φ.inverse_holomorphic.continuousOn.mono hKW)
  have hζnot : ζ ∉ φ.invFun '' K := by
    rintro ⟨v, hv, hvζ⟩
    exact hζ (hvζ ▸ φ.inverse_mapsTo (hKW hv))
  have havoid : ∀ᶠ i in l, u i ∉ φ.invFun '' K :=
    huz.eventually (hKinv.isClosed.isOpen_compl.mem_nhds hζnot)
  filter_upwards [hu, havoid] with i hi hni hφi
  exact hni ⟨φ.toFun (u i), hφi, φ.left_inv _ hi⟩

/-- At either endpoint of an interior tunnel crosscut, images of source
points eventually leave every compact subset of the strip. -/
theorem tunnel_endpoint_avoids_compact {ι : Type*} {l : Filter ι}
    (p : BlockParameters) (δ : GateIndex → ℝ)
    (φ : ConformalEquivalence (tract p δ) strip) (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    (ζ : ℂ) (hζre : ζ.re = s) (hζim : |ζ.im| = p.tunnelHeight n / 2)
    (u : ι → ℂ) (hu : ∀ᶠ i in l, u i ∈ tract p δ)
    (huz : Tendsto u l (𝓝 ζ))
    (K : Set ℂ) (hK : IsCompact K) (hKS : K ⊆ strip) :
    ∀ᶠ i in l, φ.toFun (u i) ∉ K :=
  conformal_boundary_avoids_compact (tract p δ) strip φ u ζ hu
    (tunnel_endpoints_frontier p δ n s hs ζ hζre hζim).2 huz K hK hKS

end MaxModulusPoints.CrosscutDistortion
