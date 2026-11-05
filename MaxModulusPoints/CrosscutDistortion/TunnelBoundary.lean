module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.CrosscutDistortion.TunnelSlice

/-!
# Boundary endpoints of tunnel crosscuts

The endpoints of the maximal central vertical tunnel segment lie on the
tract frontier. Adding either endpoint to the segment would contradict
maximality of its connected component.
-/


@[expose] public section

namespace MaxModulusPoints.CrosscutDistortion

open Set Blueprint

/-- Both endpoints of an interior tunnel crosscut lie on the tract frontier
and are excluded from the tract, for every choice of gate parameters. -/
theorem tunnel_endpoints_frontier (p : BlockParameters) (δ : GateIndex → ℝ)
    (n : ℕ) (s : ℝ)
    (hs : blockPosition p n + 1 / 2 < s ∧ s < blockPosition p n + 1)
    (ζ : ℂ) (hζre : ζ.re = s) (hζim : |ζ.im| = p.tunnelHeight n / 2) :
    ζ ∈ frontier (tract p δ) ∧ ζ ∉ tract p δ := by
  let H : ℝ := p.tunnelHeight n / 2
  let S : Set ℂ := {z : ℂ | z.re = s ∧ |z.im| < H}
  have hH : 0 < H := half_pos (p.tunnel_pos n)
  have hcomponent : connectedComponentIn (tract p δ ∩ {z : ℂ | z.re = s})
      (s : ℂ) = S := tunnel_vertical_component p δ n s hs
  have hsub : S ⊆ tract p δ ∩ {z : ℂ | z.re = s} := by
    rw [← hcomponent]
    exact connectedComponentIn_subset _ _
  have hpre : IsPreconnected S := by
    rw [← hcomponent]
    exact isPreconnected_connectedComponentIn
  have hbase : (s : ℂ) ∈ S := by simpa [S] using hH
  let f : ℝ → ℂ := fun y => (s : ℂ) + (y : ℂ) * Complex.I
  have hf : Continuous f := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hζeq : f ζ.im = ζ := by
    apply Complex.ext <;> simp [f, hζre]
  have himcl : ζ.im ∈ closure (Ioo (-H) H) := by
    rw [closure_Ioo (by linarith : -H ≠ H)]
    exact abs_le.mp hζim.le
  have himage : f '' Ioo (-H) H ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [S, f] using abs_lt.mpr hy
  have hζcl : ζ ∈ closure S := by
    rw [← hζeq]
    exact closure_mono himage (mem_closure_image hf.continuousAt himcl)
  have hζout : ζ ∉ tract p δ := by
    intro hζin
    have hins : IsPreconnected (insert ζ S) :=
      hpre.subset_closure (subset_insert _ _) (insert_subset hζcl subset_closure)
    have hwhole : insert ζ S ⊆ tract p δ ∩ {z : ℂ | z.re = s} :=
      insert_subset ⟨hζin, hζre⟩ hsub
    have hζcomponent := hins.subset_connectedComponentIn
      (mem_insert_of_mem ζ hbase) hwhole (mem_insert ζ S)
    rw [hcomponent] at hζcomponent
    have hlt : |ζ.im| < p.tunnelHeight n / 2 := hζcomponent.2
    exact (ne_of_lt hlt) hζim
  exact ⟨⟨closure_mono (fun z hz => (hsub hz).1) hζcl,
    fun hζint => hζout (interior_subset hζint)⟩, hζout⟩

end MaxModulusPoints.CrosscutDistortion
