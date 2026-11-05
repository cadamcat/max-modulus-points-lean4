module

public import MaxModulusPoints.Blueprint.Data
public import MaxModulusPoints.Blueprint.Interfaces.StripMapData
public import MaxModulusPoints.Construction.OpenChamberGeometry
public import MaxModulusPoints.Construction.OpenChamberPath
public import MaxModulusPoints.Construction.OpenGate
public import MaxModulusPoints.Construction.StripClearance
public import MaxModulusPoints.Construction.StripCoordinates
public import MaxModulusPoints.Construction.Tract
public import MaxModulusPoints.Construction.TractMembership

/-!
# Uniform localization of open chamber centres

The compact set in Pardo-Simón–Sixsmith, Proposition 4.1, depends only
on the block number. Physical clearance gives this compact set directly;
the rescaled strip limit then gives a uniform positive proportion of
the value at the clean reference point.
-/


@[expose] public section

namespace MaxModulusPoints.Construction

open Set Metric

noncomputable section

def upperChamberCentre (p : Blueprint.BlockParameters) (i : Blueprint.GateIndex) : ℂ :=
  ⟨Blueprint.slicePosition p i.1, upperChamberHeight i⟩

def openChamberCompact (n : ℕ) : Set ℂ :=
  stripConfinement ((128 * Real.pi / chamberClearance n) * 8)

theorem openChamberCompact_compact (n : ℕ) : IsCompact (openChamberCompact n) :=
  stripConfinement_compact _

theorem openChamberCompact_subset_strip (n : ℕ) : openChamberCompact n ⊆ Blueprint.strip :=
  stripConfinement_subset_strip _

theorem upperChamberCentre_mem_tract (p : Blueprint.BlockParameters)
    (δ : Blueprint.GateIndex → ℝ) (i : Blueprint.GateIndex)
    (hδ : δ i = Blueprint.gateUpper i) : upperChamberCentre p i ∈ Blueprint.tract p δ := by
  apply horizontal_chamber_clearance p δ i hδ
    (x := Blueprint.slicePosition p i.1) ?_ (mem_ball_self (chamberClearance_pos i.1))
  dsimp [Blueprint.slicePosition]
  constructor <;> linarith

/-- Every fully open upper-chamber centre has translated strip coordinates
in one compact set, uniformly in all the remaining geometric parameters. -/
theorem open_chamber_strip_localization (ψ : Blueprint.StripMapData)
    (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
    (i : Blueprint.GateIndex) (hδ : δ i = Blueprint.gateUpper i)
    (G : Blueprint.LogModel (Blueprint.tract p δ)) :
    (stripCoordinates ψ G).toFun (upperChamberCentre p i) -
      (((stripCoordinates ψ G).toFun
        (Blueprint.blockPosition p i.1 + 3 / 2 : ℝ)).re : ℂ) ∈ openChamberCompact i.1 := by
  let x := Blueprint.blockPosition p i.1 + 3 / 2
  let φ := stripCoordinates ψ G
  let α := smoothCorner x (upperChamberHeight i)
  have hstart : α 0 = (x : ℂ) := (smoothCorner_endpoints x _).1
  have hend : α 1 = upperChamberCentre p i := by
    change smoothCorner x (upperChamberHeight i) 1 = upperChamberCentre p i
    rw [(smoothCorner_endpoints x _).2]
    apply Complex.ext
    · dsimp [upperChamberCentre, Blueprint.slicePosition, x]
      ring
    · rfl
  have hinj : InjOn φ.toFun (Blueprint.tract p δ) := by
    intro z hz w hw he
    calc
      z = φ.invFun (φ.toFun z) := (φ.left_inv z hz).symm
      _ = φ.invFun (φ.toFun w) := congrArg φ.invFun he
      _ = w := φ.left_inv w hw
  have hxmem : (x : ℂ) ∈ Blueprint.tract p δ := by
    apply real_mem_tract
    have hp := (blockParametersLayout p).base_nonneg i.1
    change 0 ≤ Blueprint.blockPosition p i.1 at hp
    dsimp [x]
    linarith
  have hreal : (φ.toFun (α 0)).im = 0 := by
    rw [hstart]
    exact stripCoordinates_real ψ G hxmem
  have hc := strip_map_curve_confinement (chamberClearance_pos i.1)
    (by norm_num : (0 : ℝ) ≤ 8) φ.holomorphic hinj φ.mapsTo
    (smoothCorner_clearance p δ i hδ)
    (fun t _ => (hasDerivAt_smoothCorner x (upperChamberHeight i) t).differentiableAt)
    (smoothCorner_speed x i) hreal
  have he := hc (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  change φ.toFun (α 1) - ((φ.toFun (α 0)).re : ℂ) ∈ openChamberCompact i.1 at he
  rwa [hend, hstart] at he

/-- The constants in the open-chamber lower bound depend only on the block,
not on its chamber, the other gates, or any later spacing and tunnel choices. -/
theorem uniform_open_chamber_lower (ψ : Blueprint.StripMapData) (n : ℕ) :
    ∃ c B : ℝ, 0 < c ∧ c < 1 ∧ 0 < B ∧
      ∀ (p : Blueprint.BlockParameters) (δ : Blueprint.GateIndex → ℝ)
        (m : Fin (n + 1)), δ ⟨n, m⟩ = Blueprint.gateUpper ⟨n, m⟩ →
      ∀ G : Blueprint.LogModel (Blueprint.tract p δ),
        B ≤ ((stripCoordinates ψ G).toFun
          (Blueprint.blockPosition p n + 3 / 2 : ℝ)).re →
        c * (G.toFun (Blueprint.blockPosition p n + 3 / 2 : ℝ)).re ≤
          (G.toFun (upperChamberCentre p ⟨n, m⟩)).re := by
  obtain ⟨c, B, hc, hc1, hB, hbound⟩ := uniform_strip_translate_lower ψ
    (openChamberCompact_compact n) (openChamberCompact_subset_strip n)
  refine ⟨c, B, hc, hc1, hB, ?_⟩
  intro p δ m hδ G hb
  let φ := stripCoordinates ψ G
  let x := Blueprint.blockPosition p n + 3 / 2
  let b := (φ.toFun (x : ℂ)).re
  let ξ := upperChamberCentre p ⟨n, m⟩
  let η := φ.toFun ξ - (b : ℂ)
  have hη : η ∈ openChamberCompact n := open_chamber_strip_localization ψ p δ ⟨n, m⟩ hδ G
  have hξ : ξ ∈ Blueprint.tract p δ := upperChamberCentre_mem_tract p δ ⟨n, m⟩ hδ
  have hxmem : (x : ℂ) ∈ Blueprint.tract p δ := by
    apply real_mem_tract
    have hp := (blockParametersLayout p).base_nonneg n
    change 0 ≤ Blueprint.blockPosition p n at hp
    dsimp [x]
    linarith
  have hφreal : φ.toFun (x : ℂ) = (b : ℂ) := by
    apply Complex.ext
    · rfl
    · exact stripCoordinates_real ψ G hxmem
  have href : ψ.toFun (b : ℂ) = G.toFun (x : ℂ) := by
    rw [← hφreal]
    exact ψ.right_inv _ (G.mapsTo hxmem)
  have hcentre : ψ.toFun ((b : ℂ) + η) = G.toFun ξ := by
    have he : (b : ℂ) + η = φ.toFun ξ := by dsimp [η]; ring
    rw [he]
    exact ψ.right_inv _ (G.mapsTo hξ)
  have h := hbound b hb η hη
  rwa [href, hcentre] at h

#print axioms open_chamber_strip_localization
#print axioms uniform_open_chamber_lower

end

end MaxModulusPoints.Construction
