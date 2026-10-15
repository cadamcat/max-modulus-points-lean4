import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Instances.Real.Lemmas
/-!
# Pointed kernels of domains with moving gates

The kernel is the largest domain containing the base point whose compact subsets
are eventually contained in the moving sets. Kernel convergence requires the same
kernel for every subsequence, as in the kernel-convergence remark of
Pardo-Simón–Sixsmith, Section 2.
-/

open Set Filter
open scoped Topology

namespace MaxModulusPoints.ConformalKernel

universe u v

/-- Every compact subset of `D` is eventually contained in the moving sets. -/
def EventuallyContainsCompacts {X : Type u} [TopologicalSpace X]
    (D : Set X) (Dseq : ℕ → Set X) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ D → ∀ᶠ n in atTop, K ⊆ Dseq n

/-- The largest open connected set containing `a` with eventual compact inclusion. -/
structure IsPointedKernel {X : Type u} [TopologicalSpace X]
    (a : X) (D : Set X) (Dseq : ℕ → Set X) : Prop where
  isOpen : IsOpen D
  isPreconnected : IsPreconnected D
  base_mem : a ∈ D
  eventuallyContainsCompacts : EventuallyContainsCompacts D Dseq
  maximal : ∀ U : Set X, IsOpen U → IsPreconnected U → a ∈ U →
    EventuallyContainsCompacts U Dseq → U ⊆ D

/-- Every subsequence has the same pointed kernel. -/
def KernelConverges {X : Type u} [TopologicalSpace X]
    (a : X) (D : Set X) (Dseq : ℕ → Set X) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → IsPointedKernel a D (Dseq ∘ φ)

/-- Compact inclusion and locally persistent points of the complement identify every kernel. -/
theorem kernelConverges_of_persistent_complement {X : Type u} [TopologicalSpace X]
    {a : X} {D : Set X} {Dseq : ℕ → Set X}
    (ho : IsOpen D) (hc : IsPreconnected D) (ha : a ∈ D)
    (hin : EventuallyContainsCompacts D Dseq)
    (hout : ∀ z ∉ D, ∀ U : Set X, IsOpen U → z ∈ U →
      ∃ w ∈ U, ∀ᶠ n in atTop, w ∉ Dseq n) :
    KernelConverges a D Dseq := by
  intro φ hφ
  refine ⟨ho, hc, ha, ?_, ?_⟩
  · intro K hK hKD
    exact hφ.tendsto_atTop (hin K hK hKD)
  · intro U hU _ _ hUK z hz
    by_contra hzD
    obtain ⟨w, hw, hnot⟩ := hout z hzD U hU hz
    have hmem := hUK {w} isCompact_singleton (singleton_subset_iff.mpr hw)
    have hnot' := hφ.tendsto_atTop hnot
    obtain ⟨n, hn, hnn⟩ := (hmem.and hnot').exists
    exact hnn (hn (mem_singleton w))

/-- A gate family is cut from a fixed open set by locally finite closed walls.
The part of wall `i` with `level i z < δ i` is the opening. -/
structure GateFamily (X : Type u) [TopologicalSpace X] (ι : Type v) where
  ambient : Set X
  wall : ι → Set X
  level : ι → X → ℝ
  isOpen_ambient : IsOpen ambient
  isClosed_wall : ∀ i, IsClosed (wall i)
  locallyFinite_wall : LocallyFinite wall
  continuous_level : ∀ i, Continuous (level i)

/-- The domain obtained by opening gates of heights `δ`. -/
def GateFamily.domain {X : Type u} [TopologicalSpace X] {ι : Type v}
    (G : GateFamily X ι) (δ : ι → ℝ) : Set X :=
  G.ambient \ ⋃ i, G.wall i ∩ {z | δ i ≤ G.level i z}

/-- Gate incidence is jointly open in the gate heights and the ambient point. -/
theorem GateFamily.isOpen_totalSpace {X : Type u} [TopologicalSpace X]
    {ι : Type v} (G : GateFamily X ι) :
    IsOpen {p : (ι → ℝ) × X | p.2 ∈ G.domain p.1} := by
  let W : ι → Set ((ι → ℝ) × X) :=
    fun i => {p | p.2 ∈ G.wall i ∧ p.1 i ≤ G.level i p.2}
  have hW : LocallyFinite W :=
    (G.locallyFinite_wall.preimage_continuous continuous_snd).subset (fun i _ h => h.1)
  have hWc : ∀ i, IsClosed (W i) := by
    intro i
    exact (G.isClosed_wall i |>.preimage continuous_snd).inter
      (isClosed_le ((continuous_apply i).comp continuous_fst)
        ((G.continuous_level i).comp continuous_snd))
  have heq : {p : (ι → ℝ) × X | p.2 ∈ G.domain p.1} =
      Prod.snd ⁻¹' G.ambient \ ⋃ i, W i := by
    ext p
    simp only [GateFamily.domain, mem_setOf_eq, Set.mem_sdiff, mem_iUnion, mem_inter_iff,
      mem_preimage, W]
  rw [heq]
  exact (G.isOpen_ambient.preimage continuous_snd).sdiff (hW.isClosed_iUnion hWc)

/-- Each fixed gate domain is open. -/
theorem GateFamily.isOpen_domain {X : Type u} [TopologicalSpace X] {ι : Type v}
    (G : GateFamily X ι) (δ : ι → ℝ) : IsOpen (G.domain δ) := by
  exact G.isOpen_totalSpace.preimage (continuous_const.prodMk continuous_id)

/-- Product-topology convergence of gate heights preserves every compact subset of the limit. -/
theorem GateFamily.eventuallyContainsCompacts {X : Type u} [TopologicalSpace X]
    {ι : Type v} (G : GateFamily X ι) {δseq : ℕ → ι → ℝ} {δ : ι → ℝ}
    (hδ : Tendsto δseq atTop (𝓝 δ)) :
    EventuallyContainsCompacts (G.domain δ) (fun n => G.domain (δseq n)) := by
  intro K hK hKD
  have he : ∀ᶠ p in 𝓝 δ, ∀ z ∈ K, z ∈ G.domain p :=
    hK.eventually_forall_of_forall_eventually fun z hz =>
      G.isOpen_totalSpace.mem_nhds (hKD hz)
  exact hδ he

/-- If strict removed wall points are dense at every removed point, converging
opening heights give pointed kernel convergence. -/
theorem GateFamily.kernelConverges {X : Type u} [TopologicalSpace X]
    {ι : Type v} (G : GateFamily X ι) {a : X}
    {δseq : ℕ → ι → ℝ} {δ : ι → ℝ}
    (hδ : Tendsto δseq atTop (𝓝 δ))
    (ha : a ∈ G.domain δ) (hc : IsPreconnected (G.domain δ))
    (hregular : ∀ i z, z ∈ G.ambient → z ∈ G.wall i → δ i ≤ G.level i z →
      z ∈ closure {w | w ∈ G.wall i ∧ δ i < G.level i w}) :
    KernelConverges a (G.domain δ) (fun n => G.domain (δseq n)) := by
  apply kernelConverges_of_persistent_complement (G.isOpen_domain δ) hc ha
    (G.eventuallyContainsCompacts hδ)
  intro z hz U hU hzU
  by_cases hzA : z ∈ G.ambient
  · have hzW : z ∈ ⋃ i, G.wall i ∩ {z | δ i ≤ G.level i z} := by
      by_contra h
      exact hz ⟨hzA, h⟩
    obtain ⟨i, hzi, hlevel⟩ := mem_iUnion.mp hzW
    obtain ⟨w, hwU, hwi, hwlevel⟩ :=
      (mem_closure_iff_nhds.mp (hregular i z hzA hzi hlevel)) U (hU.mem_nhds hzU)
    refine ⟨w, hwU, ?_⟩
    have hcoord : Tendsto (fun n => δseq n i) atTop (𝓝 (δ i)) :=
      ((continuous_apply i).tendsto δ).comp hδ
    filter_upwards [hcoord.eventually (gt_mem_nhds hwlevel)] with n hn hmem
    exact hmem.2 (mem_iUnion.mpr ⟨i, hwi, hn.le⟩)
  · exact ⟨z, hzU, Eventually.of_forall fun _ hmem => hzA hmem.1⟩

#print axioms kernelConverges_of_persistent_complement
#print axioms GateFamily.isOpen_totalSpace
#print axioms GateFamily.isOpen_domain
#print axioms GateFamily.eventuallyContainsCompacts
#print axioms GateFamily.kernelConverges

end MaxModulusPoints.ConformalKernel
