import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Set Topology

namespace Chapter02.CountableLocallyCompactGroupDiscrete

universe u

/-- A countable Hausdorff Baire topological group is discrete.

The proof is the standard Baire argument: one singleton has nonempty
interior, and homogeneity transports its openness to the identity. -/
theorem discreteTopology_of_countable_of_baire
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [BaireSpace G] [Countable G] :
    DiscreteTopology G := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  obtain ⟨g, hg⟩ :=
    nonempty_interior_of_iUnion_of_closed
      (f := fun g : G ↦ ({g} : Set G))
      (fun _ ↦ isClosed_singleton)
      (by
        ext y
        simp only [Set.mem_iUnion, Set.mem_singleton_iff,
          Set.mem_univ, iff_true]
        exact ⟨y, rfl⟩)
  obtain ⟨x, hx⟩ := hg
  have hxg : x = g := by
    exact Set.mem_singleton_iff.mp (interior_subset hx)
  have hgmem : g ∈ interior ({g} : Set G) := by
    simpa only [hxg] using hx
  have hinterior : interior ({g} : Set G) = {g} := by
    apply Set.Subset.antisymm interior_subset
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hgmem
  have hgopen : IsOpen ({g} : Set G) := by
    rw [← hinterior]
    exact isOpen_interior
  have himage :
      (Homeomorph.mulLeft g⁻¹) '' ({g} : Set G) = {1} := by
    simp
  rw [← himage]
  exact (Homeomorph.mulLeft g⁻¹).isOpenMap _ hgopen

end Chapter02.CountableLocallyCompactGroupDiscrete
