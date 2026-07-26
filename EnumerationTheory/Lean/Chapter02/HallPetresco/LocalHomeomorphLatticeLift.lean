import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Tactic

open Classical Filter Set Topology

noncomputable section

namespace Chapter02.LocalHomeomorphLatticeLift

universe u v

/-- A convergent sequence (or net) in a homogeneous quotient with locally
homeomorphic quotient map can be corrected by lattice elements so that it
converges upstairs.

This is the representative-lifting form needed in nilmanifold return
arguments: if the cosets of `r i` converge to the identity coset, then
`r i * γ(i)⁻¹` converges to the group identity for suitable `γ(i) ∈ Γ`. -/
theorem exists_lattice_correction_tendsto_one
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G)
    (hlocal :
      IsLocalHomeomorph
        (QuotientGroup.mk : G → G ⧸ Γ))
    {ι : Type v} {l : Filter ι} (r : ι → G)
    (hr :
      Tendsto
        (fun i ↦ (QuotientGroup.mk (r i) : G ⧸ Γ))
        l
        (𝓝 (QuotientGroup.mk (1 : G) : G ⧸ Γ))) :
    ∃ γ : ι → Γ,
      Tendsto (fun i ↦ r i * (γ i : G)⁻¹) l (𝓝 1) := by
  obtain ⟨e, h1source, he⟩ := hlocal (1 : G)
  let eInv := e.symm
  have he_apply (g : G) :
      (QuotientGroup.mk g : G ⧸ Γ) = e g :=
    congrFun he g
  have hbase :
      (QuotientGroup.mk (1 : G) : G ⧸ Γ) ∈ eInv.source := by
    change (QuotientGroup.mk (1 : G) : G ⧸ Γ) ∈ e.target
    rw [he_apply]
    exact e.map_source h1source
  have hsource :
      ∀ᶠ i in l,
        (QuotientGroup.mk (r i) : G ⧸ Γ) ∈ eInv.source := by
    exact hr (eInv.open_source.mem_nhds hbase)
  have hlift :
      Tendsto
        (fun i ↦ eInv (QuotientGroup.mk (r i) : G ⧸ Γ))
        l
        (𝓝 1) := by
    have hecont :
        ContinuousAt eInv
          (QuotientGroup.mk (1 : G) : G ⧸ Γ) :=
      eInv.continuousAt hbase
    have ht := hecont.tendsto.comp hr
    have hinv :
        eInv (QuotientGroup.mk (1 : G) : G ⧸ Γ) = 1 := by
      change e.symm (QuotientGroup.mk (1 : G) : G ⧸ Γ) = 1
      rw [he_apply]
      exact e.left_inv h1source
    simpa only [hinv] using ht
  have hexists :
      ∀ᶠ i in l, ∃ γ : Γ,
        r i * (γ : G)⁻¹ =
          eInv (QuotientGroup.mk (r i) : G ⧸ Γ) := by
    filter_upwards [hsource] with i hi
    have hquot :
        QuotientGroup.mk
            (eInv (QuotientGroup.mk (r i) : G ⧸ Γ)) =
          (QuotientGroup.mk (r i) : G ⧸ Γ) := by
      rw [he_apply]
      exact e.right_inv hi
    have hmem :
        (eInv (QuotientGroup.mk (r i) : G ⧸ Γ))⁻¹ * r i ∈ Γ :=
      QuotientGroup.eq.mp hquot
    let γ : Γ :=
      ⟨(eInv (QuotientGroup.mk (r i) : G ⧸ Γ))⁻¹ * r i, hmem⟩
    refine ⟨γ, ?_⟩
    change
      r i *
          ((eInv (QuotientGroup.mk (r i) : G ⧸ Γ))⁻¹ * r i)⁻¹ =
        eInv (QuotientGroup.mk (r i) : G ⧸ Γ)
    group
  let γ : ι → Γ := fun i ↦
    if h : ∃ z : Γ,
        r i * (z : G)⁻¹ =
          eInv (QuotientGroup.mk (r i) : G ⧸ Γ)
    then Classical.choose h
    else 1
  refine ⟨γ, ?_⟩
  apply hlift.congr'
  filter_upwards [hexists] with i hi
  dsimp only [γ]
  rw [dif_pos hi]
  exact (Classical.choose_spec hi).symm

end Chapter02.LocalHomeomorphLatticeLift
