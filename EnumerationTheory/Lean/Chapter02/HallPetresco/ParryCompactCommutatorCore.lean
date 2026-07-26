import Chapter02.HallPetresco.HallPetrescoProgressionReturnLift

open Classical
open Set

noncomputable section

namespace Chapter02.ParryCompactCommutatorCore

open Chapter02.HallPetrescoProgressionReturnLift

/-- Products of a closed subgroup with a compact central commutator layer
form a closed set.  The proof identifies the product with the inverse image
of the compact image of the commutator layer in the left-coset quotient. -/
theorem isClosed_factor_commutator
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (L : Subgroup G)
    (hL : IsClosed (L : Set G))
    (hcompact : IsCompact (_root_.commutator G : Set G))
    (hstep : _root_.commutator G ≤ Subgroup.center G) :
    IsClosed {g : G | ∃ l : G, l ∈ L ∧
      ∃ c : G, c ∈ _root_.commutator G ∧ g = l * c} := by
  letI : T1Space (G ⧸ L) :=
    QuotientGroup.t1Space_iff.mpr hL
  let C : Set G := (_root_.commutator G : Set G)
  have himageCompact :
      IsCompact
        ((QuotientGroup.mk (s := L)) '' C : Set (G ⧸ L)) :=
    hcompact.image QuotientGroup.continuous_mk
  have hcarrier :
      {g : G | ∃ l : G, l ∈ L ∧
          ∃ c : G, c ∈ _root_.commutator G ∧ g = l * c} =
        (QuotientGroup.mk (s := L)) ⁻¹'
          ((QuotientGroup.mk (s := L)) '' C) := by
    ext g
    constructor
    · rintro ⟨l, hl, c, hc, rfl⟩
      refine ⟨c, hc, ?_⟩
      apply QuotientGroup.eq.mpr
      change c⁻¹ * (l * c) ∈ L
      have hcCentral : c ∈ Subgroup.center G := hstep hc
      have hcomm' : c⁻¹ * l = l * c⁻¹ :=
        (Subgroup.mem_center_iff.mp
          ((Subgroup.center G).inv_mem hcCentral) l).symm
      have heq : c⁻¹ * (l * c) = l := by
        calc
          c⁻¹ * (l * c) = (c⁻¹ * l) * c := by
            rw [mul_assoc]
          _ = (l * c⁻¹) * c := by rw [hcomm']
          _ = l := by group
      rw [heq]
      exact hl
    · rintro ⟨c, hc, hgc⟩
      have hrel : g⁻¹ * c ∈ L := QuotientGroup.eq.mp hgc.symm
      let l : G := (g⁻¹ * c)⁻¹
      have hl : l ∈ L := L.inv_mem hrel
      refine ⟨l, hl, c, hc, ?_⟩
      have hcCentral : c ∈ Subgroup.center G := hstep hc
      have hcomm : c⁻¹ * g = g * c⁻¹ :=
        (Subgroup.mem_center_iff.mp
          ((Subgroup.center G).inv_mem hcCentral) g).symm
      dsimp only [l]
      rw [mul_inv_rev, inv_inv, hcomm]
      group
  rw [hcarrier]
  exact himageCompact.isClosed.preimage QuotientGroup.continuous_mk

/-- Swapping the inputs of a commutator inverts it. -/
private theorem commutatorElement_inv
    {G : Type*} [Group G] (x y : G) :
    ⁅x, y⁆⁻¹ = ⁅y, x⁆ := by
  simp only [commutatorElement_def, mul_inv_rev, inv_inv]
  group

/-- In a two-step group, a central factor in the second input does not
change a commutator. -/
private theorem commutatorElement_mul_right_of_center
    {G : Type*} [Group G]
    (hstep : _root_.commutator G ≤ Subgroup.center G)
    (x y c : G) (hc : c ∈ _root_.commutator G) :
    ⁅x, y * c⁆ = ⁅x, y⁆ := by
  have hcentral : c ∈ Subgroup.center G := hstep hc
  have hcomm : ⁅c, x⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hcentral x).symm
  apply inv_injective
  rw [commutatorElement_inv, commutatorElement_inv]
  rw [
    commutatorElement_mul_left_of_commutator_le_center hstep y c x,
    hcomm,
    mul_one]

/-- Algebraic core of the two-step Parry criterion.

If every element of a two-step group factors as an element of `L` times an
element of the full commutator subgroup, then `L` is already the whole
group.  Indeed all commutators of the ambient group reduce to commutators
of elements of `L`. -/
theorem eq_top_of_factor_commutator
    {G : Type*} [Group G]
    (L : Subgroup G)
    (hstep : _root_.commutator G ≤ Subgroup.center G)
    (hfactor :
      ∀ g : G, ∃ l : G, l ∈ L ∧
        ∃ c : G, c ∈ _root_.commutator G ∧ g = l * c) :
    L = ⊤ := by
  have hcomm : _root_.commutator G ≤ L := by
    rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    obtain ⟨l, hl, c, hc, rfl⟩ := hfactor x
    obtain ⟨m, hm, d, hd, rfl⟩ := hfactor y
    rw [
      commutatorElement_mul_left_of_commutator_le_center
        hstep l c (m * d)]
    have hcCentral : c ∈ Subgroup.center G := hstep hc
    have hcComm : ⁅c, m * d⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact (Subgroup.mem_center_iff.mp hcCentral (m * d)).symm
    rw [hcComm, mul_one,
      commutatorElement_mul_right_of_center hstep l m d hd]
    change l * m * l⁻¹ * m⁻¹ ∈ L
    exact L.mul_mem
      (L.mul_mem (L.mul_mem hl hm) (L.inv_mem hl))
      (L.inv_mem hm)
  apply top_unique
  intro g _
  obtain ⟨l, hl, c, hc, rfl⟩ := hfactor g
  exact L.mul_mem hl (hcomm hc)

end Chapter02.ParryCompactCommutatorCore
