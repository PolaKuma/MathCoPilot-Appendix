import Chapter00.Common

noncomputable section

open Classical

namespace Chapter00

theorem properFamily_dual {X : Type*} {F : FurstenbergFamily X}
    (hF : ProperFamily F) : ProperFamily (familyDual F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hA hAB
    intro hBc
    exact hA (hF.1 hBc (Set.compl_subset_compl.mpr hAB))
  · simp [familyDual, hF.2.2]
  · simp [familyDual, hF.2.1]

theorem filterDual_iff_ramsey_of_proper {X : Type*} (F : FurstenbergFamily X)
    (hF : ProperFamily F) : IsFilterDual F ↔ HasRamseyProperty F := by
  constructor
  · intro hDual A B hAB
    by_contra h
    push_neg at h
    have hAc : Aᶜ ∈ familyDual F := by
      change (Aᶜ)ᶜ ∉ F
      simpa using h.1
    have hBc : Bᶜ ∈ familyDual F := by
      change (Bᶜ)ᶜ ∉ F
      simpa using h.2
    have hInter := hDual.2 Aᶜ hAc Bᶜ hBc
    apply hInter
    simpa [Set.compl_inter] using hAB
  · intro hRamsey
    refine ⟨properFamily_dual hF, ?_⟩
    intro A hA B hB
    change (A ∩ B)ᶜ ∉ F
    rw [Set.compl_inter]
    intro hUnion
    rcases hRamsey Aᶜ Bᶜ hUnion with hAc | hBc
    · exact hA hAc
    · exact hB hBc

theorem isFurstenbergFamily_familyProduct {X : Type*} {F G : FurstenbergFamily X}
    (hF : IsFurstenbergFamily F) (hG : IsFurstenbergFamily G) :
    IsFurstenbergFamily (familyProduct F G) := by
  intro A B hA hAB
  rcases hA with ⟨C, hC, D, hD, rfl⟩
  refine ⟨C ∪ B, hF hC Set.subset_union_left,
    D ∪ B, hG hD Set.subset_union_left, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨Or.inr hx, Or.inr hx⟩
  · rintro x ⟨hxC | hxB, hxD | hxB⟩
    · exact hAB ⟨hxC, hxD⟩
    · exact hxB
    · exact hxB
    · exact hxB

theorem properFamily_familyProduct_iff {X : Type*}
    {F G : FurstenbergFamily X} (hF : ProperFamily F) (hG : ProperFamily G) :
    ProperFamily (familyProduct F G) ↔ G ⊆ familyDual F := by
  constructor
  · intro hProd B hB hBc
    apply hProd.2.1
    exact ⟨Bᶜ, hBc, B, hB, (Set.compl_inter_self B).symm⟩
  · intro hIncl
    refine ⟨isFurstenbergFamily_familyProduct hF.1 hG.1, ?_, ?_⟩
    · rintro ⟨C, hC, D, hD, hEq⟩
      have hCD : C ∩ D = ∅ := hEq.symm
      have hSub : C ⊆ Dᶜ := Set.subset_compl_iff_disjoint_right.mpr
        (Set.disjoint_iff_inter_eq_empty.mpr hCD)
      exact (hIncl hD) (hF.1 hC hSub)
    · exact ⟨Set.univ, hF.2.2, Set.univ, hG.2.2, (Set.inter_univ Set.univ).symm⟩

theorem familyProduct_dual_relation {X : Type*}
    {F F₁ F₂ : FurstenbergFamily X}
    (hF : IsFurstenbergFamily F) (hF₁ : IsFurstenbergFamily F₁)
    (hF₂ : IsFurstenbergFamily F₂) :
    familyProduct F₁ F₂ ⊆ F ↔
      familyProduct F₁ (familyDual F) ⊆ familyDual F₂ := by
  constructor
  · intro h A hA
    rcases hA with ⟨B, hB, C, hC, rfl⟩
    intro hComp
    have hDiff : B ∩ (B ∩ C)ᶜ ∈ F :=
      h ⟨B, hB, (B ∩ C)ᶜ, hComp, rfl⟩
    apply hC
    exact hF hDiff (by
      intro x hx
      exact fun hxC => hx.2 ⟨hx.1, hxC⟩)
  · intro h A hA
    rcases hA with ⟨B, hB, C, hC, rfl⟩
    by_contra hInter
    have hDual : (B ∩ C)ᶜ ∈ familyDual F := by
      change ((B ∩ C)ᶜ)ᶜ ∉ F
      simpa using hInter
    have hOut := h ⟨B, hB, (B ∩ C)ᶜ, hDual, rfl⟩
    apply hOut
    exact hF₂ hC (by
      intro x hxC hx
      exact hx.2 ⟨hx.1, hxC⟩)

theorem filterFamily_iff_eq_product {X : Type*} {F : FurstenbergFamily X}
    (hF : ProperFamily F) : IsFilterFamily F ↔ F = familyProduct F F := by
  constructor
  · intro hFilter
    apply Set.Subset.antisymm
    · intro A hA
      exact ⟨A, hA, Set.univ, hF.2.2, (Set.inter_univ A).symm⟩
    · rintro A ⟨B, hB, C, hC, rfl⟩
      exact hFilter.2 B hB C hC
  · intro hEq
    refine ⟨hF, ?_⟩
    intro A hA B hB
    rw [hEq]
    exact ⟨A, hA, B, hB, rfl⟩

theorem filterFamily_product_dual {X : Type*} {F : FurstenbergFamily X}
    (hF : IsFilterFamily F) :
    F ⊆ familyProduct F (familyDual F) ∧
      familyProduct F (familyDual F) = familyDual F := by
  have hDual := properFamily_dual hF.1
  constructor
  · intro A hA
    exact ⟨A, hA, Set.univ, hDual.2.2, (Set.inter_univ A).symm⟩
  · apply Set.Subset.antisymm
    · rintro A ⟨B, hB, C, hC, rfl⟩
      intro hComp
      have hBad : B ∩ (B ∩ C)ᶜ ∈ F := hF.2 B hB (B ∩ C)ᶜ hComp
      exact hC (hF.1.1 hBad (by
        intro x hx
        exact fun hxC => hx.2 ⟨hx.1, hxC⟩))
    · intro A hA
      exact ⟨Set.univ, hF.1.2.2, A, hA, (Set.univ_inter A).symm⟩

theorem mem_dual_product_dual_iff {X : Type*} {F : FurstenbergFamily X}
    (hF : ProperFamily F) (A : Set X) :
    A ∈ familyDual (familyProduct F (familyDual F)) ↔
      ∀ B ∈ F, A ∩ B ∈ F := by
  have hDual := properFamily_dual hF
  have hProdUp := isFurstenbergFamily_familyProduct hF.1 hDual.1
  constructor
  · intro hA B hB
    by_contra hAB
    apply hA
    apply hProdUp
      (show B ∩ (A ∩ B)ᶜ ∈ familyProduct F (familyDual F) from
        ⟨B, hB, (A ∩ B)ᶜ, (by
          change ((A ∩ B)ᶜ)ᶜ ∉ F
          simpa using hAB), rfl⟩)
    intro x hx
    exact fun hxA => hx.2 ⟨hxA, hx.1⟩
  · intro hStable
    rintro ⟨B, hB, C, hC, hEq⟩
    have hAB := hStable B hB
    apply hC
    apply hF.1 hAB
    intro x hx
    intro hxC
    have hxAc : x ∈ Aᶜ := by
      rw [hEq]
      exact ⟨hx.2, hxC⟩
    exact hxAc hx.1

theorem maximalFilterInsideFamily {X : Type*} {F : FurstenbergFamily X}
    (hF : ProperFamily F) :
    IsFilterFamily (familyDual (familyProduct F (familyDual F))) ∧
      familyDual (familyProduct F (familyDual F)) ⊆ F ∩ familyDual F ∧
      ∀ G : FurstenbergFamily X,
        familyProduct G F ⊆ F →
          G ⊆ familyDual (familyProduct F (familyDual F)) := by
  let H := familyDual (familyProduct F (familyDual F))
  have hMem (A : Set X) : A ∈ H ↔ ∀ B ∈ F, A ∩ B ∈ F :=
    mem_dual_product_dual_iff hF A
  have hHFilter : IsFilterFamily H := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro A B hA hAB
      apply (hMem B).mpr
      intro C hC
      exact hF.1 ((hMem A).mp hA C hC) (Set.inter_subset_inter_left C hAB)
    · intro hEmpty
      have := (hMem ∅).mp hEmpty Set.univ hF.2.2
      exact hF.2.1 (by simpa using this)
    · apply (hMem Set.univ).mpr
      intro B hB
      simpa using hB
    · intro A hA B hB
      apply (hMem (A ∩ B)).mpr
      intro C hC
      have hBC := (hMem B).mp hB C hC
      have hABC := (hMem A).mp hA (B ∩ C) hBC
      simpa [Set.inter_assoc] using hABC
  refine ⟨hHFilter, ?_, ?_⟩
  · intro A hA
    have hStable := (hMem A).mp hA
    refine ⟨?_, ?_⟩
    · simpa using hStable Set.univ hF.2.2
    · intro hAc
      have hEmpty := hStable Aᶜ hAc
      exact hF.2.1 (by simpa using hEmpty)
  · intro G hGF A hA
    apply (hMem A).mpr
    intro B hB
    exact hGF ⟨A, hA, B, hB, rfl⟩

theorem furstenbergProductDualFilterCharacterizations_of_proper {X : Type*}
    (F F₁ F₂ : FurstenbergFamily X)
    (hF : ProperFamily F) (hF₁ : ProperFamily F₁) (hF₂ : ProperFamily F₂) :
    (ProperFamily (familyProduct F₁ F₂) ↔ F₂ ⊆ familyDual F₁) ∧
      (familyProduct F₁ F₂ ⊆ F ↔ familyProduct F₁ (familyDual F) ⊆ familyDual F₂) ∧
      (ProperFamily F → (IsFilterFamily F ↔ F = familyProduct F F)) ∧
      (IsFilterFamily F → F ⊆ familyProduct F (familyDual F) ∧
        familyProduct F (familyDual F) = familyDual F) ∧
      (ProperFamily F →
        IsFilterFamily (familyDual (familyProduct F (familyDual F))) ∧
        familyDual (familyProduct F (familyDual F)) ⊆ F ∩ familyDual F ∧
        ∀ G : FurstenbergFamily X,
          familyProduct G F ⊆ F → G ⊆ familyDual (familyProduct F (familyDual F))) := by
  exact ⟨properFamily_familyProduct_iff hF₁ hF₂,
    familyProduct_dual_relation hF.1 hF₁.1 hF₂.1,
    fun _ => filterFamily_iff_eq_product hF,
    filterFamily_product_dual,
    fun _ => maximalFilterInsideFamily hF⟩

/-- The minimal correction of Proposition 0.6.2: only the two factors in the
first product characterization must be proper.  The ambient family `F` needs
only upward closure, exactly as in the original statement. -/
theorem furstenbergProductDualFilterCharacterizations_of_factor_proper {X : Type*}
    (F F₁ F₂ : FurstenbergFamily X)
    (hF : IsFurstenbergFamily F) (hF₁ : ProperFamily F₁)
    (hF₂ : ProperFamily F₂) :
    (ProperFamily (familyProduct F₁ F₂) ↔ F₂ ⊆ familyDual F₁) ∧
      (familyProduct F₁ F₂ ⊆ F ↔
        familyProduct F₁ (familyDual F) ⊆ familyDual F₂) ∧
      (ProperFamily F → (IsFilterFamily F ↔ F = familyProduct F F)) ∧
      (IsFilterFamily F → F ⊆ familyProduct F (familyDual F) ∧
        familyProduct F (familyDual F) = familyDual F) ∧
      (ProperFamily F →
        IsFilterFamily (familyDual (familyProduct F (familyDual F))) ∧
        familyDual (familyProduct F (familyDual F)) ⊆ F ∩ familyDual F ∧
        ∀ G : FurstenbergFamily X,
          familyProduct G F ⊆ F →
            G ⊆ familyDual (familyProduct F (familyDual F))) := by
  refine ⟨properFamily_familyProduct_iff hF₁ hF₂,
    familyProduct_dual_relation hF hF₁.1 hF₂.1, ?_,
    filterFamily_product_dual, ?_⟩
  · intro hFproper
    exact filterFamily_iff_eq_product hFproper
  · intro hFproper
    exact maximalFilterInsideFamily hFproper

end Chapter00
