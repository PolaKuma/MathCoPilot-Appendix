import Chapter00.Section05
import Chapter00.Ergodic.Density
import Chapter00.Ergodic.Furstenberg

noncomputable section

open Classical Filter

namespace Chapter00
namespace Section06

universe u v

/--
Source: Proposition 0.6.1, Chapter 0, Section 6.
Basic identities for the dual operation on proper Furstenberg families and
elementary properties of the family product operation.
-/
theorem furstenbergDualAndProductBasicProperties {X : Type u}
    (F F₁ F₂ : FurstenbergFamily X) (ι : Type v) (Fα : ι -> FurstenbergFamily X)
    (hF : ProperFamily F) (hF₁ : ProperFamily F₁) (hF₂ : ProperFamily F₂)
    (hFα : ∀ a : ι, ProperFamily (Fα a)) :
    familyDual (familyDual F) = F ∧
      (F₁ ⊆ F₂ -> familyDual F₂ ⊆ familyDual F₁) ∧
      familyDual (⋃ a : ι, Fα a) = ⋂ a : ι, familyDual (Fα a) ∧
      familyDual (⋂ a : ι, Fα a) = ⋃ a : ι, familyDual (Fα a) ∧
      F₁ ∪ F₂ ⊆ familyProduct F₁ F₂ ∧
      familyProduct F₁ F₂ = familyProduct F₂ F₁ ∧
      (F₁ ⊆ F₂ -> familyProduct F₁ F ⊆ familyProduct F₂ F) := by
  have hdual (G : FurstenbergFamily X) (hG : ProperFamily G) :
      familyDual (familyDual G) = G := by
    ext A
    simp only [familyDual, Set.mem_setOf_eq, compl_compl, not_not]
  refine ⟨hdual F hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h A hA
    exact fun hAc => hA (h hAc)
  · ext A
    simp only [familyDual, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    push_neg
    rfl
  · ext A
    simp only [familyDual, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    push_neg
    rfl
  · intro A hA
    rcases hA with hA | hA
    · refine ⟨A, hA, Set.univ, hF₂.2.2, ?_⟩
      exact (Set.inter_univ A).symm
    · refine ⟨Set.univ, hF₁.2.2, A, hA, ?_⟩
      exact (Set.univ_inter A).symm
  · ext A
    constructor
    · rintro ⟨B, hB, C, hC, rfl⟩
      exact ⟨C, hC, B, hB, Set.inter_comm B C⟩
    · rintro ⟨B, hB, C, hC, rfl⟩
      exact ⟨C, hC, B, hB, Set.inter_comm B C⟩
  · intro h A
    rintro ⟨B, hB, C, hC, rfl⟩
    exact ⟨B, h hB, C, hC, rfl⟩

/--
Source: Proposition 0.6.2, Chapter 0, Section 6.
Product-dual relations for Furstenberg families; characterization of filters by
`F = F · F`; and maximality of `(F · F*)*`.
-/
theorem furstenbergProductDualFilterCharacterizations {X : Type u}
    (F F₁ F₂ : FurstenbergFamily X)
    (hF : IsFurstenbergFamily F) (hF₁ : ProperFamily F₁)
    (hF₂ : ProperFamily F₂) :
    (ProperFamily (familyProduct F₁ F₂) ↔ F₂ ⊆ familyDual F₁) ∧
      (familyProduct F₁ F₂ ⊆ F ↔ familyProduct F₁ (familyDual F) ⊆ familyDual F₂) ∧
      (ProperFamily F -> (IsFilterFamily F ↔ F = familyProduct F F)) ∧
      (IsFilterFamily F -> F ⊆ familyProduct F (familyDual F) ∧
        familyProduct F (familyDual F) = familyDual F) ∧
      (ProperFamily F ->
        IsFilterFamily (familyDual (familyProduct F (familyDual F))) ∧
        familyDual (familyProduct F (familyDual F)) ⊆ F ∩ familyDual F ∧
        ∀ G : FurstenbergFamily X,
          familyProduct G F ⊆ F -> G ⊆ familyDual (familyProduct F (familyDual F))) := by
  exact furstenbergProductDualFilterCharacterizations_of_factor_proper
    F F₁ F₂ hF hF₁ hF₂

/--
Source: Proposition 0.6.3, Chapter 0, Section 6.
A family is a filter-dual family iff it has the Ramsey property.
-/
theorem filterDualIffRamseyProperty {X : Type u} (F : FurstenbergFamily X) :
    ProperFamily F -> (IsFilterDual F ↔ HasRamseyProperty F) := by
  exact filterDual_iff_ramsey_of_proper F

/--
Source: discussion following Proposition 0.6.2.
The infinite-set family is dual to the cofinite-set family.
-/
theorem infiniteAndCofiniteFamilies :
    IsFurstenbergFamily infiniteSetFamily ∧ IsFilterFamily cofiniteSetFamily ∧
      familyDual infiniteSetFamily = cofiniteSetFamily := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B hA hAB
    exact hA.mono hAB
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro A B hA hAB
      exact hA.subset (Set.compl_subset_compl.mpr hAB)
    · simpa [cofiniteSetFamily] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
    · simp [cofiniteSetFamily]
    · intro A hA B hB
      change (A ∩ B)ᶜ.Finite
      rw [Set.compl_inter]
      exact hA.union hB
  · ext A
    simp [familyDual, infiniteSetFamily, cofiniteSetFamily, Set.not_infinite]

/--
Source: Proposition 0.6.4, Chapter 0, Section 6.
Relations among lower/upper Banach density and lower/upper asymptotic density,
including subadditivity, superadditivity on disjoint sets, complement formulas,
and the resulting density-one filter families.
-/
theorem densityRelationsAndDensityOneFilters (E F : Set ℕ) :
    lowerBanachDensity E ≤ lowerAsymptoticDensity E ∧
      lowerAsymptoticDensity E ≤ upperAsymptoticDensity E ∧
      upperAsymptoticDensity E ≤ upperBanachDensity E ∧
      upperBanachDensity (E ∪ F) ≤ upperBanachDensity E + upperBanachDensity F ∧
      (Disjoint E F ->
        lowerBanachDensity E + lowerBanachDensity F ≤ lowerBanachDensity (E ∪ F)) ∧
      upperAsymptoticDensity (E ∪ F) ≤
        upperAsymptoticDensity E + upperAsymptoticDensity F ∧
      (Disjoint E F ->
        lowerAsymptoticDensity E + lowerAsymptoticDensity F ≤
          lowerAsymptoticDensity (E ∪ F)) ∧
      upperAsymptoticDensity E = 1 - lowerAsymptoticDensity Eᶜ ∧
      upperBanachDensity E = 1 - lowerBanachDensity Eᶜ ∧
      IsFilterFamily densityOneFamily ∧
      IsFilterFamily lowerBanachDensityOneFamily ∧
      familyDual densityOneFamily = {A : Set ℕ | 0 < upperAsymptoticDensity A} ∧
      familyDual lowerBanachDensityOneFamily = {A : Set ℕ | 0 < upperBanachDensity A} := by
  have hDensityFilter : IsFilterFamily densityOneFamily := by
    simpa [densityOneFamily] using
      densityOneFilter_generic lowerAsymptoticDensity upperAsymptoticDensity
        lowerAsymptoticDensity_le_one upperAsymptoticDensity_nonneg
        (fun _ _ h => lowerAsymptoticDensity_mono h)
        lowerAsymptoticDensity_empty lowerAsymptoticDensity_univ
        upperAsymptoticDensity_union_le upperAsymptoticDensity_compl
  have hBanachFilter : IsFilterFamily lowerBanachDensityOneFamily := by
    simpa [lowerBanachDensityOneFamily] using
      densityOneFilter_generic lowerBanachDensity upperBanachDensity
        lowerBanachDensity_le_one upperBanachDensity_nonneg
        (fun _ _ h => lowerBanachDensity_mono h)
        lowerBanachDensity_empty lowerBanachDensity_univ
        upperBanachDensity_union_le upperBanachDensity_compl
  have hDensityDual :
      familyDual densityOneFamily = {A : Set ℕ | 0 < upperAsymptoticDensity A} := by
    simpa [densityOneFamily] using
      densityOneDual_generic lowerAsymptoticDensity upperAsymptoticDensity
        lowerAsymptoticDensity_le_one upperAsymptoticDensity_compl
  have hBanachDual :
      familyDual lowerBanachDensityOneFamily = {A : Set ℕ | 0 < upperBanachDensity A} := by
    simpa [lowerBanachDensityOneFamily] using
      densityOneDual_generic lowerBanachDensity upperBanachDensity
        lowerBanachDensity_le_one upperBanachDensity_compl
  exact ⟨lowerBanachDensity_le_lowerAsymptoticDensity E,
    lowerAsymptoticDensity_le_upperAsymptoticDensity E,
    upperAsymptoticDensity_le_upperBanachDensity E,
    upperBanachDensity_union_le E F,
    fun h => lowerBanachDensity_union_ge_of_disjoint E F h,
    upperAsymptoticDensity_union_le E F,
    fun h => lowerAsymptoticDensity_union_ge_of_disjoint E F h,
    upperAsymptoticDensity_compl E, upperBanachDensity_compl E,
    hDensityFilter, hBanachFilter, hDensityDual, hBanachDual⟩

/--
Source: Proposition 0.6.4, Chapter 0, Section 6.
The same density relations for subsets of `ℤ`.
-/
theorem integerDensityRelationsAndDensityOneFilters (E F : Set ℤ) :
    lowerBanachDensityInt E ≤ lowerAsymptoticDensityInt E ∧
      lowerAsymptoticDensityInt E ≤ upperAsymptoticDensityInt E ∧
      upperAsymptoticDensityInt E ≤ upperBanachDensityInt E ∧
      upperBanachDensityInt (E ∪ F) ≤ upperBanachDensityInt E + upperBanachDensityInt F ∧
      (Disjoint E F ->
        lowerBanachDensityInt E + lowerBanachDensityInt F ≤ lowerBanachDensityInt (E ∪ F)) ∧
      upperAsymptoticDensityInt (E ∪ F) ≤
        upperAsymptoticDensityInt E + upperAsymptoticDensityInt F ∧
      (Disjoint E F ->
        lowerAsymptoticDensityInt E + lowerAsymptoticDensityInt F ≤
          lowerAsymptoticDensityInt (E ∪ F)) ∧
      upperAsymptoticDensityInt E = 1 - lowerAsymptoticDensityInt Eᶜ ∧
      upperBanachDensityInt E = 1 - lowerBanachDensityInt Eᶜ ∧
      IsFilterFamily densityOneFamilyInt ∧
      IsFilterFamily lowerBanachDensityOneFamilyInt ∧
      familyDual densityOneFamilyInt = {A : Set ℤ | 0 < upperAsymptoticDensityInt A} ∧
      familyDual lowerBanachDensityOneFamilyInt = {A : Set ℤ | 0 < upperBanachDensityInt A} := by
  have hDensityFilter : IsFilterFamily densityOneFamilyInt := by
    simpa [densityOneFamilyInt] using
      densityOneFilter_generic lowerAsymptoticDensityInt upperAsymptoticDensityInt
        lowerAsymptoticDensityInt_le_one upperAsymptoticDensityInt_nonneg
        (fun _ _ h => lowerAsymptoticDensityInt_mono h)
        lowerAsymptoticDensityInt_empty lowerAsymptoticDensityInt_univ
        upperAsymptoticDensityInt_union_le upperAsymptoticDensityInt_compl
  have hBanachFilter : IsFilterFamily lowerBanachDensityOneFamilyInt := by
    simpa [lowerBanachDensityOneFamilyInt] using
      densityOneFilter_generic lowerBanachDensityInt upperBanachDensityInt
        lowerBanachDensityInt_le_one upperBanachDensityInt_nonneg
        (fun _ _ h => lowerBanachDensityInt_mono h)
        lowerBanachDensityInt_empty lowerBanachDensityInt_univ
        upperBanachDensityInt_union_le upperBanachDensityInt_compl
  have hDensityDual :
      familyDual densityOneFamilyInt = {A : Set ℤ | 0 < upperAsymptoticDensityInt A} := by
    simpa [densityOneFamilyInt] using
      densityOneDual_generic lowerAsymptoticDensityInt upperAsymptoticDensityInt
        lowerAsymptoticDensityInt_le_one upperAsymptoticDensityInt_compl
  have hBanachDual :
      familyDual lowerBanachDensityOneFamilyInt =
        {A : Set ℤ | 0 < upperBanachDensityInt A} := by
    simpa [lowerBanachDensityOneFamilyInt] using
      densityOneDual_generic lowerBanachDensityInt upperBanachDensityInt
        lowerBanachDensityInt_le_one upperBanachDensityInt_compl
  exact ⟨lowerBanachDensityInt_le_lowerAsymptoticDensityInt E,
    lowerAsymptoticDensityInt_le_upperAsymptoticDensityInt E,
    upperAsymptoticDensityInt_le_upperBanachDensityInt E,
    upperBanachDensityInt_union_le E F,
    fun h => lowerBanachDensityInt_union_ge_of_disjoint E F h,
    upperAsymptoticDensityInt_union_le E F,
    fun h => lowerAsymptoticDensityInt_union_ge_of_disjoint E F h,
    upperAsymptoticDensityInt_compl E, upperBanachDensityInt_compl E,
    hDensityFilter, hBanachFilter, hDensityDual, hBanachDual⟩

end Section06
end Chapter00
