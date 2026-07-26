import Chapter02.HallPetresco.HallPetrescoReducedAbelianFactor

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HallPetrescoAbelianSecondCountable

open Chapter02.HallPetrescoReducedAbelianFactor

universe u v

/-- The canonical map from the original homogeneous quotient to its common
abelian factor is open. -/
theorem isOpenMap_originalQuotientToAbelianQuotient
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ : Subgroup H) :
    IsOpenMap (originalQuotientToAbelianQuotient Γ) := by
  let q₁ : H → H ⧸ Γ := fun h ↦ QuotientGroup.mk h
  let q₂ : H → AbelianQuotient Γ := fun h ↦
    QuotientGroup.mk (Abelianization.of h)
  have hq₁surj : Function.Surjective q₁ :=
    QuotientGroup.mk_surjective
  have hcomp :
      originalQuotientToAbelianQuotient Γ ∘ q₁ = q₂ := by
    funext h
    exact originalQuotientToAbelianQuotient_mk Γ h
  have hopenComp :
      IsOpenMap (originalQuotientToAbelianQuotient Γ ∘ q₁) := by
    rw [hcomp]
    exact QuotientGroup.isOpenMap_coe.comp
      QuotientGroup.isOpenMap_coe
  intro U hU
  have hpre : IsOpen (q₁ ⁻¹' U) :=
    hU.preimage QuotientGroup.continuous_mk
  have himage :
      (originalQuotientToAbelianQuotient Γ ∘ q₁) '' (q₁ ⁻¹' U) =
        originalQuotientToAbelianQuotient Γ '' U := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨q₁ h, hh, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h, rfl⟩ := hq₁surj x
      exact ⟨h, hx, rfl⟩
  rw [← himage]
  exact hopenComp (q₁ ⁻¹' U) hpre

/-- The common abelian factor map from the original compact metric model is
open. -/
theorem isOpenMap_modelToAbelianQuotient
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsOpenMap (modelToAbelianQuotient N P) := by
  exact
    (isOpenMap_originalQuotientToAbelianQuotient P.lattice).comp
      P.toQuotient.isOpenMap

/-- The genuine common abelian factor of a compact metric nilsystem is
second countable. -/
noncomputable def abelianQuotientSecondCountableTopology
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    SecondCountableTopology (AbelianQuotient P.lattice) := by
  letI : CompactSpace (AbelianQuotient P.lattice) :=
    abelianQuotientCompactSpace N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  have hcontinuous := continuous_modelToAbelianQuotient N P
  have hquotient : Topology.IsQuotientMap
      (modelToAbelianQuotient N P) :=
    hcontinuous.isClosedMap.isQuotientMap
      hcontinuous (surjective_modelToAbelianQuotient N P)
  exact hquotient.secondCountableTopology
    (isOpenMap_modelToAbelianQuotient N P)

end Chapter02.HallPetrescoAbelianSecondCountable
