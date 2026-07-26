import Chapter02.HallPetresco.HallPetrescoCompactReduced
import Chapter02.HallPetresco.HallPetrescoReducedHausdorff

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HallPetrescoReducedSecondCountable

open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoCompactReduced

universe u v

/-- The canonical factor from the full Hall--Petresco quotient to the
reduced quotient is open. -/
theorem isOpenMap_fullToReduced
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    IsOpenMap (fullToReduced N Γ) := by
  let A := Chapter02.HallPetrescoTwoStepGroup.subgroup N
  let L := Chapter02.HallPetrescoLattice.subgroupLattice N Γ
  let M := averagingNormalSubgroup N
  let R := ReducedGroup N
  let q₁ : A → Quotient N Γ :=
    fun a ↦ QuotientGroup.mk a
  let qM : A → R :=
    fun a ↦ QuotientGroup.mk' M a
  let q₂ : R → ReducedQuotient N Γ :=
    fun r ↦ QuotientGroup.mk r
  have hq₁surj : Function.Surjective q₁ :=
    QuotientGroup.mk_surjective
  have hcomp :
      fullToReduced N Γ ∘ q₁ = q₂ ∘ qM := by
    funext a
    exact fullToReduced_mk N Γ a
  have hopenComp : IsOpenMap (fullToReduced N Γ ∘ q₁) := by
    rw [hcomp]
    exact QuotientGroup.isOpenMap_coe.comp
      QuotientGroup.isOpenMap_coe
  intro U hU
  have hpre : IsOpen (q₁ ⁻¹' U) :=
    hU.preimage QuotientGroup.continuous_mk
  have himage :
      (fullToReduced N Γ ∘ q₁) '' (q₁ ⁻¹' U) =
        fullToReduced N Γ '' U := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨q₁ a, ha, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hq₁surj x
      exact ⟨a, hx, rfl⟩
  rw [← himage]
  exact hopenComp (q₁ ⁻¹' U) hpre

/-- The real reduced Hall--Petresco quotient attached to a compact metric
nilsystem presentation is second countable. -/
noncomputable def reducedQuotientSecondCountableTopology
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    SecondCountableTopology (ReducedQuotient N P.lattice) := by
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  letI : T2Space (Quotient N P.lattice) :=
    quotientT2Space N P
  letI : TopologicalSpace.PseudoMetrizableSpace
      (Quotient N P.lattice) :=
    quotientPseudoMetrizableSpace N P
  letI : SecondCountableTopology (Quotient N P.lattice) := by
    infer_instance
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  have hcontinuous := continuous_fullToReduced N P.lattice
  have hquotient : Topology.IsQuotientMap
      (fullToReduced N P.lattice) :=
    hcontinuous.isClosedMap.isQuotientMap
      hcontinuous (surjective_fullToReduced N P.lattice)
  exact hquotient.secondCountableTopology
    (isOpenMap_fullToReduced N P.lattice)

end Chapter02.HallPetrescoReducedSecondCountable
