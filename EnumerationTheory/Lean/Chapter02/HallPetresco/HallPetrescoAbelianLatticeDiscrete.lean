import Chapter02.HallPetresco.CountableLocallyCompactGroupDiscrete
import Chapter02.HallPetresco.HallPetrescoReducedAbelianFactor
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Covering.Quotient

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoAbelianLatticeDiscrete

open Chapter02.CountableLocallyCompactGroupDiscrete
open Chapter02.HallPetrescoReducedAbelianFactor

universe u v

/-- The image of the genuine lattice in the common abelian factor is
countable. -/
theorem countable_abelianLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Countable (abelianLattice P.lattice) := by
  letI : DiscreteTopology P.lattice := P.discreteLattice
  letI : Countable P.lattice :=
    countable_of_Lindelof_of_discrete
  let project : P.lattice → abelianLattice P.lattice :=
    fun γ ↦ ⟨Abelianization.of γ.1, ⟨γ.1, γ.2, rfl⟩⟩
  have hproject : Function.Surjective project := by
    rintro ⟨a, ha⟩
    rcases ha with ⟨γ, hγ, rfl⟩
    exact ⟨⟨γ, hγ⟩, rfl⟩
  exact hproject.countable

/-- Under the standard locally compact, second-countable hypotheses of a
nilpotent Lie group, the actual lattice in the common abelian factor is
discrete. -/
noncomputable def abelianLatticeDiscreteTopology
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    DiscreteTopology (abelianLattice P.lattice) := by
  letI : T2Space H := N.t2Ambient
  letI : IsClosed
      (_root_.commutator H : Set H) :=
    N.isClosed_commutator
  letI : IsClosed
      (abelianLattice P.lattice : Set (AbelianFactor H)) :=
    isClosed_abelianLattice N P
  letI : Countable (abelianLattice P.lattice) :=
    countable_abelianLattice N P
  letI : LocallyCompactSpace (abelianLattice P.lattice) :=
    (isClosed_abelianLattice N P).locallyCompactSpace
  exact discreteTopology_of_countable_of_baire
    (abelianLattice P.lattice)

/-- The common abelian quotient projection is a covering map. -/
theorem abelianQuotient_isCoveringMap
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsCoveringMap
      (QuotientGroup.mk :
        AbelianFactor H → AbelianQuotient P.lattice) := by
  letI : T2Space H := N.t2Ambient
  letI : IsClosed
      (_root_.commutator H : Set H) :=
    N.isClosed_commutator
  letI : IsClosed
      (abelianLattice P.lattice : Set (AbelianFactor H)) :=
    isClosed_abelianLattice N P
  letI : DiscreteTopology (abelianLattice P.lattice) :=
    abelianLatticeDiscreteTopology N P
  exact
    ((abelianLattice P.lattice).isQuotientCoveringMap
      (isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap

/-- Hence the common abelian quotient projection is locally a
homeomorphism. -/
theorem abelianQuotient_isLocalHomeomorph
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsLocalHomeomorph
      (QuotientGroup.mk :
        AbelianFactor H → AbelianQuotient P.lattice) :=
  (abelianQuotient_isCoveringMap N P).isLocalHomeomorph

end Chapter02.HallPetrescoAbelianLatticeDiscrete
