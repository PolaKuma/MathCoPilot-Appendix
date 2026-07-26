import Chapter02.Dynamics.CompactMinimalGroupRotationUnique
import Chapter02.HallPetresco.HallPetrescoAbelianSecondCountable

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoAbelianUniqueMean

open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoAbelianSecondCountable

universe u v

/-- The actual common abelian factor carries a unique invariant probability
measure for its minimal rotation. -/
def AbelianUniqueMeanLaw
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) : Prop :=
  letI : CompactSpace (AbelianQuotient P.lattice) :=
    abelianQuotientCompactSpace N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  letI : SecondCountableTopology (AbelianQuotient P.lattice) :=
    abelianQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (AbelianQuotient P.lattice) := inferInstance
  letI : MetricSpace (AbelianQuotient P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MeasurableSpace (AbelianQuotient P.lattice) :=
    borel (AbelianQuotient P.lattice)
  letI : BorelSpace (AbelianQuotient P.lattice) := ⟨rfl⟩
  ∃ ν : ProbabilityMeasure (AbelianQuotient P.lattice),
    Chapter02.CompactUniqueErgodicCesaro.HasUniqueIntegralInvariant
      (abelianStep P.lattice N.translation) ν

/-- Minimality inherited from the original nilrotation proves the preceding
unique-mean law without any measure-theoretic assumption on the factor. -/
theorem abelianUniqueMeanLaw
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    AbelianUniqueMeanLaw N P := by
  letI : CompactSpace (AbelianQuotient P.lattice) :=
    abelianQuotientCompactSpace N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  letI : SecondCountableTopology (AbelianQuotient P.lattice) :=
    abelianQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (AbelianQuotient P.lattice) := inferInstance
  letI : MetricSpace (AbelianQuotient P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MeasurableSpace (AbelianQuotient P.lattice) :=
    borel (AbelianQuotient P.lattice)
  letI : BorelSpace (AbelianQuotient P.lattice) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ :=
    Chapter02.CompactUniqueErgodicCesaro.exists_integralInvariant
      (abelianStep P.lattice N.translation)
      (continuous_abelianStep P.lattice N.translation)
  refine ⟨ν, ?_⟩
  exact
    Chapter02.CompactMinimalGroupRotationUnique.hasUniqueIntegralInvariant_of_everyOrbitHitsOpen
      (QuotientGroup.mk (Abelianization.of N.translation) :
        AbelianQuotient P.lattice)
      (everyOrbitHitsOpen_abelianStep N P) ν hν

end Chapter02.HallPetrescoAbelianUniqueMean
