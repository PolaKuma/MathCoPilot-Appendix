import Chapter02.HallPetresco.HallPetrescoAveragedQuotientMeasure
import Chapter02.HallPetresco.HallPetrescoCentralExtensionMinimality

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoAveragedMinimalPresentation

open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoAveragedQuotientMeasure
open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoQuotientCentralLift
open Chapter02.HostKraStructuredRecurrence

/-- Minimality of the genuine reduced Hall--Petresco quotient turns the
continuous equivariant averaged-measure map into the exact compact minimal
presentation required by the downstream joining argument. -/
theorem hasQuotientMeasurePresentation_of_reduced_minimal
    {H : Type} {X : Type}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (hminimal : EveryOrbitHitsOpen (reducedStep N P.lattice)) :
    letI : CompactSpace (Quotient N P.lattice) := quotientCompactSpace N P
    HasQuotientMeasurePresentation N P m := by
  letI : CompactSpace (Quotient N P.lattice) := quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  let Y := ReducedQuotient N P.lattice
  let S : Y → Y := reducedStep N P.lattice
  let Ψ : Y → ProbabilityMeasure (Quotient N P.lattice) :=
    reducedQuotientAveragedMeasure N P m
  refine ⟨Y, inferInstance, inferInstance,
    ⟨(QuotientGroup.mk 1 : ReducedQuotient N P.lattice)⟩,
    S, Ψ, continuous_reducedQuotientAveragedMeasure N P m,
    ?_, hminimal, ?_⟩
  · intro y
    exact reducedQuotientAveragedMeasure_progression N P m y
  · intro q
    exact centralQuotientMeasure_mem_range_reducedQuotientAveragedMeasure
      N P m q

/-- The remaining vertical-return statement now feeds all the way through
the actual quotient and averaged configuration measures, with no abstract
orbit-realization assumption. -/
theorem hasQuotientMeasurePresentation_of_fullQuadraticFiber
    {H : Type} {X : Type}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (hvertical : HasFullQuadraticFiberOrbitClosure N P.lattice) :
    letI : CompactSpace (Quotient N P.lattice) := quotientCompactSpace N P
    HasQuotientMeasurePresentation N P m := by
  exact hasQuotientMeasurePresentation_of_reduced_minimal N P m
    (everyOrbitHitsOpen_reducedStep_of_fullQuadraticFiber N P hvertical)

/-- Under vertical recurrence, the actual reduced quotient produces the
distinguished configuration-measure orbit used by the Hall--Petresco
joining theorem. -/
theorem exists_geometricOrbit_of_fullQuadraticFiber
    {H : Type} {X : Type}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (hvertical : HasFullQuadraticFiberOrbitClosure N P.lattice) :
    ∃ ν : ProbabilityMeasure (Chapter02.HallPetrescoTwoStepGroup.Vertex → X),
      Chapter02.HallPetrescoCentralMeasures.HasHallPetrescoGeometricOrbit
        N m ν := by
  letI : CompactSpace (Quotient N P.lattice) := quotientCompactSpace N P
  exact exists_geometricOrbit_of_quotientMeasurePresentation N P m
    (hasQuotientMeasurePresentation_of_fullQuadraticFiber
      N P m hvertical)

/-- Consequently every continuous observation on the toral two-step model
has the full compact-minimal correlation orbit required by the checked
sharp central-fiber estimate. -/
theorem exists_correlationOrbit_of_fullQuadraticFiber
    {H : Type} {X : Type}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (hvertical : HasFullQuadraticFiberOrbitClosure N P.lattice)
    (f : C(X, ℝ)) :
    ∃ ν : ProbabilityMeasure (Chapter02.HallPetrescoTwoStepGroup.Vertex → X),
      Chapter02.HostKraHallPetrescoCorrelation.HasHallPetrescoCorrelationOrbit
        m μ (Chapter02.toCompactCentralAction N.centralAction) f
        (Chapter02.HallPetrescoMeasureOrbit.measureOrbitCorrelation N ν f) := by
  letI : CompactSpace (Quotient N P.lattice) := quotientCompactSpace N P
  exact exists_correlationOrbit_of_quotientMeasurePresentation N P m
    (hasQuotientMeasurePresentation_of_fullQuadraticFiber
      N P m hvertical) f

end Chapter02.HallPetrescoAveragedMinimalPresentation
