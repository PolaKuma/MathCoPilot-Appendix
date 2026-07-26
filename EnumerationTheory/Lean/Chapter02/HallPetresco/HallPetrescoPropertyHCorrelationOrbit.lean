import Chapter02.HallPetresco.HallPetrescoAveragedMinimalPresentation
import Chapter02.HallPetresco.HallPetrescoPropertyHPhaseExclusion

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoPropertyHCorrelationOrbit

open Chapter02.HallPetrescoAveragedMinimalPresentation
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoPropertyHPhaseExclusion
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.NilsystemPropertyHReduction

/-- A genuinely presented toral two-step nilsystem satisfying property (H)
supplies the compact minimal Hall--Petresco correlation orbit used by the
checked sharp central-fiber estimate. -/
theorem exists_correlationOrbit_of_propertyH
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
    (hproperty :
      identityTranslationSubgroup H N.translation = ⊤)
    (f : C(X, ℝ)) :
    ∃ ν : ProbabilityMeasure
        (Chapter02.HallPetrescoTwoStepGroup.Vertex → X),
      Chapter02.HostKraHallPetrescoCorrelation.HasHallPetrescoCorrelationOrbit
        m μ (Chapter02.toCompactCentralAction N.centralAction) f
        (Chapter02.HallPetrescoMeasureOrbit.measureOrbitCorrelation
          N ν f) := by
  exact exists_correlationOrbit_of_fullQuadraticFiber N P m
    (hasFullQuadraticFiberOrbitClosure_of_propertyH N P hproperty) f

end Chapter02.HallPetrescoPropertyHCorrelationOrbit
