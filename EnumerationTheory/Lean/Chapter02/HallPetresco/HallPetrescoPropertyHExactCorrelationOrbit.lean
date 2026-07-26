import Chapter02.HallPetresco.HallPetrescoCentralMeasures
import Chapter02.HallPetresco.HallPetrescoPropertyHPhaseExclusion
import Chapter02.HallPetresco.HallPetrescoReducedAveragedCorrelation

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HallPetrescoPropertyHExactCorrelationOrbit

open Chapter02.HallPetrescoAveragedQuotientMeasure
open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoCentralMeasures
open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoPropertyHPhaseExclusion
open Chapter02.HallPetrescoQuotientCentralLift
open Chapter02.HallPetrescoReducedAveragedCorrelation
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HostKraStructuredRecurrence
open Chapter02.NilsystemPropertyHReduction

/-- For every specified reduced base point, property (H) gives the exact
Hall--Petresco correlation-orbit structure of its fiber-averaged
configuration sequence.

Unlike an existential orbit wrapper, this theorem preserves the concrete
sequence that a finite-stage Host--Kra approximation supplies. -/
theorem hasHallPetrescoCorrelationOrbit_reducedAveraged_of_propertyH
    {H : Type} {X : Type}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace
      (Chapter02.HallPetrescoLattice.Quotient N P.lattice)]
    [BorelSpace
      (Chapter02.HallPetrescoLattice.Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (hproperty :
      identityTranslationSubgroup H N.translation = ⊤)
    (q : ReducedQuotient N P.lattice)
    (f : C(X, ℝ)) :
    Chapter02.HostKraHallPetrescoCorrelation.HasHallPetrescoCorrelationOrbit
      m μ (Chapter02.toCompactCentralAction N.centralAction) f
      (measureOrbitCorrelation N
        (reducedAveragedConfigurationMeasure N P m q) f) := by
  letI : CompactSpace
      (Chapter02.HallPetrescoLattice.Quotient N P.lattice) :=
    quotientCompactSpace N P
  have hvertical :
      HasFullQuadraticFiberOrbitClosure N P.lattice :=
    hasFullQuadraticFiberOrbitClosure_of_propertyH N P hproperty
  have hminimal :
      EveryOrbitHitsOpen (reducedStep N P.lattice) :=
    everyOrbitHitsOpen_reducedStep_of_fullQuadraticFiber N P hvertical
  let Φ : ReducedQuotient N P.lattice →
      ProbabilityMeasure
        (Chapter02.HallPetrescoTwoStepGroup.Vertex → X) :=
    reducedAveragedConfigurationMeasure N P m
  have hΦ : Continuous Φ :=
    continuous_reducedAveragedConfigurationMeasure N P m
  have hgeom :
      HasHallPetrescoGeometricOrbit N m
        (reducedAveragedConfigurationMeasure N P m q) := by
    refine ⟨
      hasMinimalMeasureOrbit_reducedAveragedConfigurationMeasure
        N P m q, ?_⟩
    intro r
    obtain ⟨p, hp⟩ :=
      centralQuotientMeasure_mem_range_reducedQuotientAveragedMeasure
        N P m r
    have horbitDense :
        Dense
          (forwardOrbit (reducedStep N P.lattice) q) := by
      rw [dense_iff_inter_open]
      intro U hU hUne
      obtain ⟨n, hn⟩ := hminimal q U hU hUne
      exact ⟨((reducedStep N P.lattice)^[n]) q,
        hn, ⟨n, rfl⟩⟩
    have hpclosure :
        p ∈ closure
          (forwardOrbit (reducedStep N P.lattice) q) := by
      rw [horbitDense.closure_eq]
      exact Set.mem_univ p
    have hΦclosure :
        Φ p ∈ closure
          (Φ ''
            forwardOrbit (reducedStep N P.lattice) q) := by
      apply map_mem_closure hΦ hpclosure
      intro y hy
      exact ⟨y, hy, rfl⟩
    have himage :
        Φ '' forwardOrbit (reducedStep N P.lattice) q ⊆
          forwardOrbit (measureStep N) (Φ q) := by
      rintro _ ⟨y, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      exact
        (reducedAveragedConfigurationMeasure_iterate
          N P m q n).symm
    have hΦorbit :
        Φ p ∈ closure
          (forwardOrbit (measureStep N) (Φ q)) :=
      closure_mono himage hΦclosure
    have hcentral :
        Φ p =
          centralParameterMeasure m μ
            (Chapter02.toCompactCentralAction N.centralAction) r := by
      unfold Φ reducedAveragedConfigurationMeasure
      rw [hp]
      exact
        quotientConfigurationMeasure_centralQuotientMeasure
          N P m r
    rw [← hcentral]
    exact hΦorbit
  exact
    hasHallPetrescoCorrelationOrbit_of_geometricOrbit
      N m (reducedAveragedConfigurationMeasure N P m q)
      hgeom f

end Chapter02.HallPetrescoPropertyHExactCorrelationOrbit
