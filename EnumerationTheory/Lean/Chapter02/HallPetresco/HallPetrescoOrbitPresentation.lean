import Chapter02.HallPetresco.HallPetrescoCentralMeasures
import Chapter02.Dynamics.MinimalFactorOrbitClosure

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HallPetrescoOrbitPresentation

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoCentralMeasures
open Chapter02.HostKraStructuredRecurrence

/-- An operational presentation of the BHK Hall--Petresco nilmanifold as a
compact minimal system factoring equivariantly onto configuration measures.

The last field says that the explicit central parameter measures constructed
from `μ × Haar` are in the image of the nilmanifold factor map. -/
def HasOrbitPresentation
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
  [IsProbabilityMeasure m] : Prop :=
  ∃ Y : Type, ∃ _top : TopologicalSpace Y, ∃ _compact : CompactSpace Y,
    ∃ _nonempty : Nonempty Y, ∃ S : Y → Y,
    ∃ Φ : Y → ProbabilityMeasure (Vertex → X),
      Continuous Φ ∧
      (∀ y, Φ (S y) = measureStep N (Φ y)) ∧
      EveryOrbitHitsOpen S ∧
      ∀ q,
        centralParameterMeasure m μ
            (Chapter02.toCompactCentralAction N.centralAction) q ∈
          Set.range Φ

/-- A compact-minimal equivariant Hall--Petresco presentation constructs
the distinguished joining and proves its complete geometric orbit
properties. -/
theorem exists_geometricOrbit_of_presentation
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (hpresent : HasOrbitPresentation N m) :
    ∃ ν : ProbabilityMeasure (Vertex → X),
      HasHallPetrescoGeometricOrbit N m ν := by
  obtain ⟨Y, topY, compactY, nonemptyY, S, Φ,
      hΦ, hequiv, hminimal, hcentral⟩ := hpresent
  letI : TopologicalSpace Y := topY
  letI : CompactSpace Y := compactY
  obtain ⟨y₀⟩ := nonemptyY
  refine ⟨Φ y₀, ?_, ?_⟩
  · exact
      Chapter02.MinimalFactorOrbitClosure.everyOrbitHitsOpen_orbitClosure_of_factor
        S (measureStep N) (continuous_measureStep N)
        Φ hΦ hequiv hminimal y₀
  · intro q
    obtain ⟨y, hy⟩ := hcentral q
    rw [← hy]
    exact
      Chapter02.MinimalFactorOrbitClosure.factor_mem_orbitClosure_of_minimal
        S (measureStep N) Φ hΦ hequiv hminimal y₀ y

/-- Consequently every continuous observation has the full
Hall--Petresco correlation-orbit representation used by the checked sharp
Fourier argument. -/
theorem exists_correlationOrbit_of_presentation
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (hpresent : HasOrbitPresentation N m)
    (f : C(X, ℝ)) :
    ∃ ν : ProbabilityMeasure (Vertex → X),
      Chapter02.HostKraHallPetrescoCorrelation.HasHallPetrescoCorrelationOrbit
        m μ (Chapter02.toCompactCentralAction N.centralAction) f
        (measureOrbitCorrelation N ν f) := by
  obtain ⟨ν, hν⟩ :=
    exists_geometricOrbit_of_presentation N m hpresent
  exact ⟨ν,
    hasHallPetrescoCorrelationOrbit_of_geometricOrbit N m ν hν f⟩

end Chapter02.HallPetrescoOrbitPresentation
