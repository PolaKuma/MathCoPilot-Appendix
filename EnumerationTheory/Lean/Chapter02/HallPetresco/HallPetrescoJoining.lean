import Chapter02.HallPetresco.HallPetrescoMeasureOrbit
import Chapter02.HostKra.HostKraHallPetrescoCorrelation

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HallPetrescoJoining

open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HostKraCentralChangeVariables

/-- The precise measure-theoretic Hall--Petresco joining package used by
BHK Propositions 6.5 and 7.2.

The map `param` supplies the central Hall configurations needed for the
sharp lower bound.  Requiring those measures to lie in the orbit closure
is exactly what permits the same compact minimal orbit to realize both the
modified correlation sequence and every central Hall value. -/
def HasHallPetrescoJoining
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
    (f : C(X, ℝ))
    (ν : ProbabilityMeasure (Vertex → X)) : Prop :=
  HasMinimalMeasureOrbit N ν ∧
    ∃ param :
        (((Fin N.torusDim → Circle) ×
            (Fin N.torusDim → Circle)) ×
          (Fin N.torusDim → Circle)) →
          ProbabilityMeasure (Vertex → X),
      Continuous param ∧
      (∀ q, param q ∈ closure (forwardOrbit (measureStep N) ν)) ∧
      ∀ q,
        measureObservation f (param q) =
          centralHallValue m μ
            (Chapter02.toCompactCentralAction N.centralAction) f
            q.1.1 q.1.2 q.2

/-- A Hall--Petresco joining produces the semantically complete orbit
model used by the already checked central-fiber sharp estimate. -/
theorem hasHallPetrescoCorrelationOrbit_of_joining
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
    (f : C(X, ℝ))
    (ν : ProbabilityMeasure (Vertex → X))
    (hν : HasHallPetrescoJoining N m f ν) :
    Chapter02.HostKraHallPetrescoCorrelation.HasHallPetrescoCorrelationOrbit
      m μ (Chapter02.toCompactCentralAction N.centralAction) f
      (measureOrbitCorrelation N ν f) := by
  obtain ⟨hminimal, param, hparam, hparam_mem, hparam_value⟩ := hν
  let P := ProbabilityMeasure (Vertex → X)
  let T : P → P := measureStep N
  let Q := orbitClosure T ν
  let hT : Continuous T := continuous_measureStep N
  letI : TopologicalSpace Q := inferInstance
  letI : CompactSpace Q :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let S : Q → Q := orbitClosureStep T ν hT
  let q₀ : Q := orbitClosureBase T ν
  let ψ : Q → ℝ := fun q ↦ measureObservation f q.1
  let centralParam :
      (((Fin N.torusDim → Circle) ×
          (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)) → Q :=
    fun q ↦ ⟨param q, hparam_mem q⟩
  refine ⟨Q, inferInstance, inferInstance, S, q₀, ψ, centralParam,
    continuous_orbitClosureStep T ν hT, hminimal,
    (continuous_measureObservation f).comp continuous_subtype_val,
    hparam.subtype_mk _, ?_, ?_⟩
  · intro n
    change measureObservation f (((measureStep N)^[n]) ν) =
      measureObservation f
        (((orbitClosureStep T ν hT)^[n]) (orbitClosureBase T ν)).1
    rw [orbitClosureStep_iterate_base]
  · intro q
    exact hparam_value q

end Chapter02.HallPetrescoJoining
