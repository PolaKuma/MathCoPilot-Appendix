import Chapter02.HallPetresco.HallPetrescoAveragedQuotientMeasure
import Chapter02.HallPetresco.HallPetrescoReducedOrbitObservation
import Chapter02.Dynamics.MinimalFactorOrbitClosure

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoReducedAveragedCorrelation

open Chapter02.HallPetrescoAveragedQuotientMeasure
open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoQuotientCentralLift
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedOrbitObservation
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HostKraStructuredRecurrence

universe u v

/-- Push the fiber-averaged measure attached to a reduced
Hall--Petresco point to the four-coordinate configuration space. -/
def reducedAveragedConfigurationMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (q : ReducedQuotient N P.lattice) :
    ProbabilityMeasure (Chapter02.HallPetrescoTwoStepGroup.Vertex → X) :=
  quotientConfigurationMeasure N P
    (reducedQuotientAveragedMeasure N P m q)

/-- Reduced progression translation becomes the progression pushforward
on the associated configuration measure. -/
theorem reducedAveragedConfigurationMeasure_progression
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (q : ReducedQuotient N P.lattice) :
    reducedAveragedConfigurationMeasure N P m
        (reducedStep N P.lattice q) =
      measureStep N (reducedAveragedConfigurationMeasure N P m q) := by
  unfold reducedAveragedConfigurationMeasure
  rw [reducedQuotientAveragedMeasure_progression]
  simpa only [quotientMeasureStep] using
    quotientConfigurationMeasure_map_quotientStep N P
      (reducedQuotientAveragedMeasure N P m q)

/-- The preceding equivariance holds for every forward iterate. -/
theorem reducedAveragedConfigurationMeasure_iterate
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (q : ReducedQuotient N P.lattice) (n : ℕ) :
    reducedAveragedConfigurationMeasure N P m
        (((reducedStep N P.lattice)^[n]) q) =
      ((measureStep N)^[n])
        (reducedAveragedConfigurationMeasure N P m q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        Function.iterate_succ_apply',
        reducedAveragedConfigurationMeasure_progression, ih]

/-- The reduced-point-to-configuration-measure map is continuous. -/
theorem continuous_reducedAveragedConfigurationMeasure
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] :
    Continuous (reducedAveragedConfigurationMeasure N P m) :=
  (continuous_quotientConfigurationMeasure N P).comp
    (continuous_reducedQuotientAveragedMeasure N P m)

/-- The full configuration-measure orbit closure of a fiber-averaged
joining attached to one reduced point is minimal.  This is the
observation-independent form of the pointwise result. -/
theorem hasMinimalMeasureOrbit_reducedAveragedConfigurationMeasure
    {H : Type u} {X : Type v}
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
    (q : ReducedQuotient N P.lattice) :
    HasMinimalMeasureOrbit N
      (reducedAveragedConfigurationMeasure N P m q) := by
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  let R : ReducedQuotient N P.lattice →
      ReducedQuotient N P.lattice :=
    reducedStep N P.lattice
  let Q := orbitClosure R q
  letI : CompactSpace Q :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let S : Q → Q :=
    orbitClosureStep R q (continuous_reducedStep N P.lattice)
  let Φ : Q →
      ProbabilityMeasure (Chapter02.HallPetrescoTwoStepGroup.Vertex → X) :=
    fun y ↦ reducedAveragedConfigurationMeasure N P m y.1
  have hΦ : Continuous Φ :=
    (continuous_reducedAveragedConfigurationMeasure N P m).comp
      continuous_subtype_val
  have hequiv (y : Q) :
      Φ (S y) = measureStep N (Φ y) :=
    reducedAveragedConfigurationMeasure_progression N P m y.1
  have hsource : EveryOrbitHitsOpen S :=
    everyOrbitHitsOpen_reducedStep_orbitClosure N P q
  have hfactor :=
    Chapter02.MinimalFactorOrbitClosure.everyOrbitHitsOpen_orbitClosure_of_factor
      S (measureStep N) (continuous_measureStep N)
      Φ hΦ hequiv hsource (orbitClosureBase R q)
  simpa only [HasMinimalMeasureOrbit, Φ, orbitClosureBase] using hfactor

/-- Every actual fiber-averaged Hall--Petresco joining obtained from one
reduced point has a compact-minimal scalar correlation orbit.  No global
minimality of the entire reduced quotient is required. -/
theorem isMinimalOrbitSequence_reducedAveragedCorrelation
    {H : Type u} {X : Type v}
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
    (q : ReducedQuotient N P.lattice)
    (f : C(X, ℝ)) :
    IsMinimalOrbitSequence.{u}
      (measureOrbitCorrelation N
        (reducedAveragedConfigurationMeasure N P m q) f) := by
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  let ψ : ReducedQuotient N P.lattice → ℝ :=
    fun y ↦ measureObservation f
      (reducedAveragedConfigurationMeasure N P m y)
  have hψ : Continuous ψ :=
    (continuous_measureObservation f).comp
      (continuous_reducedAveragedConfigurationMeasure N P m)
  have hminimal :
      IsMinimalOrbitSequence.{u}
        (fun n ↦ ψ (((reducedStep N P.lattice)^[n]) q)) :=
    isMinimalOrbitSequence_reducedOrbitObservation N P q ψ hψ
  have heq :
      measureOrbitCorrelation N
          (reducedAveragedConfigurationMeasure N P m q) f =
        fun n ↦ ψ (((reducedStep N P.lattice)^[n]) q) := by
    funext n
    unfold measureOrbitCorrelation ψ
    rw [reducedAveragedConfigurationMeasure_iterate]
  rw [heq]
  exact hminimal

end Chapter02.HallPetrescoReducedAveragedCorrelation
