import Chapter02.HallPetresco.HallPetrescoReducedAveragedCorrelation
import Chapter02.HallPetresco.HallPetrescoReducedSecondCountable
import Chapter02.HostKra.HostKraHallPetrescoUniformMean
import Chapter02.HallPetresco.CompactCentralCubeSurjective

open Classical Filter MeasureTheory

noncomputable section

set_option maxHeartbeats 2000000

namespace Chapter02.HallPetrescoReducedUniqueMean

open Chapter02.HallPetrescoAveragedQuotientMeasure
open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedSecondCountable

universe u v

/-- The exact invariant-measure theorem still required on the actual
reduced Hall--Petresco quotient.  It states both unique invariance of the
progression translation and the BHK central Haar formula for every
continuous fourfold observation after fiber averaging. -/
def ReducedUniqueMeanLaw
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
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] : Prop :=
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  letI : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MeasurableSpace (ReducedQuotient N P.lattice) :=
    borel (ReducedQuotient N P.lattice)
  letI : BorelSpace (ReducedQuotient N P.lattice) := ⟨rfl⟩
  ∃ ν : ProbabilityMeasure (ReducedQuotient N P.lattice),
    Chapter02.CompactUniqueErgodicCesaro.HasUniqueIntegralInvariant
      (reducedStep N P.lattice) ν ∧
    ∀ f : C(X, ℝ),
      (∫ q, measureObservation f
          (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
            N P m q)
        ∂(ν : Measure (ReducedQuotient N P.lattice))) =
        ∫ g, ∫ h, ∫ z,
          Chapter02.HostKraCentralChangeVariables.centralHallValue
            m μ
            (Chapter02.toCompactCentralAction N.centralAction)
            f g h z ∂m ∂m ∂m

/-- The precise Parry equidistribution statement on the genuine reduced
Hall--Petresco quotient: every invariant probability measure has the same
continuous observation integrals, namely the central Haar formula. -/
def ReducedInvariantIntegralIdentification
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
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] : Prop :=
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  letI : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MeasurableSpace (ReducedQuotient N P.lattice) :=
    borel (ReducedQuotient N P.lattice)
  letI : BorelSpace (ReducedQuotient N P.lattice) := ⟨rfl⟩
  (∀ ρ σ : ProbabilityMeasure (ReducedQuotient N P.lattice),
      Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
          (reducedStep N P.lattice) ρ →
        Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
          (reducedStep N P.lattice) σ →
        ∀ φ : C(ReducedQuotient N P.lattice, ℝ),
          (∫ q, φ q ∂(ρ : Measure (ReducedQuotient N P.lattice))) =
            ∫ q, φ q ∂(σ : Measure (ReducedQuotient N P.lattice))) ∧
    ∀ ν : ProbabilityMeasure (ReducedQuotient N P.lattice),
      Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
        (reducedStep N P.lattice) ν →
      ∀ f : C(X, ℝ),
        (∫ q, measureObservation f
            (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
              N P m q)
          ∂(ν : Measure (ReducedQuotient N P.lattice))) =
          ∫ g, ∫ h, ∫ z,
            Chapter02.HostKraCentralChangeVariables.centralHallValue
              m μ
              (Chapter02.toCompactCentralAction N.centralAction)
              f g h z ∂m ∂m ∂m

/-- It suffices to identify the continuous integrals of every invariant
probability measure on the actual reduced quotient.  Existence then follows
from compactness, while equality of all continuous integrals gives
uniqueness. -/
theorem reducedUniqueMeanLaw_of_invariant_integral_eq
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
    (hidentify : ReducedInvariantIntegralIdentification N P m) :
    ReducedUniqueMeanLaw N P m := by
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  letI : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MeasurableSpace (ReducedQuotient N P.lattice) :=
    borel (ReducedQuotient N P.lattice)
  letI : BorelSpace (ReducedQuotient N P.lattice) := ⟨rfl⟩
  change
    (∀ ρ σ : ProbabilityMeasure (ReducedQuotient N P.lattice),
        Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
            (reducedStep N P.lattice) ρ →
          Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
            (reducedStep N P.lattice) σ →
          ∀ φ : C(ReducedQuotient N P.lattice, ℝ),
            (∫ q, φ q ∂(ρ : Measure (ReducedQuotient N P.lattice))) =
              ∫ q, φ q ∂(σ : Measure (ReducedQuotient N P.lattice))) ∧
      ∀ ν : ProbabilityMeasure (ReducedQuotient N P.lattice),
        Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
          (reducedStep N P.lattice) ν →
        ∀ f : C(X, ℝ),
          (∫ q, measureObservation f
              (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
                N P m q)
            ∂(ν : Measure (ReducedQuotient N P.lattice))) =
            ∫ g, ∫ h, ∫ z,
              Chapter02.HostKraCentralChangeVariables.centralHallValue
                m μ
                (Chapter02.toCompactCentralAction N.centralAction)
                f g h z ∂m ∂m ∂m at hidentify
  obtain ⟨huniqueIntegrals, hmean⟩ := hidentify
  obtain ⟨ν, hν⟩ :=
    Chapter02.CompactUniqueErgodicCesaro.exists_integralInvariant
      (reducedStep N P.lattice) (continuous_reducedStep N P.lattice)
  refine ⟨ν, ?_, hmean ν hν⟩
  apply
    Chapter02.CompactUniqueErgodicCesaro.hasUniqueIntegralInvariant_of_integral_eq
      (reducedStep N P.lattice) ν hν
  intro ρ hρ f
  exact huniqueIntegrals ρ ν hρ hν f

/-- The actual reduced quotient law supplies a unique Hall--Petresco mean
orbit for the fiber-averaged correlation attached to every reduced point. -/
theorem hasUniqueHallPetrescoMeanOrbit
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
    (hlaw : ReducedUniqueMeanLaw N P m)
    (q : ReducedQuotient N P.lattice)
    (f : C(X, ℝ)) :
    Chapter02.HostKraHallPetrescoUniformMean.HasUniqueHallPetrescoMeanOrbit.{0, v, u}
      m μ (Chapter02.toCompactCentralAction N.centralAction) f
      (measureOrbitCorrelation N
        (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
          N P m q) f) := by
  letI : CompactSpace (Quotient N P.lattice) :=
    quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  let metricQ : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MetricSpace (ReducedQuotient N P.lattice) := metricQ
  let measQ : MeasurableSpace (ReducedQuotient N P.lattice) :=
    borel (ReducedQuotient N P.lattice)
  letI : MeasurableSpace (ReducedQuotient N P.lattice) := measQ
  let borelQ : BorelSpace (ReducedQuotient N P.lattice) := ⟨rfl⟩
  letI : BorelSpace (ReducedQuotient N P.lattice) := borelQ
  obtain ⟨ν, hunique, hmean⟩ := hlaw
  let ψ : C(ReducedQuotient N P.lattice, ℝ) :=
    ⟨fun y ↦ measureObservation f
        (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
          N P m y),
      (continuous_measureObservation f).comp
        (Chapter02.HallPetrescoReducedAveragedCorrelation.continuous_reducedAveragedConfigurationMeasure
          N P m)⟩
  refine ⟨ReducedQuotient N P.lattice, metricQ, inferInstance,
    measQ, borelQ, reducedStep N P.lattice, q, ψ, ν,
    continuous_reducedStep N P.lattice, hunique, ?_, hmean f⟩
  intro n
  unfold measureOrbitCorrelation ψ
  change
    measureObservation f
        (((measureStep N)^[n])
          (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
            N P m q)) =
      measureObservation f
        (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
          N P m (((reducedStep N P.lattice)^[n]) q))
  rw [
    Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure_iterate
      N P m q n]

/-- Consequently every genuine reduced fiber-averaged Hall--Petresco
correlation has the sharp translated-uniform fourth-power lower limit. -/
theorem sharp_uniformLiminfAtLeast
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
    [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hlaw : ReducedUniqueMeanLaw N P m)
    (q : ReducedQuotient N P.lattice)
    (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    Chapter02.HostKraU3UniformBlockReduction.HasUniformCesaroLiminfAtLeast
      (measureOrbitCorrelation N
        (Chapter02.HallPetrescoReducedAveragedCorrelation.reducedAveragedConfigurationMeasure
          N P m q) f)
      ((∫ x, f x ∂μ) ^ 4) := by
  exact
    Chapter02.HostKraHallPetrescoUniformMean.sharp_uniformLiminfAtLeast
      m CompactCentralCubeSurjective.torus_cube_surjective
      μ (Chapter02.toCompactCentralAction N.centralAction)
      f hf _
      (hasUniqueHallPetrescoMeanOrbit N P m hlaw q f)

end Chapter02.HallPetrescoReducedUniqueMean
