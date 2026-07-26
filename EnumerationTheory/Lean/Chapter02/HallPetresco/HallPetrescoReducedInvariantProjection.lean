import Chapter02.HallPetresco.HallPetrescoAbelianUniqueMean
import Chapter02.HallPetresco.HallPetrescoReducedSecondCountable

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoReducedInvariantProjection

open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedSecondCountable
open Chapter02.HallPetrescoAbelianSecondCountable

universe u v

/-- Any two invariant probabilities on the actual reduced quotient induce
the same integrals for all continuous observables pulled back from the
common abelian factor. -/
def ReducedInvariantBaseIdentification
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)] : Prop :=
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
  ∀ ρ σ : ProbabilityMeasure (ReducedQuotient N P.lattice),
    Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
        (reducedStep N P.lattice) ρ →
      Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
        (reducedStep N P.lattice) σ →
      ∀ φ : C(AbelianQuotient P.lattice, ℝ),
        (∫ q, φ (reducedToAbelianQuotient N P.lattice q)
          ∂(ρ : Measure (ReducedQuotient N P.lattice))) =
          ∫ q, φ (reducedToAbelianQuotient N P.lattice q)
            ∂(σ : Measure (ReducedQuotient N P.lattice))

theorem reducedInvariantBaseIdentification
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)] :
    ReducedInvariantBaseIdentification N P := by
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
    Chapter02.HallPetrescoAbelianUniqueMean.abelianUniqueMeanLaw N P
  intro ρ σ hρ hσ φ
  let π : ReducedQuotient N P.lattice → AbelianQuotient P.lattice :=
    reducedToAbelianQuotient N P.lattice
  have hπ : AEMeasurable π (ρ : Measure (ReducedQuotient N P.lattice)) :=
    (continuous_reducedToAbelianQuotient N P.lattice).measurable.aemeasurable
  have hπσ : AEMeasurable π (σ : Measure (ReducedQuotient N P.lattice)) :=
    (continuous_reducedToAbelianQuotient N P.lattice).measurable.aemeasurable
  let ρB : ProbabilityMeasure (AbelianQuotient P.lattice) :=
    ProbabilityMeasure.map ρ hπ
  let σB : ProbabilityMeasure (AbelianQuotient P.lattice) :=
    ProbabilityMeasure.map σ hπσ
  have hmapInvariant
      (τ : ProbabilityMeasure (ReducedQuotient N P.lattice))
      (hτ : Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
        (reducedStep N P.lattice) τ) :
      Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
        (abelianStep P.lattice N.translation)
        (ProbabilityMeasure.map τ
          ((continuous_reducedToAbelianQuotient N P.lattice).measurable.aemeasurable)) := by
    intro f
    simp only [ProbabilityMeasure.toMeasure_map]
    let fS : C(AbelianQuotient P.lattice, ℝ) :=
      f.comp
        ⟨abelianStep P.lattice N.translation,
          continuous_abelianStep P.lattice N.translation⟩
    have hleft :
        (∫ b, fS b
            ∂Measure.map (reducedToAbelianQuotient N P.lattice)
              (τ : Measure (ReducedQuotient N P.lattice))) =
          ∫ q, fS (reducedToAbelianQuotient N P.lattice q)
            ∂(τ : Measure (ReducedQuotient N P.lattice)) :=
      integral_map
        ((continuous_reducedToAbelianQuotient N P.lattice).measurable.aemeasurable)
        fS.continuous.aestronglyMeasurable
    have hright :
        (∫ b, f b
            ∂Measure.map (reducedToAbelianQuotient N P.lattice)
              (τ : Measure (ReducedQuotient N P.lattice))) =
          ∫ q, f (reducedToAbelianQuotient N P.lattice q)
            ∂(τ : Measure (ReducedQuotient N P.lattice)) :=
      integral_map
        ((continuous_reducedToAbelianQuotient N P.lattice).measurable.aemeasurable)
        f.continuous.aestronglyMeasurable
    change
      (∫ b, fS b
          ∂Measure.map (reducedToAbelianQuotient N P.lattice)
            (τ : Measure (ReducedQuotient N P.lattice))) =
        ∫ b, f b
          ∂Measure.map (reducedToAbelianQuotient N P.lattice)
            (τ : Measure (ReducedQuotient N P.lattice))
    rw [hleft, hright]
    let fπ : C(ReducedQuotient N P.lattice, ℝ) :=
      f.comp
        ⟨reducedToAbelianQuotient N P.lattice,
          continuous_reducedToAbelianQuotient N P.lattice⟩
    have hi := hτ fπ
    change
      (∫ q, fS (reducedToAbelianQuotient N P.lattice q)
        ∂(τ : Measure (ReducedQuotient N P.lattice))) =
        ∫ q, f (reducedToAbelianQuotient N P.lattice q)
          ∂(τ : Measure (ReducedQuotient N P.lattice))
    change
      (∫ q, f (reducedToAbelianQuotient N P.lattice
          (reducedStep N P.lattice q))
        ∂(τ : Measure (ReducedQuotient N P.lattice))) =
        ∫ q, f (reducedToAbelianQuotient N P.lattice q)
          ∂(τ : Measure (ReducedQuotient N P.lattice)) at hi
    simp_rw [reducedToAbelianQuotient_reducedStep] at hi
    exact hi
  have hρB : ρB = ν := hν.2 ρB (hmapInvariant ρ hρ)
  have hσB : σB = ν := hν.2 σB (hmapInvariant σ hσ)
  have hρint :
      (∫ q, φ (π q) ∂(ρ : Measure (ReducedQuotient N P.lattice))) =
        ∫ b, φ b ∂(ρB : Measure (AbelianQuotient P.lattice)) := by
    dsimp only [ρB]
    rw [ProbabilityMeasure.toMeasure_map]
    exact (integral_map hπ φ.continuous.aestronglyMeasurable).symm
  have hσint :
      (∫ q, φ (π q) ∂(σ : Measure (ReducedQuotient N P.lattice))) =
        ∫ b, φ b ∂(σB : Measure (AbelianQuotient P.lattice)) := by
    dsimp only [σB]
    rw [ProbabilityMeasure.toMeasure_map]
    exact (integral_map hπσ φ.continuous.aestronglyMeasurable).symm
  rw [hρint, hσint, hρB, hσB]

end Chapter02.HallPetrescoReducedInvariantProjection
