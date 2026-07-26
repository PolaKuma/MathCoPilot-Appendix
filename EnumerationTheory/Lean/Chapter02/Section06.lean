import Chapter02.Spectral.SpectralMultiplicityCounterexample
import Chapter02.Spectral.WienerInvariant
import Chapter02.Spectral.CyclicMeasureType
import Chapter02.Spectral.SpectralMixing
import Chapter02.Spectral.DirectSumSpectralModel
import Chapter02.Spectral.OrderedSpectralDecomposition
import Chapter02.Spectral.OrderedDirectSum
import Chapter02.Spectral.OrderedSpectralUniqueness
import Chapter02.Spectral.OrderedMultiplicityDecomposition
import Chapter02.Spectral.SpectralClassification

noncomputable section

namespace Chapter02
namespace Section06

universe u

/-- Source: Definition 2.6.1, Chapter 2, Section 6. -/
def singularAbsolutelyContinuousAndIndependentPowersDefinitions
    (μ : CircleMeasureData) : Prop × Prop × Prop :=
  (IsSingularCircleMeasure μ, IsAbsolutelyContinuousCircleMeasure μ,
    HasIndependentPowers μ)

/-- Source: Proposition 2.6.2, Chapter 2, Section 6. -/
theorem riemannLebesgueLemmaForAbsolutelyContinuousCircleMeasures :
    RiemannLebesgueStatement := by
  exact CircleFourier.riemannLebesgue

/-- Source: Theorem 2.6.3, Chapter 2, Section 6. -/
theorem wienerInvariantSubspaceTheorem :
    WienerInvariantSubspaceStatement := by
  exact WienerInvariant.wienerInvariantSubspace

/-- Source: Definition 2.6.4, Chapter 2, Section 6. -/
def unitaryEquivalenceAndCyclicSpectralModelDefinitions
    (D E : HilbertOperatorData.{u}) : Prop × Prop :=
  (UnitarilyEquivalent D E, CyclicSubspaceSpectralProperties D)

/-- Source: Proposition 2.6.5, Chapter 2, Section 6. -/
theorem cyclicSubspaceAndSpectralMeasureProperties (D : HilbertOperatorData.{u}) :
    CyclicSubspaceSpectralProperties D := by
  exact CyclicMeasureType.cyclicSubspaceProperties D

/-- Source: Remark 2.6.6, Chapter 2, Section 6. -/
theorem orthogonalCyclicSubspacesNeedNotHaveMutuallySingularSpectralMeasures
    : OrthogonalCyclicSubspacesCounterexample.{u} := by
  exact SpectralMultiplicityCounterexample.counterexample

/-- Source: Definition 2.6.7, Chapter 2, Section 6. -/
def spectralTypeDefinition (μ : CircleMeasureData) : Set CircleMeasureData :=
  SpectralTypeDefinition μ

/-- Source: Theorem 2.6.8, Chapter 2, Section 6. -/
theorem spectralDecompositionTheoremFormOne (D : HilbertOperatorData.{u}) :
    SpectralDecompositionFormOne D := by
  intro hsep hD
  let hex := OrderedSpectralDecomposition.exists_orderedSpectralDecomposition D hsep hD
  let x := Classical.choose hex
  have hx : IsOrderedSpectralDecomposition D x := Classical.choose_spec hex
  refine ⟨x, hx, ?_⟩
  intro y hy n
  exact OrderedSpectralUniqueness.ordered_components_equivalent D hD x y hx hy n

/-- Source: Remark 2.6.9, Chapter 2, Section 6. -/
def finiteSpectralSequenceRemark (D : HilbertOperatorData.{u}) : Prop :=
  SpectralDecompositionFormOne D

/-- Source: Remark 2.6.10, Chapter 2, Section 6. -/
theorem unitaryEquivalentToDirectSumOfMultiplicationOperators
    (D : HilbertOperatorData.{u}) :
    DirectSumOfCyclicMultiplicationModelsStatement D := by
  exact OrderedDirectSum.directSumStatement D

/-- Source: Definition 2.6.11, Chapter 2, Section 6. -/
def maximalSpectralTypeSpectralSequenceAndMultiplicityDefinitions
    (D : HilbertOperatorData.{u}) : Prop :=
  MaximalSpectralTypeAndMultiplicityDefinitions D

/-- Source: Theorem 2.6.12, Chapter 2, Section 6. -/
theorem unitaryClassifiedByMaximalSpectralTypeAndMultiplicity
    (D : HilbertOperatorData.{u}) :
    SpectralClassificationByMaximalTypeAndMultiplicity D := by
  exact SpectralClassification.classification D

/-- Source: Definition 2.6.13, Chapter 2, Section 6. -/
def spectralKindDefinitions (D : HilbertOperatorData.{u}) :
    Prop × Prop × Prop × Prop × Prop :=
  SpectralKindDefinitions D

/-- Source: Definition 2.6.14, Chapter 2, Section 6. -/
def spectralMultiplicityAndHomogeneousSpectrumDefinitions
    (D : HilbertOperatorData.{u}) : Prop :=
  HomogeneousSpectrumDefinitions D

/-- Source: Theorem 2.6.15, Chapter 2, Section 6. -/
theorem spectralDecompositionTheoremFormTwo (D : HilbertOperatorData.{u}) :
    SpectralDecompositionFormTwo D := by
  intro hsep hD
  obtain ⟨x, hx⟩ :=
    OrderedSpectralDecomposition.exists_orderedSpectralDecomposition D hsep hD
  choose μ hμ _ using fun n ↦ SpectralMeasure.spectralMeasure D hD (x n)
  refine ⟨OrderedMultiplicitySupports.multiplicityStratum μ,
    OrderedMultiplicityVectors.multiplicityVector D hD x μ hμ,
    OrderedMultiplicityVectors.multiplicityMeasure μ, ?_, ?_⟩
  · exact OrderedMultiplicityDecomposition.isMultiplicityDecomposition_of_ordered
      D hD x μ hμ hx.1 hx.2
  · intro C y ν hM n k hnk
    exact OrderedMultiplicityDecomposition.canonical_multiplicity_decomposition_unique
      D hD x μ hμ hx C y ν hM n k hnk

/-- Source: Theorem 2.6.16, Chapter 2, Section 6. -/
theorem spectralCharacterizationsOfErgodicWeakAndStrongMixing
    (M : System.{u}) :
    SpectralCharacterizationsOfMixing M := by
  exact SpectralMixing.spectralCharacterizationsOfMixing M

/-- Source: Problem 2.6.17, Banach's simple Lebesgue spectrum problem. -/
def banachSimpleLebesgueSpectrumProblem : Prop :=
  BanachSimpleLebesgueSpectrumProblem.{u}

end Section06
end Chapter02
