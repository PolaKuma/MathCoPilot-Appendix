import Chapter02.Spectral.EigenvalueCountability
import Chapter02.Spectral.SpectralPointMass
import Chapter02.Spectral.Herglotz
import Chapter02.Spectral.CyclicSpectralModel
import Chapter02.Spectral.SpectralRelations
import Chapter02.Spectral.SpectralWiener
import Chapter02.Spectral.SpectralMeasureType
import Chapter02.Spectral.WeakSpectrum
import Chapter02.Spectral.AlmostPeriodic
import Chapter02.Spectral.CompactDiscrete
import Chapter02.Ergodic.AlgebraSubSigma
import Chapter02.Spectral.SeparatedKernelDensity
import Chapter02.Spectral.HilbertSchmidtInvariant

noncomputable section

namespace Chapter02
namespace Section05

universe u

/-- Source: Theorem 2.5.1, Chapter 2, Section 5. -/
theorem eigenvaluePropertiesForErgodicSystems (M : System.{u}) :
    HasEigenvalueProperties M := by
  intro hM
  exact ⟨eigen_norm_modulus M hM,
    eigen_orthogonal M hM,
    same_eigenvalue_proportional M hM,
    eigenvalues_group_property M hM⟩

/-- Source: Remark 2.5.2, Chapter 2, Section 5. -/
theorem eigenspacesAreOneDimensionalAndCountableInSeparableCase (M : System.{u}) :
    EigenspacesAndCountabilityStatement M := by
  exact eigenspaces_countable M

/-- Source: Definition 2.5.3, Chapter 2, Section 5. -/
def almostPeriodicFunctionAndAlgebraDefinitions (M : System.{u})
    (f : M.X -> ℂ) : Prop × Prop :=
  (IsAlmostPeriodicFunction M f, BoundedAlmostPeriodicFunctionsFormAlgebra M)

/-- Source: Theorem 2.5.4, Chapter 2, Section 5. -/
theorem koopmanVonNeumannSpectralMixingTheorem (M : System.{u}) :
    KoopmanVonNeumannSpectralMixingStatement M := by
  intro hM hInv
  exact (WeakSpectrum.weakMixing_iff_continuousSpectrum M hM hInv).symm

/-- Source: Definition 2.5.5, Chapter 2, Section 5. -/
def positiveDefiniteFunctionDefinition (φ : ℤ -> ℂ) : Prop :=
  IsPositiveDefinite φ

/-- Source: Theorem 2.5.6, Chapter 2, Section 5. -/
theorem herglotzTheorem : HerglotzStatement := by
  exact Herglotz.herglotz

/-- Source: Proposition 2.5.7, Chapter 2, Section 5. -/
theorem cyclicSubspaceUnitaryEquivalentToMultiplicationOperator
    (D : HilbertOperatorData.{u}) :
    CyclicSubspaceMultiplicationModelStatement D := by
  exact CyclicSpectralModel.cyclicModel D

/-- Source: Proposition 2.5.8, Chapter 2, Section 5. -/
theorem spectralMeasuresUnderAbsoluteContinuityAndOrthogonalCyclicSubspaces
    (D : HilbertOperatorData.{u}) :
    SpectralMeasureAbsoluteContinuityAndOrthogonality D := by
  exact SpectralRelations.spectralRelations D

/-- Source: Definition 2.5.9, Chapter 2, Section 5. -/
def discreteAndContinuousSpectralSubspaceDefinitions (D : HilbertOperatorData.{u}) :
    Prop :=
  DiscreteContinuousSpectralSubspacesStatement D

/-- Source: Proposition 2.5.10, Chapter 2, Section 5. -/
theorem vectorInDiscreteOrContinuousSpectralSubspaceIffSpectralMeasureType
    (D : HilbertOperatorData.{u}) :
    SpectralSubspaceMeasureTypeStatement D := by
  exact SpectralMeasureType.spectralSubspaceMeasureType D

/-- Source: Remark 2.5.11, Chapter 2, Section 5. -/
theorem eigenvectorSpectralMeasureIsPointMass (D : HilbertOperatorData.{u}) :
    EigenvectorSpectralMeasurePointMassStatement D := by
  exact SpectralPointMass.eigenvector_spectral_measure_point_mass D

/-- Source: Theorem 2.5.12, Chapter 2, Section 5. -/
theorem wienerTheoremForContinuousSpectrum (D : HilbertOperatorData.{u}) :
    WienerTheoremStatement D := by
  exact SpectralWiener.wienerTheorem D

/-- Source: Definition 2.5.13, Chapter 2, Section 5. -/
def almostPeriodicVectorDefinition (D : HilbertOperatorData.{u}) (x : D.H) : Prop :=
  IsAlmostPeriodicVector D x

/-- Source: Theorem 2.5.14, Chapter 2, Section 5. -/
theorem almostPeriodicVectorsEqualDiscreteSpectralSubspace
    (D : HilbertOperatorData.{u}) :
    AlmostPeriodicVectorStatement D := by
  exact AlmostPeriodic.almostPeriodicVector D

/-- Source: Theorem 2.5.15, Chapter 2, Section 5. -/
theorem boundedConjugationInvariantAlgebraComesFromSubSigmaAlgebra
    (M : System.{u}) :
    AlgebraOfBoundedFunctionsStatement M := by
  exact AlgebraSubSigma.algebraOfBoundedFunctions M

/-- Source: Definition 2.5.16, Chapter 2, Section 5. -/
def kroneckerAlgebraHilbertSchmidtDefinitions (M : System.{u}) : Prop × Prop :=
  (KroneckerFactorStatement M,
    ∀ H : M.X × M.X -> ℂ, MeasureTheory.MemLp H 2 (M.μ.prod M.μ) ->
      ∀ f : M.X -> ℂ, M.lpMember 2 f ->
        InKernelRange M H (kernelAction M H f))

/-- Source: Theorem 2.5.17, Chapter 2, Section 5. -/
theorem compactFunctionsAndHilbertSchmidtOperatorsInErgodicSystems
    (M : System.{u}) :
    HilbertSchmidtConsequencesStatement M := by
  intro hErg
  have hM : Chapter01.IsMeasurePreservingSystem M := hErg.1
  refine ⟨?_, ?_, ?_⟩
  · intro H hH hHnonconst
    exact
      ⟨HilbertSchmidtInvariant.kernelRangeSpannedByEigenfunctions
          M hM H hH,
        HilbertSchmidtInvariant.exists_nonconstant_eigenfunction_in_kernelRange
          M hM hErg H hH hHnonconst⟩
  · intro f hfAP hf0 hfT
    exact HilbertSchmidtInvariant.tensorSquare_condExp_ne_zero
      M hM hErg f hfAP hf0 hfT
  · intro hdense
    exact
      HilbertSchmidtConsequences.denseCompactFunctions_imply_dense_integrableKernelRange
        M hM hdense

/-- Source: Theorem 2.5.18, Chapter 2, Section 5. -/
theorem compactSystemIffDiscreteSpectrumWeakMixingIffContinuousSpectrum
    (M : System.{u}) :
    CompactIffDiscreteSpectrumStatement M := by
  exact CompactDiscrete.compactIffDiscreteSpectrumWeakMixingIffContinuousSpectrum M

end Section05
end Chapter02
