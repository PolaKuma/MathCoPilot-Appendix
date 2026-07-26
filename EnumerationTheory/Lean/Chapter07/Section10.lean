import Chapter07.Section09

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v

namespace Section10

def measurablePowerSystem (M : MeasurableSystem.{u}) (k : ℕ) : MeasurableSystem.{u} where
  X := M.X
  measurableSpace := M.measurableSpace
  μ := M.μ
  T := M.T^[k]

def pullbackSetFamily (T : Type u -> Type u) := T

def preimageFamily {X : Type u} {Y : Type v} (T : X -> Y)
    (A : Set (Set Y)) : Set (Set X) :=
  {B | ∃ C ∈ A, B = T ⁻¹' C}

def MeasureNontrivialPartition (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : Prop :=
  ∀ A ∈ α.atoms, M.μ A < 1

def universalTailJoin (M : MeasurableSystem.{u}) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra
    {A | ∃ α : FiniteMeasurablePartition M, A ∈ tailSigmaAlgebra M α}

/-- Source: Definition 7.10.1. -/
def pinskerAlgebra (M : MeasurableSystem.{u}) : Set (Set M.X) :=
  pinskerSigmaAlgebra M

/-- Source: Remark 7.10.2. -/
theorem zeroEntropyPartitionSigmaAlgebras_formAnAlgebra
    (M : MeasurableSystem.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter00.IsAlgebra (pinskerGenerators M) := by
  sorry

/-- Source: Theorem 7.10.3, assertions (1)--(5). -/
theorem pinskerSigmaAlgebra_characterizations
    (M : MeasurableSystem.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    pinskerSigmaAlgebra M = binaryPinskerCharacterization M ∧
    isSubSigmaAlgebra M (pinskerSigmaAlgebra M) ∧
    (∀ α : FiniteMeasurablePartition M,
      (partitionMeasurableWith M α (pinskerSigmaAlgebra M) ↔
        partitionEntropyRate M α = 0) ∧
      (partitionEntropyRate M α = 0 ↔
        partitionMeasurableWith M α (pastPartitionSigmaAlgebra M α))) ∧
    EqualModuloMeasure M (preimageFamily M.T (pinskerSigmaAlgebra M))
      (pinskerSigmaAlgebra M) ∧
    (∀ k : ℕ, 1 ≤ k ->
      EqualModuloMeasure M (pinskerSigmaAlgebra M)
        (pinskerSigmaAlgebra (measurablePowerSystem M k))) ∧
    (Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T ->
      ∃ inv : M.X -> M.X,
        (∀ x, inv (M.T x) = x ∧ M.T (inv x) = x) ∧
        EqualModuloMeasure M (pinskerSigmaAlgebra M)
          (pinskerSigmaAlgebra { M with T := inv })) := by
  sorry

/-- Source: Remark 7.10.4. -/
theorem zeroEntropy_pastAndInvertibilityConsequences
    (M : MeasurableSystem.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    (∀ α : FiniteMeasurablePartition M,
      partitionEntropyRate M α = 0 ↔
        partitionMeasurableWith M α (pastPartitionSigmaAlgebra M α)) ∧
    (measureEntropy M = 0 ↔
      ∀ α : FiniteMeasurablePartition M,
        partitionMeasurableWith M α (pastPartitionSigmaAlgebra M α)) ∧
    (measureEntropy M = 0 ->
      EqualModuloMeasure M (preimageFamily M.T (measurableSets M)) (measurableSets M)) ∧
    (measureEntropy M = 0 -> ∀ A : Set (Set M.X), isSubSigmaAlgebra M A ->
      preimageFamily M.T A ⊆ A -> EqualModuloMeasure M (preimageFamily M.T A) A) := by
  sorry

/-- Source: Proposition 7.10.5. -/
theorem partitionMeasurableWithPinsker_hasZeroEntropy
    (M : MeasurableSystem.{u}) (η : FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    partitionMeasurableWith M η (pinskerSigmaAlgebra M) ->
        partitionEntropyRate M η = 0 := by
  sorry

def IsPinskerFactor (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) : Prop :=
  Chapter01.IsFactorMap M N π ∧
    EqualModuloMeasure M (preimageFamily π (measurableSets N)) (pinskerSigmaAlgebra M)

/-- Source: Definition 7.10.6. -/
def isPinskerFactor (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (π : M.X -> N.X) : Prop := IsPinskerFactor M N π

/-- Source: Definition 7.10.7. -/
def completelyPositiveEntropy (M : MeasurableSystem.{u}) : Prop :=
  hasCompletelyPositiveEntropy M

/-- Source: Proposition 7.10.8. -/
theorem completelyPositiveEntropy_equivalentPartitionTests
    (M : MeasurableSystem.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    hasCompletelyPositiveEntropy M ↔
      (∀ A : Set M.X, ∀ hA : A ∈ measurableSets M,
        ∀ hAc : Aᶜ ∈ measurableSets M,
        M.μ A ≠ 0 -> M.μ A ≠ 1 ->
          0 < partitionEntropyRate M (binaryPartition M A hA hAc)) ∧
      ∀ α : FiniteMeasurablePartition M, MeasureNontrivialPartition M α ->
        0 < partitionEntropyRate M α := by
  sorry

/-- Source: Lemma 7.10.9. -/
theorem conditionalEntropyLimitsForComparablePartitions
    (M : MeasurableSystem.{u}) (α β γ : FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (partitionRefines M α β ∨ partitionRefines M β α) ->
      Tendsto (fun n : ℕ =>
        conditionalEntropy M (iteratedJoinPartition M α (n + 1))
          (partitionSigmaAlgebra M γ) / (n + 1 : ℝ)) atTop
        (nhds (conditionalEntropy M α
          (sigmaJoin (pastPartitionSigmaAlgebra M α)
            (partitionSigmaAlgebra M γ)))) := by
  sorry

/-- Source: Theorem 7.10.10 (Pinsker formula). -/
theorem pinskerFormula
    (M : MeasurableSystem.{u}) (inv : M.X -> M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T)
    (hinv_eq : ∀ x, inv (M.T x) = x ∧ M.T (inv x) = x)
    (α β : FiniteMeasurablePartition M) :
    partitionEntropyRate M (joinPartition M α β) =
      partitionEntropyRate M β +
        conditionalEntropy M α
          (sigmaJoin (orbitPartitionSigmaAlgebra M inv β)
            (pastPartitionSigmaAlgebra M α)) := by
  sorry

/-- Source: Theorem 7.10.11, relative Pinsker formula. -/
theorem relativePinskerFormula
    (M : MeasurableSystem.{u}) (inv : M.X -> M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T)
    (hinv_eq : ∀ x, inv (M.T x) = x ∧ M.T (inv x) = x)
    (α β : FiniteMeasurablePartition M) (A : Set (Set M.X))
    (hA : isSubSigmaAlgebra M A)
    (hAinv : EqualModuloMeasure M (preimageFamily M.T A) A) :
    conditionalEntropy M (joinPartition M α β)
        (sigmaJoin (sigmaJoin (pastPartitionSigmaAlgebra M α)
          (pastPartitionSigmaAlgebra M β)) A) =
      conditionalEntropy M β (sigmaJoin (pastPartitionSigmaAlgebra M β) A) +
      conditionalEntropy M α
        (sigmaJoin (sigmaJoin (pastPartitionSigmaAlgebra M α)
          (orbitPartitionSigmaAlgebra M inv β)) A) := by
  sorry

/-- Source: Theorem 7.10.12. -/
theorem pinskerAlgebra_isJoinOfFutureTails
    (M : MeasurableSystem.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T) :
    EqualModuloMeasure M (pinskerSigmaAlgebra M) (universalTailJoin M) := by
  sorry

/-- Source: Theorem 7.10.13. -/
theorem conditioningOnPinskerDoesNotChangePastConditionalEntropy
    (M : MeasurableSystem.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T)
    (ξ : FiniteMeasurablePartition M) (A : Set (Set M.X))
    (hA : isSubSigmaAlgebra M A)
    (hAinv : EqualModuloMeasure M (preimageFamily M.T A) A) :
    conditionalEntropy M ξ (sigmaJoin (pastPartitionSigmaAlgebra M ξ) A) =
      conditionalEntropy M ξ
        (sigmaJoin (sigmaJoin (pastPartitionSigmaAlgebra M ξ)
          (pinskerSigmaAlgebra M)) A) ∧
    partitionEntropyRate M ξ =
      conditionalEntropy M ξ
        (sigmaJoin (pastPartitionSigmaAlgebra M ξ) (pinskerSigmaAlgebra M)) := by
  sorry

/-- Source: Theorem 7.10.14. -/
theorem entropyOfLargePowersConvergesToPinskerConditionalEntropy
    (M : MeasurableSystem.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T)
    (ξ : FiniteMeasurablePartition M) :
    Tendsto (fun k : ℕ => partitionEntropyRate (measurablePowerSystem M (k + 1))
        (finitePartitionForMap M (M.T^[k + 1]) ξ))
      atTop (nhds (conditionalEntropy M ξ (pinskerSigmaAlgebra M))) := by
  sorry

end Section10
end Chapter07
