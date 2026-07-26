import Chapter07.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v w

namespace Section01

def entropyConvexFunction (t : ℝ) : ℝ :=
  if t = 0 then 0 else t * Real.log t

/-- Source: Definition 7.1.1, Chapter 7, Section 1. -/
def finitePartitionEntropy (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : ℝ :=
  partitionEntropy M α

/-- Source: Remark 7.1.1, Chapter 7, Section 1. -/
theorem entropyConvexFunction_convexOn_unitInterval :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) entropyConvexFunction := by
  sorry

/-- Source: Proposition 7.1.2, Chapter 7, Section 1. -/
theorem partitionEntropy_basicProperties
    (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M)
    (hprob : IsProbabilityMeasurableSystem M) :
    (α.atoms.card = 1 -> partitionEntropy M α = 0) ∧
      (0 < α.atoms.card ->
        partitionEntropy M α ≤ Real.log (α.atoms.card : ℝ)) ∧
      (partitionRefines M α β -> partitionEntropy M β ≤ partitionEntropy M α) ∧
      (Chapter01.IsMeasurePreservingSystem M ->
        partitionEntropy M (pullbackPartition M α) = partitionEntropy M α) := by
  sorry

/-- Source: Definition 7.1.2, Chapter 7, Section 1. -/
def informationOfPartition (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) : M.X -> ℝ :=
  informationFunction M α

/-- Source: Definition 7.1.3, Chapter 7, Section 1. -/
def conditionalInformationOfPartition (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) (𝓕 : Set (Set M.X)) : M.X -> ℝ :=
  conditionalInformation M α 𝓕

/-- Source: Remark 7.1.4, Chapter 7, Section 1. -/
theorem conditionalInformation_trivial_full_and_finiteFormulas
    (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M)
    (hprob : IsProbabilityMeasurableSystem M) :
    (∀ᵐ x ∂M.μ, conditionalInformation M α {Set.univ} x = informationFunction M α x) ∧
      (∀ᵐ x ∂M.μ,
        conditionalInformation M α (measurableSets M) x = 0) ∧
      (∀ᵐ x ∂M.μ, conditionalInformation M α (partitionSigmaAlgebra M β) x =
        ∑ A ∈ α.atoms, ∑ B ∈ β.atoms,
          if x ∈ A ∩ B then
            - Real.log ((M.μ (A ∩ B)).toReal / (M.μ B).toReal) else 0) := by
  sorry

/-- Source: Proposition 7.1.5, Chapter 7, Section 1. -/
theorem conditionalInformation_join_chainRule
    (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M)
    (F : Set (Set M.X))
    (hprob : IsProbabilityMeasurableSystem M) (hF : isSubSigmaAlgebra M F) :
    ∀ᵐ x ∂M.μ, conditionalInformation M (joinPartition M α β) F x =
      conditionalInformation M α F x +
        conditionalInformation M β (sigmaJoin (partitionSigmaAlgebra M α) F) x := by
  sorry

/-- Source: Corollary 7.1.6, Chapter 7, Section 1. -/
theorem conditionalInformation_iteratedDecomposition
    (M : MeasurableSystem.{u}) (α : ℕ -> FiniteMeasurablePartition M)
    (F : Set (Set M.X)) (n : ℕ)
    (hprob : IsProbabilityMeasurableSystem M) (hF : isSubSigmaAlgebra M F) :
    ∀ᵐ x ∂M.μ, conditionalInformation M (finitePartitionSequenceJoin M α n) F x =
      ∑ i : Fin n, conditionalInformation M (α i)
        (sigmaJoin
          (Chapter00.generatedSigmaAlgebra
            ((finitePartitionSequenceJoin M α i).atoms : Set (Set M.X))) F) x := by
  sorry

/-- Source: Definition 7.1.7, Chapter 7, Section 1. -/
def conditionalPartitionEntropy (M : MeasurableSystem.{u})
    (α : FiniteMeasurablePartition M) (𝓕 : Set (Set M.X)) : ℝ :=
  conditionalEntropy M α 𝓕

/-- Source: Proposition 7.1.7, Chapter 7, Section 1. -/
theorem conditionalEntropy_conditionalExpectationFormula
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (𝓕 : Set (Set M.X))
    (_hprob : IsProbabilityMeasurableSystem M) (_h𝓕 : isSubSigmaAlgebra M 𝓕) :
    conditionalEntropy M α 𝓕 =
      (M.integral fun x => (conditionalInformation M α 𝓕 x : ℂ)).re := by
  rfl

/-- Source: Proposition 7.1.8, Chapter 7, Section 1. -/
theorem conditionalEntropy_trivial_and_fullSigma
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (hprob : IsProbabilityMeasurableSystem M) :
    conditionalEntropy M α {Set.univ} = partitionEntropy M α ∧
      conditionalEntropy M α M.𝓧 = 0 := by
  sorry

/-- Source: Proposition 7.1.9, Chapter 7, Section 1. -/
theorem conditionalEntropy_basicProperties
    (M : MeasurableSystem.{u}) (α β γ : FiniteMeasurablePartition M)
    (𝓕 𝓖 : Set (Set M.X))
    (hprob : IsProbabilityMeasurableSystem M)
    (h𝓕 : isSubSigmaAlgebra M 𝓕) (h𝓖 : isSubSigmaAlgebra M 𝓖) :
    0 ≤ conditionalEntropy M α 𝓕 ∧
      conditionalEntropy M α 𝓕 ≤ Real.log (α.atoms.card : ℝ) ∧
      conditionalEntropy M (joinPartition M α β) 𝓕 =
        conditionalEntropy M α 𝓕 +
          conditionalEntropy M β (sigmaJoin (partitionSigmaAlgebra M α) 𝓕) ∧
      (partitionMeasurableWith M α 𝓕 -> conditionalEntropy M α 𝓕 = 0) ∧
      (partitionRefines M α β -> conditionalEntropy M β 𝓕 ≤ conditionalEntropy M α 𝓕) ∧
      (𝓕 ⊆ 𝓖 -> conditionalEntropy M α 𝓖 ≤ conditionalEntropy M α 𝓕) ∧
      conditionalEntropy M (joinPartition M α β) 𝓕 ≤
        conditionalEntropy M α 𝓕 + conditionalEntropy M β 𝓕 := by
  sorry

/-- Source: Lemma 7.1.10, Chapter 7, Section 1. -/
theorem jensenInequalityForConditionalEntropy
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (𝓕 : Set (Set M.X))
    (hprob : IsProbabilityMeasurableSystem M) (h𝓕 : isSubSigmaAlgebra M 𝓕) :
    conditionalEntropy M α 𝓕 ≤ partitionEntropy M α := by
  sorry

/-- Source: Definition 7.1.11, Chapter 7, Section 1. -/
def independentMeasurablePartitions (M : MeasurableSystem.{u})
    (α β : FiniteMeasurablePartition M) : Prop :=
  independentPartitions M α β

/-- Source: Proposition 7.1.12, Chapter 7, Section 1. -/
theorem independentPartitions_entropyCharacterizations
    (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M)
    (hprob : IsProbabilityMeasurableSystem M) :
    independentPartitions M α β ↔
      partitionEntropy M (joinPartition M α β) =
        partitionEntropy M α + partitionEntropy M β ∧
      conditionalEntropy M α {B | ∃ C ∈ β.atoms, B = C} =
        partitionEntropy M α := by
  sorry

/-- Source: Lemma 7.1.13, Chapter 7, Section 1. -/
theorem subadditiveSequence_limitEqualsInf
    (a : ℕ -> ℝ) :
    (∀ n, 0 ≤ a n) -> (∀ m n : ℕ, a (m + n) ≤ a m + a n) ->
      Tendsto (fun n : ℕ => a (n + 1) / (n + 1 : ℝ)) atTop
        (nhds (sInf {r : ℝ | ∃ n : ℕ, 0 < n ∧ r = a n / (n : ℝ)})) := by
  sorry

/-- Source: Proposition 7.1.14, Chapter 7, Section 1. -/
theorem iteratedPartitionEntropy_subadditiveAndLimit
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (∀ m n : ℕ,
      partitionEntropy M (iteratedJoinPartition M α (m + n)) ≤
        partitionEntropy M (iteratedJoinPartition M α m) +
          partitionEntropy M (iteratedJoinPartition M α n)) ∧
    Tendsto (fun n : ℕ =>
      partitionEntropy M (iteratedJoinPartition M α (n + 1)) / (n + 1 : ℝ))
      atTop (nhds (partitionEntropyRate M α)) := by
  sorry

/-- Source: Definition 7.1.15, Chapter 7, Section 1. -/
def entropyOfTransformationWithRespectToPartition
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M) : ℝ :=
  partitionEntropyRate M α

/-- Source: Definition 7.1.16, Chapter 7, Section 1. -/
def entropyOfMeasurePreservingTransformation (M : MeasurableSystem.{u}) : EReal :=
  measureEntropy M

/-- Source: Proposition 7.1.17, Chapter 7, Section 1. -/
theorem measureEntropy_factorMonotonicity_and_isomorphismInvariance
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    (Chapter01.IsFactorMap M N π -> measureEntropy N ≤ measureEntropy M) ∧
      (Chapter01.IsIsomorphicSystems M N -> measureEntropy M = measureEntropy N) := by
  sorry

/-- Source: Proposition 7.1.18, Chapter 7, Section 1. -/
theorem partitionEntropyRate_controlledByApproximation
    (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    partitionEntropyRate M α ≤ partitionEntropyRate M β +
      conditionalEntropy M α {B | ∃ C ∈ β.atoms, B = C} := by
  sorry

/-- Source: Corollary 7.1.19, Chapter 7, Section 1. -/
theorem entropyDistance_boundForPartitionEntropyRates
    (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    |partitionEntropyRate M α - partitionEntropyRate M β| ≤ partitionDistance M α β := by
  sorry

/-- Source: Proposition 7.1.20, Chapter 7, Section 1. -/
theorem entropyOfPositivePowers
    (M : MeasurableSystem.{u}) (m : ℕ)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    measureEntropy (measurableIterateSystem M m) = (m : EReal) * measureEntropy M := by
  sorry

/-- Source: Remark 7.1.21, Chapter 7, Section 1. -/
theorem entropyForInvertibleSystemsAndIntegerPowers
    (M : MeasurableSystem.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsInvertibleMeasurePreservingMap
      {A : Set M.X | @MeasurableSet M.X M.measurableSpace A} M.μ
      {A : Set M.X | @MeasurableSet M.X M.measurableSpace A} M.μ M.T ->
      ∃ inv : M.X -> M.X,
        (∀ α : FiniteMeasurablePartition M,
          partitionEntropyRate { M with T := inv } (finitePartitionForMap M inv α) =
            partitionEntropyRate M α) ∧
        ∀ m : ℤ, measureEntropy (measurableIntegerPowerSystem M inv m) =
          (m.natAbs : EReal) * measureEntropy M := by
  sorry

end Section01
end Chapter07
