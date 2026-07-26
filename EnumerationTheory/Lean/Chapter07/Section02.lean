import Chapter07.Section01

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v w

namespace Section02

def IsCircleTimesMap (M : MeasurableSystem.{u}) (n : ℕ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∃ e : M.X ≃ AddCircle (1 : ℝ),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e M.μ = MeasureTheory.Measure.addHaar ∧
      ∀ x : M.X, e (M.T x) = n • e x

def IsBernoulliShiftWith {k : ℕ} (M : MeasurableSystem.{u})
    (p : Fin k -> ℝ) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∃ e : M.X ≃ (ℤ -> Fin k),
      Measurable e ∧ Measurable e.symm ∧
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∀ x : M.X, ∀ n : ℤ, e (M.T x) n = e x (n + 1)) ∧
      ∀ n : ℕ, ∀ a : Fin (n + 1) -> Fin k,
        M.μ {x | ∀ i : Fin (n + 1), e x (i : ℤ) = a i} =
          ENNReal.ofReal (∏ i, p (a i))

/-- The bilateral shift with the product of normalized Lebesgue measure on
`[0,1]`; the finite-cylinder equation records the product measure, which a bare
conjugacy to the shift space does not determine. -/
def IsContinuousProductShift (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    ∃ e : M.X ≃ (ℤ -> Set.Icc (0 : ℝ) 1),
      Measurable e ∧ Measurable e.symm ∧
      (∀ x : M.X, ∀ n : ℤ, e (M.T x) n = e x (n + 1)) ∧
      ∀ I : Finset ℤ, ∀ A : ℤ -> Set (Set.Icc (0 : ℝ) 1),
        (∀ i ∈ I, MeasurableSet (A i)) ->
        M.μ {x | ∀ i ∈ I, e x i ∈ A i} =
          ∏ i ∈ I, (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Set.Icc (0 : ℝ) 1)) (Subtype.val '' A i)

def IsConditionalExpectationVersion (M : MeasurableSystem.{u})
    (f : M.X -> ℝ) (F : Set (Set M.X)) (g : M.X -> ℝ) : Prop :=
  Chapter00.IsMeasurableForFamily F (fun x => (g x : ℂ)) ∧
    MeasureTheory.Integrable f M.μ ∧ MeasureTheory.Integrable g M.μ ∧
    ∀ A ∈ F, MeasurableSet A ->
      ∫ x in A, g x ∂M.μ = ∫ x in A, f x ∂M.μ

def ConvergesInL1AndAlmostEverywhere (M : MeasurableSystem.{u})
    (gseq : ℕ -> M.X -> ℝ) (g : M.X -> ℝ) : Prop :=
  Tendsto (fun n => M.lpNorm 1 (fun x => ((gseq n x - g x : ℝ) : ℂ)))
      atTop (nhds 0) ∧
    ∀ᵐ x ∂M.μ, Tendsto (fun n => gseq n x) atTop (nhds (g x))

def increasingSigmaLimit (M : MeasurableSystem.{u})
    (F : ℕ -> Set (Set M.X)) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra {A | ∃ n, A ∈ F n}

def decreasingSigmaLimit (M : MeasurableSystem.{u})
    (F : ℕ -> Set (Set M.X)) : Set (Set M.X) :=
  ⋂ n, F n

/-- Source: Lemma 7.2.1, Chapter 7, Section 2. -/
theorem conditionalExpectation_maximalLemma
    (M : MeasurableSystem.{u}) (f : M.X -> ℝ)
    (F : ℕ -> Set (Set M.X)) (N : ℕ) (g : ℕ -> M.X -> ℝ) :
    IsProbabilityMeasurableSystem M ->
    (∀ n, isSubSigmaAlgebra M (F n)) ->
    (∀ n, F n ⊆ F (n + 1)) ->
    (∀ n, n ≤ N -> IsConditionalExpectationVersion M f (F n) (g n)) ->
    ∀ c : ℝ, 0 < c ->
      M.μ {x | ∃ n ≤ N, c < g n x} ≤
        ENNReal.ofReal ((∫ x, |f x| ∂M.μ) / c) := by
  sorry

/-- Source: Theorem 7.2.2, Chapter 7, Section 2. -/
theorem increasingMartingaleConvergence
    (M : MeasurableSystem.{u}) (f : M.X -> ℝ) (F : ℕ -> Set (Set M.X))
    (gseq : ℕ -> M.X -> ℝ) (g : M.X -> ℝ) :
    IsProbabilityMeasurableSystem M ->
    (∀ n, isSubSigmaAlgebra M (F n)) -> (∀ n, F n ⊆ F (n + 1)) ->
    (∀ n, IsConditionalExpectationVersion M f (F n) (gseq n)) ->
    IsConditionalExpectationVersion M f (increasingSigmaLimit M F) g ->
      ConvergesInL1AndAlmostEverywhere M gseq g := by
  sorry

/-- Source: Theorem 7.2.3, Chapter 7, Section 2. -/
theorem decreasingMartingaleConvergence
    (M : MeasurableSystem.{u}) (f : M.X -> ℝ) (F : ℕ -> Set (Set M.X))
    (gseq : ℕ -> M.X -> ℝ) (g : M.X -> ℝ) :
    IsProbabilityMeasurableSystem M ->
    (∀ n, isSubSigmaAlgebra M (F n)) -> (∀ n, F (n + 1) ⊆ F n) ->
    (∀ n, IsConditionalExpectationVersion M f (F n) (gseq n)) ->
    IsConditionalExpectationVersion M f (decreasingSigmaLimit M F) g ->
      ConvergesInL1AndAlmostEverywhere M gseq g := by
  sorry

/-- Source: Theorem 7.2.4, Chapter 7, Section 2. -/
theorem chungInformationMaximalInequality
    (M : MeasurableSystem.{u}) (α : CountableMeasurablePartition M)
    (F : ℕ -> Set (Set M.X)) :
    IsProbabilityMeasurableSystem M ->
    (∀ n, isSubSigmaAlgebra M (F n)) ->
    countablePartitionEntropy M α ≠ ⊤ ->
    ((∀ n, F n ⊆ F (n + 1)) ∨ (∀ n, F (n + 1) ⊆ F n)) ->
      MeasureTheory.Integrable
        (fun x => sSup {r : ℝ | ∃ n, r = countableConditionalInformation M α (F n) x}) M.μ ∧
      (∫ x, sSup {r : ℝ | ∃ n,
          r = countableConditionalInformation M α (F n) x} ∂M.μ) ≤
        (countablePartitionEntropy M α).toReal + 1 := by
  sorry

/-- Source: Theorem 7.2.5, Chapter 7, Section 2. -/
theorem conditionalInformationAndEntropy_convergeAlongMonotoneSigmaAlgebras
    (M : MeasurableSystem.{u}) (α : CountableMeasurablePartition M)
    (F : ℕ -> Set (Set M.X)) :
    IsProbabilityMeasurableSystem M ->
    (∀ n, isSubSigmaAlgebra M (F n)) ->
    countablePartitionEntropy M α ≠ ⊤ ->
    (((∀ n, F n ⊆ F (n + 1)) ->
      ConvergesInL1AndAlmostEverywhere M
        (fun n => countableConditionalInformation M α (F n))
        (countableConditionalInformation M α (increasingSigmaLimit M F)) ∧
      Antitone (fun n => countableConditionalEntropy M α (F n)) ∧
      Tendsto (fun n => countableConditionalEntropy M α (F n)) atTop
        (nhds (countableConditionalEntropy M α (increasingSigmaLimit M F)))) ∧
    ((∀ n, F (n + 1) ⊆ F n) ->
      ConvergesInL1AndAlmostEverywhere M
        (fun n => countableConditionalInformation M α (F n))
        (countableConditionalInformation M α (decreasingSigmaLimit M F)) ∧
      Monotone (fun n => countableConditionalEntropy M α (F n)) ∧
      Tendsto (fun n => countableConditionalEntropy M α (F n)) atTop
        (nhds (countableConditionalEntropy M α (decreasingSigmaLimit M F))))) := by
  sorry

/-- Source: Proposition 7.2.6, Chapter 7, Section 2. -/
theorem countablePartitionInformation_chainRules
    (M : MeasurableSystem.{u}) (α : CountableMeasurablePartition M)
    (β : CountableMeasurablePartition M) (F : Set (Set M.X))
    (hprob : IsProbabilityMeasurableSystem M) (hF : isSubSigmaAlgebra M F) :
    (∀ᵐ x ∂M.μ, countableJoinConditionalInformation M α β F x =
      countableConditionalInformation M α F x +
        countableConditionalInformation M β
          (sigmaJoin (countablePartitionSigmaAlgebra M α) F) x) ∧
    countableJoinConditionalEntropy M α β F =
      countableConditionalEntropy M α F +
        countableConditionalEntropy M β
          (sigmaJoin (countablePartitionSigmaAlgebra M α) F) := by
  sorry

/-- Source: Proposition 7.2.7, Chapter 7, Section 2. -/
theorem partitionEntropyRate_equalsPastConditionalEntropy
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    partitionEntropyRate M α = conditionalEntropy M α (pastPartitionSigmaAlgebra M α) ∧
      partitionEntropyRate M α ≤ partitionEntropy M α := by
  sorry

/-- Source: Theorem 7.2.8, Chapter 7, Section 2. -/
theorem abramovIncreasingPartitionsEntropyLimit
    (M : MeasurableSystem.{u}) (α : ℕ -> FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (∀ n, partitionRefines M (α (n + 1)) (α n)) ->
      EqualModuloMeasure M
        (Chapter00.generatedSigmaAlgebra
          {A | ∃ n : ℕ, ∃ B ∈ (α n).atoms, A = B}) (measurableSets M) ->
        Tendsto (fun n => (partitionEntropyRate M (α n) : EReal))
          atTop (nhds (measureEntropy M)) := by
  sorry

/-- Source: Theorem 7.2.9, Chapter 7, Section 2. -/
theorem productMeasureEntropy_additivity
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (P : MeasurableSystem.{max u v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hP : Chapter01.IsMeasurePreservingSystem P)
    (hprod : ∃ e : P.X ≃ M.X × N.X,
      Measurable e ∧ Measurable e.symm ∧
      (∀ x, e (P.T x) = (M.T (e x).1, N.T (e x).2)) ∧
      MeasureTheory.Measure.map e P.μ = M.μ.prod N.μ) :
    measureEntropy P = measureEntropy M + measureEntropy N := by
  sorry

/-- Source: Theorem 7.2.10, Chapter 7, Section 2. -/
theorem kolmogorovSinaiFiniteGeneratorTheorem
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    EqualModuloMeasure M (futurePartitionSigmaAlgebra M α) (measurableSets M) ->
      measureEntropy M = partitionEntropyRate M α := by
  sorry

/-- Source: Remark 7.2.11, Chapter 7, Section 2. -/
theorem invertibleGenerator_canUseTwoSidedOrbit
    (M : MeasurableSystem.{u}) (α : FiniteMeasurablePartition M)
    (inv : M.X -> M.X) :
    Chapter01.IsMeasurePreservingSystem M ->
    Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T ->
    (∀ x, inv (M.T x) = x ∧ M.T (inv x) = x) ->
    EqualModuloMeasure M (orbitPartitionSigmaAlgebra M inv α) (measurableSets M) ->
      measureEntropy M = partitionEntropyRate M α := by
  sorry

/-- Source: Theorem 7.2.12, Chapter 7, Section 2. -/
theorem kriegerFiniteGeneratorTheorem
    (M : MeasurableSystem.{u}) :
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
    Chapter02.IsErgodic M -> measureEntropy M < ⊤ ->
    Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T ->
      ∃ n : ℕ, ∃ α : FiniteMeasurablePartition M,
        α.atoms.card = n ∧ Real.exp (measureEntropy M).toReal ≤ n ∧
        n ≤ Real.exp (measureEntropy M).toReal + 1 ∧
        ∃ inv : M.X -> M.X,
          (∀ x, inv (M.T x) = x ∧ M.T (inv x) = x) ∧
          EqualModuloMeasure M (orbitPartitionSigmaAlgebra M inv α) (measurableSets M) := by
  sorry

/-- Source: Example 7.2.13, Chapter 7, Section 2. -/
theorem identityTransformation_hasZeroMeasureEntropy
    (M : MeasurableSystem.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    M.T = id -> measureEntropy M = 0 := by
  sorry

/-- Source: Example 7.2.14, Chapter 7, Section 2. -/
theorem doublingMap_hasEntropyLogTwo :
    ∃ M : MeasurableSystem.{0}, IsCircleTimesMap M 2 ∧
      measureEntropy M = (Real.log 2 : EReal) := by
  sorry

/-- Source: Example 7.2.15, Chapter 7, Section 2. -/
theorem circleRotation_hasZeroMeasureEntropy
    (α : ℝ) :
    ∃ M : MeasurableSystem.{0}, Chapter01.IsRotationSystem M α ∧
      measureEntropy M = 0 := by
  sorry

/-- Source: Example 7.2.16, Chapter 7, Section 2. -/
theorem bernoulliShift_entropyFormula
    {k : ℕ} (hk : 2 ≤ k) (p : Fin k -> ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ M : MeasurableSystem.{0}, IsBernoulliShiftWith M p ∧
      measureEntropy M =
        (∑ i : Fin k, - p i * Real.log (p i) : ℝ) := by
  sorry

/-- Source: Example 7.2.17, Chapter 7, Section 2. -/
theorem continuousProductShift_hasInfiniteEntropy :
    ∃ M : MeasurableSystem.{0}, IsContinuousProductShift M ∧
      measureEntropy M = ⊤ := by
  sorry

/-- Source: Example 7.2.18, Chapter 7, Section 2. -/
theorem markovShift_entropyFormula
    {k : ℕ} (p : Fin k -> ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hk : 2 ≤ k) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hP : ∀ i j, 0 ≤ P i j) (hrows : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    ∃ M : MeasurableSystem.{0}, Chapter01.IsMarkovShiftWith M k p P ∧
      measureEntropy M =
        (∑ i : Fin k, ∑ j : Fin k,
          - p i * P i j * Real.log (P i j) : ℝ) := by
  sorry

end Section02
end Chapter07
