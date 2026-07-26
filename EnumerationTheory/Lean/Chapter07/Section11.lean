import Chapter07.Section10

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u v w

namespace Section11

def imageFamily {X : Type u} (T : X -> X) (A : Set (Set X)) : Set (Set X) :=
  {B | ∃ C ∈ A, B = T '' C}

def iteratedImageFamily {X : Type u} (T : X -> X)
    (A : Set (Set X)) (n : ℕ) : Set (Set X) := imageFamily (T^[n]) A

def forwardJoinFamily (M : MeasurableSystem.{u}) (A : Set (Set M.X)) : Set (Set M.X) :=
  Chapter00.generatedSigmaAlgebra {B | ∃ n : ℕ, B ∈ iteratedImageFamily M.T A n}

def backwardTailFamily (M : MeasurableSystem.{u}) (A : Set (Set M.X)) : Set (Set M.X) :=
  ⋂ n : ℕ, Section10.preimageFamily (M.T^[n]) A

/-- The definition recalled at the start of §7.11. -/
def IsKolmogorovSystem (M : MeasurableSystem.{u}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T ∧
    ∃ K : Set (Set M.X), isSubSigmaAlgebra M K ∧ K ⊆ imageFamily M.T K ∧
      EqualModuloMeasure M (forwardJoinFamily M K) (measurableSets M) ∧
      EqualModuloMeasure M (backwardTailFamily M K) {∅, Set.univ}

def IsTrivialMeasureSystem (M : MeasurableSystem.{u}) : Prop :=
  ∀ A ∈ measurableSets M, M.μ A = 0 ∨ M.μ A = 1

/-- Source: Lemma 7.11.1. -/
theorem kolmogorovSystems_areErgodicAndNonatomic
    (M : MeasurableSystem.{u}) :
    IsKolmogorovSystem M -> Chapter02.IsErgodic M ∧
      (¬ IsTrivialMeasureSystem M -> ∀ x : M.X, M.μ {x} = 0) := by
  sorry

/-- Source: Lemma 7.11.2. -/
theorem closeEqualCardinalityPartitions_haveCloseEntropyRates
    (M : MeasurableSystem.{u}) (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ α β : FiniteMeasurablePartition M,
      ∀ A : Fin k -> Set M.X, ∀ B : Fin k -> Set M.X,
      (∀ i, A i ∈ α.atoms) -> (∀ C ∈ α.atoms, ∃ i, A i = C) ->
      (∀ i, B i ∈ β.atoms) -> (∀ C ∈ β.atoms, ∃ i, B i = C) ->
      (∑ i, (M.μ (Chapter00.symmDiff (A i) (B i))).toReal) < δ ->
        conditionalEntropy M α (partitionSigmaAlgebra M β) +
          conditionalEntropy M β (partitionSigmaAlgebra M α) < ε ∧
        |partitionEntropyRate M α - partitionEntropyRate M β| < ε := by
  sorry

/-- Source: Theorem 7.11.3. -/
theorem rohlinSinaiTailContainsPinsker
    (M : MeasurableSystem.{u}) (A : Set (Set M.X))
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T)
    (hA : isSubSigmaAlgebra M A)
    (hdecreasing : Section10.preimageFamily M.T A ⊆ A)
    (hgenerates : EqualModuloMeasure M (forwardJoinFamily M A) (measurableSets M)) :
    pinskerSigmaAlgebra M ⊆ backwardTailFamily M A := by
  sorry

/-- Source: Theorem 7.11.4 (Rohlin--Sinai). -/
theorem rohlinSinaiTheorem
    (M : MeasurableSystem.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hinv : Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T) :
    (∃ K : Set (Set M.X), isSubSigmaAlgebra M K ∧ K ⊆ imageFamily M.T K ∧
      EqualModuloMeasure M (forwardJoinFamily M K) (measurableSets M) ∧
      EqualModuloMeasure M (backwardTailFamily M K) (pinskerSigmaAlgebra M)) ∧
    (IsKolmogorovSystem M ↔ hasCompletelyPositiveEntropy M) := by
  sorry

def ProductMeasureSystemData (M : MeasurableSystem.{u})
    (N : MeasurableSystem.{v}) (P : MeasurableSystem.{max u v}) : Prop :=
  Chapter01.IsMeasurePreservingSystem M ∧
    Chapter01.IsMeasurePreservingSystem N ∧
    Chapter01.IsMeasurePreservingSystem P ∧
    ∃ e : P.X ≃ M.X × N.X,
      Measurable e ∧ Measurable e.symm ∧
      (∀ x, e (P.T x) = (M.T (e x).1, N.T (e x).2)) ∧
      MeasureTheory.Measure.map e P.μ = M.μ.prod N.μ

def productPinskerFamily (M : MeasurableSystem.{u})
    (N : MeasurableSystem.{v}) : Set (Set (M.X × N.X)) :=
  Chapter00.generatedSigmaAlgebra
    {C | ∃ A ∈ pinskerSigmaAlgebra M, ∃ B ∈ pinskerSigmaAlgebra N, C = A ×ˢ B}

def pullbackProductPinskerFamily (M : MeasurableSystem.{u})
    (N : MeasurableSystem.{v}) (P : MeasurableSystem.{max u v})
    (e : P.X ≃ M.X × N.X) : Set (Set P.X) :=
  Chapter00.generatedSigmaAlgebra
    {C | ∃ D ∈ productPinskerFamily M N, C = e ⁻¹' D}

/-- Source: Theorem 7.11.5. -/
theorem productPinskerFormula
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (P : MeasurableSystem.{max u v})
    (hP : ProductMeasureSystemData M N P) :
    (∃ e : P.X ≃ M.X × N.X,
      EqualModuloMeasure P (pinskerSigmaAlgebra P)
        (pullbackProductPinskerFamily M N P e)) ∧
      (IsKolmogorovSystem M -> IsKolmogorovSystem N -> IsKolmogorovSystem P) := by
  sorry

/-- Source: Lemma 7.11.6 (Pinsker inequality). -/
theorem pinskerInequality
    {l : ℕ} (p q : Fin l -> ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hsump : ∑ i, p i = 1) (hsumq : ∑ i, q i ≤ 1) :
    ((∑ i, |p i - q i|) ^ 2 / 2) * Real.log 2 ≤
      ∑ i, p i * Real.log (p i / q i) := by
  sorry

/-- Source: Lemma 7.11.7. -/
theorem entropyDrop_controlsTotalCorrelation
    (M : MeasurableSystem.{u}) (α β : FiniteMeasurablePartition M) (ε : ℝ)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hε : 0 < ε)
    (hdrop : partitionEntropy M α -
      conditionalEntropy M α (partitionSigmaAlgebra M β) <
        ε ^ 2 / 2 * Real.log 2) :
    ∑ B ∈ β.atoms, ∑ A ∈ α.atoms,
      |(M.μ (A ∩ B)).toReal - (M.μ A).toReal * (M.μ B).toReal| < ε := by
  sorry

def IsMixingOfAllOrders (M : MeasurableSystem.{u}) : Prop :=
  ∀ k : ℕ, ∀ A : Fin (k + 1) -> Set M.X,
    (∀ i, A i ∈ measurableSets M) -> ∀ ε : ℝ, 0 < ε -> ∃ N : ℕ,
      ∀ gaps : Fin k -> ℕ, (∀ i, N ≤ gaps i) ->
        |(M.μ (⋂ i : Fin (k + 1),
            (M.T^[(Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum gaps]) ⁻¹' A i)).toReal -
          ∏ i, (M.μ (A i)).toReal| < ε

/-- Source: Theorem 7.11.8. -/
theorem kolmogorovSystems_areMixingOfAllOrders
    (M : MeasurableSystem.{u}) :
    IsKolmogorovSystem M -> IsMixingOfAllOrders M := by
  sorry

/-- Source: Theorem 7.11.9 (Ornstein). -/
theorem ornsteinBernoulliConjugacyTheorem
    (M N : MeasurableSystem.{u}) :
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
    Chapter04.IsLebesgueProbabilitySpace N.toProbabilitySpace ->
    isBernoulliMeasureSystem M -> isBernoulliMeasureSystem N ->
    measureEntropy M = measureEntropy N -> Chapter01.IsIsomorphicSystems M N := by
  sorry

/-- Source: Theorem 7.11.10 (Sinai factor theorem). -/
theorem sinaiFactorTheorem
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
    Chapter04.IsLebesgueProbabilitySpace N.toProbabilitySpace ->
    Chapter02.IsErgodic M ->
    Chapter01.IsInvertibleMeasurePreservingMap (measurableSets M) M.μ
      (measurableSets M) M.μ M.T ->
    isBernoulliMeasureSystem N -> measureEntropy N ≤ measureEntropy M ->
      ∃ π : M.X -> N.X, Chapter01.IsFactorMap M N π := by
  sorry

end Section11
end Chapter07
