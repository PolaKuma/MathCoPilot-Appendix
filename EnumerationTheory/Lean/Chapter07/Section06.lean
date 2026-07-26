import Chapter07.Section05

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u

namespace Section06

/-- Source: Definition 7.6.1.  The domain is restricted to invariant Borel
probability measures by the accompanying predicate. -/
def invariantMeasureEntropyMap (S : System.{u}) : MeasureOn S.X -> EReal :=
  entropyMap S

/-- Source: Theorem 7.6.2. -/
theorem entropyMap_isAffine
    (S : System.{u}) :
    ∀ μ ν : MeasureOn S.X,
      Chapter06.IsInvariantMeasure S μ -> Chapter06.IsInvariantMeasure S ν ->
      ∀ p : ℝ, 0 ≤ p -> p ≤ 1 ->
        entropyMap S (p • μ + (1 - p) • ν) =
          (p : EReal) * entropyMap S μ +
            ((1 - p : ℝ) : EReal) * entropyMap S ν := by
  sorry

/-- Source: Example 7.6.3.  The measures are the uniform atomic measures on
the `2^(n+1)` points fixed by `σ^(n+1)`; their weak-star limit is the fair
Bernoulli measure. -/
theorem fullTwoShift_periodicMeasuresConvergeToFairBernoulli :
    ∃ μseq : ℕ -> MeasureOn (FullShiftSpace 2),
      ∃ μ : MeasureOn (FullShiftSpace 2),
        (∀ n : ℕ, ∃ F : Finset (FullShiftSpace 2),
          (F : Set (FullShiftSpace 2)) = fixedPointSet (fullShiftSystem 2) (n + 1) ∧
          F.card = 2 ^ (n + 1) ∧
          IsUniformMeasureOnFiniteSet (μseq n) F ∧
          Chapter06.IsInvariantMeasure (fullShiftSystem 2) (μseq n) ∧
          entropyMap (fullShiftSystem 2) (μseq n) = 0) ∧
        IsUniformBernoulliMeasure 2 μ ∧
        entropyMap (fullShiftSystem 2) μ = (Real.log 2 : EReal) ∧
        Chapter06.weakStarConverges μseq μ := by
  sorry

def ReciprocalAlphabet :=
  {x : ℝ // x = 0 ∨ ∃ n : ℕ, x = 1 / ((n + 1 : ℕ) : ℝ)}

instance reciprocalAlphabetTopology : TopologicalSpace ReciprocalAlphabet :=
  TopologicalSpace.induced Subtype.val inferInstance

abbrev ReciprocalShiftSpace := ℤ -> ReciprocalAlphabet

instance reciprocalShiftTopology : TopologicalSpace ReciprocalShiftSpace :=
  inferInstance

def reciprocalShift (x : ReciprocalShiftSpace) : ReciprocalShiftSpace :=
  fun i => x (i + 1)

def reciprocalShiftSystem : System.{0} where
  X := ReciprocalShiftSpace
  topology := inferInstance
  T := reciprocalShift

def reciprocalSymbol (n : ℕ) : ReciprocalAlphabet :=
  ⟨1 / ((n + 1 : ℕ) : ℝ), Or.inr ⟨n, rfl⟩⟩

def reciprocalZeroPoint : ReciprocalShiftSpace :=
  fun _ => ⟨0, Or.inl rfl⟩

def reciprocalCylinder {n : ℕ} (start : ℤ)
    (word : Fin n -> ReciprocalAlphabet) : Set ReciprocalShiftSpace :=
  {x | ∀ i : Fin n, x (start + (i : ℕ)) = word i}

def IsTwoSymbolBernoulliMeasure (a b : ReciprocalAlphabet)
    (μ : MeasureOn ReciprocalShiftSpace) : Prop :=
  a ≠ b ∧ Chapter06.IsInvariantMeasure reciprocalShiftSystem μ ∧
    ∀ n : ℕ, ∀ start : ℤ, ∀ word : Fin n -> ReciprocalAlphabet,
      μ.measure (reciprocalCylinder start word) =
        ∏ i : Fin n, if word i = a ∨ word i = b then (2 : ENNReal)⁻¹ else 0

/-- Source: Example 7.6.4.  Bernoulli measures on the shrinking alphabets
`{1/(n+1),1/(n+2)}` converge to the all-zero Dirac mass, so the entropy map is
not upper semicontinuous. -/
theorem reciprocalAlphabetShift_entropyMapNotUpperSemicontinuous :
    ∃ μseq : ℕ -> MeasureOn ReciprocalShiftSpace,
      (∀ n, IsTwoSymbolBernoulliMeasure (reciprocalSymbol n)
        (reciprocalSymbol (n + 1)) (μseq n)) ∧
      (∀ n, entropyMap reciprocalShiftSystem (μseq n) = (Real.log 2 : EReal)) ∧
      Chapter06.weakStarConverges μseq (Chapter06.diracMeasure reciprocalZeroPoint) ∧
      Chapter06.IsInvariantMeasure reciprocalShiftSystem
        (Chapter06.diracMeasure reciprocalZeroPoint) ∧
      entropyMap reciprocalShiftSystem (Chapter06.diracMeasure reciprocalZeroPoint) = 0 ∧
      ¬ EntropyMapUpperSemicontinuous reciprocalShiftSystem := by
  sorry

/-- Source: Theorem 7.6.5. -/
theorem expansiveHomeomorphism_entropyMapUpperSemicontinuous
    (S : System.{u}) [PseudoMetricSpace S.X] [CompactSpace S.X]
    (inv : S.X -> S.X) (c : ℝ)
    (hcompat : MetricCompatibleWithTopology S)
    (hexp : IsExpansiveMapWithConstant S.T inv c) :
    EntropyMapUpperSemicontinuous S := by
  sorry

/-- Source: Theorem 7.6.6. -/
theorem finePartitions_computeMeasureEntropy
    (S : System.{u}) [PseudoMetricSpace S.X] [CompactSpace S.X]
    (hcompat : MetricCompatibleWithTopology S) (hT : Continuous S.T)
    (ξ : ℕ -> FiniteBorelPartition S)
    (hdiam : Tendsto (fun n => sSup {r : ℝ | ∃ A ∈ (ξ n).atoms,
      r = Metric.diam A}) atTop (nhds 0))
    (μ : MeasureOn S.X) (hμ : Chapter06.IsInvariantMeasure S μ) :
    Tendsto (fun n => (borelPartitionEntropyRate S μ (ξ n) : EReal))
      atTop (nhds (entropyMap S μ)) := by
  sorry

/-- Source: Theorem 7.6.7. -/
theorem entropy_affineAlongErgodicDecomposition
    (S : System.{u}) (μ : MeasureOn S.X)
    (D : EntropyErgodicDecompositionData S μ)
    (ξ : FiniteBorelPartition S)
    (hμ : Chapter06.IsInvariantMeasure S μ) :
    borelPartitionEntropyRate S μ ξ =
        D.averageReal (fun ν => borelPartitionEntropyRate S ν ξ) ∧
      entropyMap S μ = D.averageEReal (fun ν => entropyMap S ν) := by
  sorry

end Section06
end Chapter07
