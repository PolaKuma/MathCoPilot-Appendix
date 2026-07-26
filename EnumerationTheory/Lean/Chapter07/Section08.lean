import Chapter07.Section07

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u


namespace Section08

def maximalEntropyMeasures (S : System.{u}) : Set (MeasureOn S.X) :=
  { μ | measureOfMaximalEntropy S μ }

/-- Source: Definition 7.8.1. -/
def isMeasureOfMaximalEntropy (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  μ ∈ maximalEntropyMeasures S

/-- Source: Remark 7.8.2. -/
theorem zeroEntropy_allInvariantMeasuresAreMaximal
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S)
    (hzero : topologicalEntropy S = 0) :
    maximalEntropyMeasures S = Chapter06.invariantMeasures S := by
  sorry

/-- Source: Proposition 7.8.3, all five assertions. -/
theorem maximalEntropyMeasures_properties
    (S : System.{u}) (hS : Chapter05.IsTopologicalSystem S) :
    (∀ μ ∈ maximalEntropyMeasures S, ∀ ν ∈ maximalEntropyMeasures S,
      ∀ p : ℝ, 0 ≤ p -> p ≤ 1 ->
        p • μ + (1 - p) • ν ∈ maximalEntropyMeasures S) ∧
    (topologicalEntropy S < ⊤ ->
      Chapter06.extremePoints (maximalEntropyMeasures S) =
        maximalEntropyMeasures S ∩ Chapter06.ergodicMeasures S) ∧
    (topologicalEntropy S < ⊤ -> (maximalEntropyMeasures S).Nonempty ->
      ∃ μ, μ ∈ maximalEntropyMeasures S ∧
        Chapter06.IsErgodicMeasure S μ) ∧
    (topologicalEntropy S = ⊤ -> (maximalEntropyMeasures S).Nonempty) ∧
    (EntropyMapUpperSemicontinuous S ->
      (maximalEntropyMeasures S).Nonempty ∧ IsCompact (maximalEntropyMeasures S)) := by
  sorry

/-- Source: Remark 7.8.4. -/
theorem infiniteEntropy_canHaveNoErgodicMaximalMeasure :
    ∃ S : System.{0}, Chapter05.IsMinimalSystem S ∧
      topologicalEntropy S = ⊤ ∧
      ∀ μ : MeasureOn S.X, Chapter06.IsErgodicMeasure S μ ->
        entropyMap S μ < ⊤ := by
  sorry

/-- Source: Example 7.8.5 (Gurevič). -/
theorem aCompactSystemCanHaveNoMaximalEntropyMeasure :
    ∃ S : System.{0}, Nonempty S.X ∧ Chapter05.IsTopologicalSystem S ∧
      ¬ (maximalEntropyMeasures S).Nonempty := by
  sorry

/-- Source: Remark 7.8.6(1), in its topological content. -/
theorem minimalSystemsCanLackMaximalEntropyMeasures :
    ∃ S : System.{0}, Chapter05.IsMinimalSystem S ∧
      ¬ (maximalEntropyMeasures S).Nonempty := by
  sorry

/-- Source: Definition 7.8.7. -/
def intrinsicallyErgodic (S : System.{u}) : Prop :=
  ∃! μ : MeasureOn S.X, μ ∈ maximalEntropyMeasures S

/-- Source: Remark 7.8.8(1). -/
theorem uniquelyErgodic_impliesIntrinsicallyErgodic
    (S : System.{u}) :
    Chapter06.IsUniquelyErgodic S -> intrinsicallyErgodic S := by
  sorry

/-- Source: Remark 7.8.8(2). -/
theorem uniqueMaximalMeasureAtInfiniteEntropy_forcesUniqueErgodicity
    (S : System.{u}) :
    topologicalEntropy S = ⊤ -> intrinsicallyErgodic S ->
      Chapter06.IsUniquelyErgodic S := by
  sorry

/-- Source: Remark 7.8.8(3). -/
theorem uniqueMaximalEntropyMeasure_isErgodic
    (S : System.{u}) :
    intrinsicallyErgodic S ->
      ∃ μ : MeasureOn S.X, Chapter06.IsErgodicMeasure S μ ∧
        μ ∈ maximalEntropyMeasures S := by
  sorry

/-- Source: Example 7.8.9. -/
theorem fullShift_uniqueMaximalEntropyMeasure
    (k : ℕ) (hk : 2 ≤ k) :
    ∃! μ : MeasureOn (FullShiftSpace k),
      IsUniformBernoulliMeasure k μ ∧
        μ ∈ maximalEntropyMeasures (fullShiftSystem k) := by
  sorry

def markovCylinder {k n : ℕ} (A : Fin k -> Fin k -> ℕ)
    (start : ℤ) (word : Fin (n + 1) -> Fin k) : Set (markovShiftSpace A) :=
  {x | ∀ i : Fin (n + 1), x.1 (start + (i : ℕ)) = word i}

def IsParryMeasure {k : ℕ} (A : Fin k -> Fin k -> ℕ)
    (μ : MeasureOn (markovShiftSpace A)) : Prop :=
  ∃ ρ : ℝ, ∃ left right stationary : Fin k -> ℝ,
    IsPerronRoot A ρ ∧
    (∀ i, 0 < left i ∧ 0 < right i ∧
      stationary i = left i * right i) ∧
    (∑ i, stationary i) = 1 ∧
    (∀ j, ∑ i, left i * (A i j : ℝ) = ρ * left j) ∧
    (∀ i, ∑ j, (A i j : ℝ) * right j = ρ * right i) ∧
    Chapter06.IsInvariantMeasure (markovShiftSystem A) μ ∧
    ∀ n : ℕ, ∀ start : ℤ, ∀ word : Fin (n + 1) -> Fin k,
      μ.measure (markovCylinder A start word) = ENNReal.ofReal
        (stationary (word 0) *
          ∏ i : Fin n,
            ((A (word i.castSucc) (word i.succ) : ℝ) * right (word i.succ)) /
              (ρ * right (word i.castSucc)))

/-- Source: Example 7.8.10. -/
theorem irreducibleMarkovShift_uniqueParryMaximalMeasure
    {k : ℕ} (A : Fin k -> Fin k -> ℕ)
    (hk : 0 < k) (h01 : IsZeroOneMatrix A) (hirr : IsIrreducibleMatrix A) :
    ∃! μ : MeasureOn (markovShiftSpace A),
      IsParryMeasure A μ ∧
        μ ∈ maximalEntropyMeasures (markovShiftSystem A) := by
  sorry

end Section08
end Chapter07
