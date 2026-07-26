import Chapter08.Section04

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators

namespace Chapter08

universe u

namespace Section05

/-- Source: Definition 8.5.1. -/
def mobiusAndLiouvilleFunctions : Prop :=
  IsMobiusFunction mobiusFunction ∧ IsLiouvilleFunction liouvilleFunction

/-- Source: Question 8.5.2 (Chowla conjecture). -/
def chowlaConjectureQuestion : Prop := ChowlaConjecture

/-- Source: Definition 8.5.3. -/
def sequenceAssociatedToTopologicalSystem
    (S : TopologicalSystem.{u}) (ξ : ℕ → ℂ) : Prop :=
  IsSequenceRealizedBy S ξ

/-- Source: Question 8.5.4 (Sarnak conjecture). -/
def sarnakConjectureQuestion : Prop := SarnakConjecture

def IsPeriodicSequence (ξ : ℕ → ℂ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∀ n, ξ (n + q) = ξ n

def IsQuasiperiodicSequence (ξ : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : ℕ, ∃ c z : Fin r → ℂ,
    (∀ i, ‖z i‖ = 1) ∧ ∀ n, ‖ξ n - ∑ i, c i * z i ^ n‖ < ε

/-- Source: Remark 8.5.5: constant, periodic and quasiperiodic test sequences. -/
theorem basicExamplesTowardSarnakConjecture :
    PrimeNumberTheoremOrthogonality ∧
    (∀ ξ : ℕ → ℂ, IsPeriodicSequence ξ →
      asymptoticallyOrthogonal (fun n => (mobiusFunction n : ℂ)) ξ) ∧
    ∀ ξ : ℕ → ℂ, IsQuasiperiodicSequence ξ →
      asymptoticallyOrthogonal (fun n => (mobiusFunction n : ℂ)) ξ := by
  sorry

/-- Source: Theorem 8.5.6. -/
theorem sarnakMobiusOrbitClosureProperties (Xμ : TopologicalSystem.{u}) :
    MobiusOrbitSystemEntropyStatement Xμ := by
  sorry

/-- Source: Lemma 8.5.7 (Davenport estimate). -/
theorem davenportEstimateForMobiusExponentialSums : DavenportEstimate := by
  sorry

/-- Source: Theorem 8.5.8. -/
theorem measureTheoreticSarnakTheorem
    (M : MeasurableSystem.{u}) (f : M.X → ℂ) :
    SarnakMeasureTheoremStatement M f := by
  sorry

/-- Source: Theorem 8.5.9. -/
theorem chowlaConjectureImpliesSarnakConjecture :
    ChowlaConjecture → SarnakConjecture := by
  sorry

/-- Source: Definition 8.5.10. -/
def chowlaConditionForSymbolicSequence (z : SymbolicSequence) : Prop :=
  ChowlaConditionTwoSided z

/-- Source: Definition 8.5.11. -/
def sarnakConditionForSymbolicSequence (z : SymbolicSequence) : Prop :=
  IsSignedSymbolicSequence z ∧ SarnakCondition (fun n => z n)

/-- Source: Lemma 8.5.12: odd moments vanish and all-even moments descend to `ν`. -/
theorem relativeIndependentLift_coordinateMomentFormulas
    (ν : Measure SupportSequence) (hν : IsShiftInvariantProbabilityMeasure ν) :
    ∀ r : ℕ, ∀ a : Fin r → ℕ, (∀ i, 1 ≤ a i) → StrictMono a →
      (∀ k : Fin (r + 1) → ℕ,
        (∀ i, k i = 1 ∨ k i = 2) → (∃ i, k i = 1) →
          symbolicMoment (RelativelyIndependentLift ν) r a k = 0) ∧
      symbolicMoment (RelativelyIndependentLift ν) r a (fun _ => 2) =
        supportMoment ν r a := by
  sorry

/-- Source: Lemma 8.5.13. -/
theorem quasiGenericLiftCharacterizationByChowlaCorrelations
    (z : SymbolicSequence) : ChowlaQuasiGenericEquivalence z := by
  sorry

/-- Source: Remark 8.5.14. -/
theorem chowlaConditionEquivalentToAllQuasiGenericLifts
    (z : SymbolicSequence) : ChowlaQuasiGenericRemark z := by
  sorry

/-- Source: Lemma 8.5.15. -/
theorem relativelyIndependentLiftIsFactorOfProduct
    (ν : Measure SupportSequence) : RelativeIndependentLiftFactorStatement ν := by
  sorry

/-- Source: Lemma 8.5.16. -/
theorem squareProjectionExtensionIsTrivialOrRelativeK
    (ν : Measure SupportSequence) : RelativeKOrTrivialExtensionStatement ν := by
  sorry

/-- Source: Lemma 8.5.17. -/
theorem conditionalExpectationOfCoordinateFunctionVanishes
    (ν : Measure SupportSequence) : ConditionalExpectationCoordinateZeroStatement ν := by
  sorry

/-- Source: Lemma 8.5.18. -/
theorem zeroEntropyJoiningIsRelativelyIndependentOverSquareFactor :
    ZeroEntropyJoiningRelativeIndependenceStatement := by
  sorry

/-- Source: Theorem 8.5.19. -/
theorem chowlaConditionImpliesSarnakCondition (z : SymbolicSequence) :
    ChowlaConditionTwoSided z → SarnakCondition (fun n => z n) := by
  sorry

end Section05
end Chapter08
