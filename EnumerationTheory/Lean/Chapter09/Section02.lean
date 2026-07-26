import Chapter09.Section01

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section02

universe u

/-- Source: Theorem 9.2.1, Chapter 9, Section 2. -/
theorem szemerediTheorem
    (E : Set ℕ) :
    HasPositiveUpperBanachDensity E -> ContainsArbitrarilyLongArithmeticProgressions E := by
  sorry

/-- Source: Definition 9.2.2, Chapter 9, Section 2. -/
def poincareSequenceDefinition (R : Set ℕ) : Prop :=
  IsPoincareSequence R

/-- Source: Theorem 9.2.3, Chapter 9, Section 2. -/
theorem furstenbergCorrespondencePrinciple :
    FurstenbergCorrespondencePrinciple := by
  sorry

/-- Source: Theorem 9.2.4, Chapter 9, Section 2. -/
theorem poincareSequencesCharacterizedByDifferenceSets
    (R : Set ℕ) :
    IsPoincareSequence R ↔
      IsPositiveNaturalSet R ∧
        ∀ E : Set ℕ, HasPositiveUpperBanachDensity E ->
          (R ∩ naturalDifferenceSet E).Nonempty := by
  sorry

/-- Source: Corollary 9.2.5, Chapter 9, Section 2. -/
theorem poincareSequencesAreRecurrenceSetsAndDifferenceSetsSyndetic
    (R E : Set ℕ) :
    (IsPoincareSequence R -> Chapter05.IsRecurrenceSet R) ∧
      (HasPositiveUpperBanachDensity E -> IsSyndeticSet (naturalDifferenceSet E)) := by
  sorry

/-- Source: Theorem 9.2.6, Chapter 9, Section 2. -/
theorem poincareMultipleRecurrenceTheorem
    (M : MeasurableSystem.{u}) :
    MultiplePoincareRecurrenceStatement M := by
  sorry

/-- Source: Theorem 9.2.7, Chapter 9, Section 2. -/
theorem furstenbergPositiveCesaroMultipleRecurrence
    (M : MeasurableSystem.{u}) :
    PositiveCesaroMultipleRecurrenceFromOne M := by
  sorry

end Section02
end Chapter09
