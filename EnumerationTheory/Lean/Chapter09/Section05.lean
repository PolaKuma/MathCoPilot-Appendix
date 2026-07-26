import Chapter09.Section04

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section05

universe u

/-- Source: Theorem 9.5.1, Chapter 9, Section 5. -/
theorem rothTheoremNumberTheoretic
    (E : Set ℕ) :
    HasPositiveUpperBanachDensity E -> ∃ a b : ℕ, 0 < b ∧ a ∈ E ∧ a + b ∈ E ∧ a + 2 * b ∈ E := by
  sorry

/-- Source: Theorem 9.5.2, Chapter 9, Section 5. -/
theorem rothTheoremDynamical
    (M : MeasurableSystem.{u}) :
    RothAveragePositive M := by
  sorry

/-- Source: Lemma 9.5.3, Chapter 9, Section 5. -/
theorem productTelescopingIdentity :
    ProductTelescopingIdentity := by
  intro k
  induction k with
  | zero =>
      intro a b
      simp
  | succ k ih =>
      intro a b
      have htail := ih (fun i : Fin k => a i.succ) (fun i : Fin k => b i.succ)
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
      simp [Finset.prod_filter, Fin.prod_univ_succ] at htail ⊢
      simp only [mul_assoc] at htail
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      rw [← htail]
      ring

/-- Source: Lemma 9.5.4, Chapter 9, Section 5. -/
theorem compactSelfAdjointCommutingOperatorEigenfunctions
    (M : MeasurableSystem.{u}) :
    CompactSelfAdjointCommutingOperatorStatement M := by
  sorry

/-- Source: Theorem 9.5.5, Chapter 9, Section 5. -/
theorem furstenbergWeissDoubleAverageConvergence
    (M : MeasurableSystem.{u}) :
    Chapter02.IsErgodic M -> KroneckerFactorControlsDoubleAverage M 1 2 := by
  sorry

/-- Source: Remark 9.5.6, Chapter 9, Section 5. -/
theorem furstenbergWeissDoubleAverageForDistinctIntegerPowers
    (M : MeasurableSystem.{u}) :
    Chapter02.IsErgodic M ->
      ∀ a b : ℤ, KroneckerFactorControlsDoubleAverage M a b := by
  sorry

/-- Source: Theorem 9.5.7, Chapter 9, Section 5. -/
theorem kroneckerSystemsHavePositiveMultipleRecurrence
    (M : MeasurableSystem.{u}) :
    IsKroneckerSystem M -> HasSZProperty M := by
  sorry

end Section05
end Chapter09
