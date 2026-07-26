import Chapter09.Section03

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section04

universe u

/-- Source: Theorem 9.4.1, Chapter 9, Section 4. -/
theorem furstenbergSarkozyNumberTheoretic
    (E : Set ℕ) (p : Polynomial ℤ) :
    HasPositiveUpperBanachDensity E -> p.eval 0 = 0 ->
      ∃ x ∈ E, ∃ y ∈ E, ∃ n : ℕ, 0 < n ∧
        (x : ℤ) - (y : ℤ) = p.eval (n : ℤ) := by
  sorry

/-- Source: Theorem 9.4.2, Chapter 9, Section 4. -/
theorem furstenbergSarkozyDynamical
    (M : MeasurableSystem.{u}) :
    PolynomialRecurrenceStatement M := by
  sorry

/-- Source: Remark 9.4.3, Chapter 9, Section 4. -/
theorem polynomialAveragesControlledByRationalKroneckerFactor
    (M : MeasurableSystem.{u}) :
    PolynomialCesaroCharacteristicStatement M := by
  sorry

end Section04
end Chapter09
