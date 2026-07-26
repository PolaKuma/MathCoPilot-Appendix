import Chapter03.ContinuedFractions.GaussMeasure
import Chapter03.ContinuedFractions.GaussErgodic
import Chapter03.ContinuedFractions.DigitFrequency
import Chapter03.LimitLaws.MetricLaws
import Chapter03.LimitLaws.LevyLaws
import Chapter03.LimitLaws.ErrorLaws

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter03
namespace Section02

/--
Source: Proposition 3.2.1, Chapter 3, Section 2.
The continued fraction system `([0,1], B([0,1]), μ, T)` is measure preserving.
-/
theorem continuedFractionSystemIsMeasurePreserving :
    IsMeasurePreservingGaussSystem
      { μ := gaussMeasure, T := gaussMap } := by
  exact ⟨rfl, rfl, gaussMeasure_isProbability, gaussMap_measurePreserving⟩

/--
Source: Lemma 3.2.2, Chapter 3, Section 2.
For every irrational `x ∈ [0,1]`, if `aₙ(x)` is defined by the continued
fraction map, then `x = [a₁(x), a₂(x), …]`.
-/
theorem irrationalPointEqualsContinuedFractionFromDigits (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) (hirr : Irrational x) :
    HasContinuedFractionExpansion x (gaussPartialQuotients x) := by
  exact Section01.gaussPartialQuotients_expansion x hx hirr

/--
Source: Remark 3.2.3, Chapter 3, Section 2.
The coding map from sequences of positive integers to continued fractions
semiconjugates the shift with the Gauss map; the remark also introduces the
notation `pₙ(x), qₙ(x)` and complete quotients.
-/
def continuedFractionShiftSemiconjugacyAndCompleteQuotientsRemark : Prop :=
  ShiftSemiconjugatesContinuedFractionMap ∧ CompleteQuotientRelations

/--
Source: Theorem 3.2.4, Chapter 3, Section 2.
The continued fraction system `([0,1], B([0,1]), μ, T)` is ergodic.
-/
theorem continuedFractionSystemIsErgodic :
    IsErgodicGaussSystem { μ := gaussMeasure, T := gaussMap } := by
  exact gaussSystem_isErgodic

/--
Source: Theorem 3.2.5, Chapter 3, Section 2.
For almost every `x = [a₁, a₂, …]`, the frequency of the digit `j` is
`(2 log(1+j) - log j - log(2+j)) / log 2`.
-/
theorem almostEveryDigitFrequencyFormula (j : ℕ) (hj : 0 < j) :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => digitFrequency (gaussPartialQuotients x) j (n + 1)) atTop
        (nhds ((2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
          Real.log (2 + (j : ℝ))) / Real.log 2)) := by
  exact digitFrequency_formula_ae j hj

/--
Source: Theorem 3.2.5, Chapter 3, Section 2.
For almost every continued fraction, the geometric mean of the partial quotients
tends to Khinchin's constant.
-/
theorem almostEveryGeometricMeanPartialQuotients :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => geometricMeanPartialQuotients
          (gaussPartialQuotients x) (n + 1)) atTop
        (nhds khinchinConstant) := by
  exact geometricMean_formula_ae

/--
Source: Theorem 3.2.5, Chapter 3, Section 2.
For almost every continued fraction, the arithmetic mean of the partial
quotients diverges to infinity.
-/
theorem almostEveryArithmeticMeanPartialQuotientsDiverges :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
          (Finset.range (n + 1)).sum
            (fun k => ((gaussPartialQuotients x).tail k : ℝ)))
        atTop atTop := by
  exact arithmeticMeanPartialQuotients_diverges_ae

/--
Source: Theorem 3.2.5, Chapter 3, Section 2.
For almost every `x`, `(1/n) log qₙ(x)` tends to `π²/(12 log 2)`.
-/
theorem almostEveryConvergentDenominatorGrowth :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
          Real.log
        (convergentDenominator (gaussPartialQuotients x) (n + 1) : ℝ))
        atTop (nhds levyConstant) := by
  exact convergentDenominator_growth_ae

/--
Source: Theorem 3.2.5, Chapter 3, Section 2.
For almost every `x`, `(1/n) log |x - pₙ(x)/qₙ(x)|` tends to
`-π²/(6 log 2)`.
-/
theorem almostEveryConvergentApproximationErrorExponent :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
          Real.log |x - ((finiteContinuedFraction
            (gaussPartialQuotients x) (n + 1) : ℚ) : ℝ)|)
        atTop (nhds continuedFractionErrorExponent) := by
  exact convergentApproximationError_exponent_ae

end Section02
end Chapter03
