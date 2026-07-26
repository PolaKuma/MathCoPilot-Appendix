import Chapter04.Section05

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u v

namespace Section06

/--
Source: Theorem 4.6.1, Chapter 4, Section 6.
Ergodic decomposition theorem: a measure-preserving system over a Borel
probability space decomposes into ergodic component measures whose integral is
the original measure.
-/
theorem ergodicDecompositionTheorem (M : System.{u}) :
    Chapter01.IsMeasurePreservingSystem M ->
    IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      ∃ D : ErgodicDecompositionData M, IsErgodicDecomposition M D := by
  exact MathCopilotPrior.chapter04_results.ergodic_decomposition M

/--
Source: Theorem 4.6.2, Chapter 4, Section 6.
The ergodic decomposition can be expressed as a factor map onto a Borel
probability system whose fibers carry the ergodic components.
-/
theorem factorErgodicDecompositionTheorem (M : System.{u}) :
    Chapter01.IsMeasurePreservingSystem M ->
    IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      HasFactorErgodicDecomposition M := by
  exact MathCopilotPrior.chapter04_results.factor_ergodic_decomposition M

end Section06
end Chapter04
