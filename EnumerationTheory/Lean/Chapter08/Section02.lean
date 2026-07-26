import Chapter08.Section01

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter08

universe u v w

namespace Section02

/-- Source: Theorem 8.2.1, Chapter 8, Section 2. -/
theorem graphJoining_characterizedBySubSigmaAlgebras
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) :
    IsJoining M N J ->
      (IsGraphJoining M N J ↔
        ∀ B : Set N.X, B ∈ N.𝓧 -> ∃ A : Set M.X, A ∈ M.𝓧 ∧
          ModEqUnderJoining J A B) ∧
      (IsIsomorphismGraphJoining M N J ↔
        (∀ B : Set N.X, B ∈ N.𝓧 -> ∃ A : Set M.X, A ∈ M.𝓧 ∧
          ModEqUnderJoining J A B) ∧
        (∀ A : Set M.X, A ∈ M.𝓧 -> ∃ B : Set N.X, B ∈ N.𝓧 ∧
          ModEqUnderJoining J A B)) := by
  sorry

/-- Source: Theorem 8.2.2, Chapter 8, Section 2. -/
theorem joiningDeterminesCommonFactor
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) :
    IsJoining M N J ->
      ∃ 𝓐 : SubSigmaAlgebra M, ∃ 𝓑 : SubSigmaAlgebra N,
        IsCommonFactorDeterminedByJoining M N J 𝓐 𝓑 := by
  sorry

/-- Source: Theorem 8.2.3, Chapter 8, Section 2. -/
theorem halmosVonNeumann_spectralIsomorphismImpliesIsomorphism
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter04.IsLebesgueProbabilitySpace N.toProbabilitySpace ->
      HasDiscreteSpectrumMeasureSystem M -> HasDiscreteSpectrumMeasureSystem N ->
        (SpectrallyIsomorphic M N ↔ Chapter01.IsIsomorphicSystems M N) := by
  sorry

end Section02
end Chapter08
