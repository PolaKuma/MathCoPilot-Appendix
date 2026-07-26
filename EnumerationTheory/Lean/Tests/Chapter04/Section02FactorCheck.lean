import Chapter04.Descriptive.CountableCodeFactor

noncomputable section

open Classical Filter

namespace Chapter04.Section02FactorCheck

universe u

theorem invariantSubsigmaAlgebraGivesFactor
    (M : System.{u}) (F : SetFamily M.X) :
    Chapter01.IsMeasurePreservingSystem M ->
      IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter00.IsSigmaAlgebraFamily F -> F ⊆ M.𝓧 ->
      (∀ A : Set M.X, A ∈ F -> M.T ⁻¹' A ∈ F) ->
        ∃ N : System.{u}, ∃ π : M.X -> N.X,
          Chapter01.IsFactorMap M N π ∧
          IsLebesgueProbabilitySpace N.toProbabilitySpace ∧
          (∀ A : Set M.X, A ∈ F ->
            ∃ B : Set N.X, B ∈ N.𝓧 ∧
              M.μ (Chapter00.symmDiff A (π ⁻¹' B)) = 0) ∧
          (∀ B : Set N.X, B ∈ N.𝓧 -> π ⁻¹' B ∈ F) ∧
          ({A : Set M.X | ∃ B ∈ F, A = M.T ⁻¹' B} = F ->
            IsInvertibleModNull N) := by
  intro hM hLeb hF hsub hInv
  exact CountableCodeFactor.exists_lebesgueFactor_of_invariantSubSigma
    M F hM hLeb hF hsub hInv

end Chapter04.Section02FactorCheck
