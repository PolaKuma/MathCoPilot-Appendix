import Chapter07.Section06

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter07

universe u

namespace Section07

/-- Source: Theorem 7.7.1, the variational principle. -/
theorem variationalPrinciple
    (S : System.{u}) [Nonempty S.X] [CompactSpace S.X]
    (hS : Chapter05.IsTopologicalSystem S) :
    (∀ μ : MeasureOn S.X, Chapter06.IsInvariantMeasure S μ ->
      entropyMap S μ ≤ topologicalEntropy S) ∧
      topologicalEntropy S =
        sSup {h : EReal | ∃ μ : MeasureOn S.X,
          Chapter06.IsInvariantMeasure S μ ∧ h = entropyMap S μ} := by
  sorry

/-- Source: Corollary 7.7.2. -/
theorem variationalPrinciple_ergodicAndInvariantCoreForms
    (S : System.{u}) [Nonempty S.X] [CompactSpace S.X]
    (hS : Chapter05.IsTopologicalSystem S) :
    topologicalEntropy S =
        sSup {h : EReal | ∃ μ : MeasureOn S.X,
          Chapter06.IsErgodicMeasure S μ ∧ h = entropyMap S μ} ∧
      topologicalEntropy S =
        topologicalEntropy (nonwanderingRestrictedSystem S hS.1) ∧
      topologicalEntropy S = topologicalEntropy (eventualRangeSystem S) := by
  sorry

end Section07
end Chapter07
