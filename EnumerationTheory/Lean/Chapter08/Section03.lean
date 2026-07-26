import Chapter08.Section02

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators

namespace Chapter08

universe u v

namespace Section03

/-- Source: Lemma 8.3.1.  `K` is `J ×_N J`; its `X × X` marginal is `μ × μ`. -/
theorem relativelyIndependentSelfProduct_productProjectionForcesProductJoining
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) (K : Measure ((M.X × N.X) × M.X)) :
    IsRelativelyIndependentSelfProductOverRight M N J K ->
      MeasurePreserving (fun p : (M.X × N.X) × M.X => (p.1.1, p.2))
        K (M.μ.prod M.μ) ->
        IsProductJoining M N J := by
  sorry

/-- Source: Theorem 8.3.2. -/
theorem weakMixingProductWithEveryErgodicSystem
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Chapter02.IsWeakMixing M -> Chapter02.IsErgodic N ->
      Chapter02.IsErgodic
        { X := M.X × N.X,
          measurableSpace := inferInstance,
          μ := M.μ.prod N.μ,
          T := fun p => (M.T p.1, N.T p.2) } := by
  sorry

/-- Source: Theorem 8.3.3 (Ornstein). -/
theorem ornsteinStrongMixingCriterion (M : MeasurableSystem.{u}) :
    Chapter02.IsStrongMixing M ↔
      Chapter02.IsWeakMixing M ∧ ∃ θ : ℝ, 0 < θ ∧
        ∀ A B : Set M.X, MeasurableSet A -> MeasurableSet B ->
          Filter.limsup
            (fun n : ℕ => (M.μ (A ∩ (M.T^[n]) ⁻¹' B)).toReal) atTop
              ≤ θ * (M.μ A).toReal * (M.μ B).toReal := by
  sorry

/-- Source: Question 8.3.4 (the book records this as an open existence question). -/
def pairwiseIndependentNonproductZeroEntropyTripleJoiningQuestion : Prop :=
  ∃ M : MeasurableSystem.{u}, HasPairwiseIndependentNonproductTripleSelfJoining M

end Section03
end Chapter08
