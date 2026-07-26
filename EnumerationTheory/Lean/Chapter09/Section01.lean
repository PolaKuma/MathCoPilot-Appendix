import Chapter09.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section01

universe u

/-- Source: Theorem 9.1.1, Chapter 9, Section 1. -/
theorem simultaneousTopologicalRecurrence
    (X : Type u) [PseudoMetricSpace X] [CompactSpace X] [Nonempty X]
    (l : ℕ) (T : Fin l -> X -> X) :
    0 < l -> (∀ i, Continuous (T i)) ->
      IsCommutingFamily T ->
      HasSimultaneousTopologicalRecurrence X T := by
  sorry

/-- Source: Definition 9.1.2, homogeneous system. -/
def homogeneousSystem (S : TopologicalSystem.{u}) : Prop :=
  IsHomogeneousSystem S

/-- Source: Definition 9.1.2, homogeneous closed subset. -/
def homogeneousClosedSubset
    (S : TopologicalSystem.{u}) (A : Set S.X) : Prop :=
  IsHomogeneousClosedSubset S A

/-- Source: Lemma 9.1.3, Chapter 9, Section 1. -/
theorem bowenHomogeneousSubsetApproximateFixedPoint
    (S : TopologicalSystem.{u}) [PseudoMetricSpace S.X] (A : Set S.X) :
    IsHomogeneousClosedSubset S A -> HasApproximateReturnInSubset S A ->
      ∀ ε : ℝ, 0 < ε -> ∃ z ∈ A, ∃ n : ℕ,
        0 < n ∧ dist ((S.T^[n]) z) z < ε := by
  sorry

/-- Source: Lemma 9.1.4, Chapter 9, Section 1. -/
theorem homogeneousSubsetContainsRecurrentPoint
    (S : TopologicalSystem.{u}) [PseudoMetricSpace S.X] (A : Set S.X) :
    IsHomogeneousClosedSubset S A -> HasApproximateReturnInSubset S A ->
      HasRecurrentPointInSubset S A := by
  sorry

/-- Source: Theorem 9.1.5, Chapter 9, Section 1. -/
theorem commutingMapsHaveCommonRecurrentPoint
    (X : Type u) [PseudoMetricSpace X] [CompactSpace X] [Nonempty X]
    (l : ℕ) (T : Fin l -> X -> X) :
    0 < l -> (∀ i, Continuous (T i)) -> IsCommutingFamily T ->
      HasSimultaneousTopologicalRecurrence X T := by
  exact simultaneousTopologicalRecurrence X l T

/-- Source: Theorem 9.1.6, Chapter 9, Section 1. -/
theorem vanDerWaerdenTheorem
    (l : ℕ) (B : Fin l -> Set ℕ) :
    (⋃ j : Fin l, B j) = Set.univ ->
      ∃ j : Fin l, ContainsArbitrarilyLongArithmeticProgressions (B j) := by
  sorry

end Section01
end Chapter09
