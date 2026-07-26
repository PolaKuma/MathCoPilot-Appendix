import Chapter08.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter08

universe u v w

namespace Section01

/-- Source: Definition 8.1.1, Chapter 8, Section 1. -/
def joiningAndSelfJoining (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  IsJoining M N J

/-- Source: Remark 8.1.2, Chapter 8, Section 1. -/
theorem joining_basicRemarks
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Chapter01.IsMeasurePreservingSystem M -> Chapter01.IsMeasurePreservingSystem N ->
    (∃ J : JoiningData M N, IsJoining M N J) ∧
      ((¬ Chapter02.IsErgodic M ∨ ¬ Chapter02.IsErgodic N) ->
        ErgodicJoinings M N = ∅) := by
  sorry

/-- Source: Remark 8.1.2(2), joining of probability spaces without dynamics. -/
def joiningOfUnderlyingProbabilitySpaces
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  IsMeasureSpaceJoining M N J

/-- Source: Definition 8.1.3, Chapter 8, Section 1. -/
def multipleSystemsJoining {ι : Type w} (M : ι -> MeasurableSystem.{u})
    (J : MultipleJoiningData M) : Prop :=
  IsMultipleJoining M J

/--
Source: Definition 8.1.3, Chapter 8, Section 1.
The weak joining topology is metrizable and makes the joining space compact;
under topological models it agrees with the induced weak topology.
-/
theorem joiningSpace_compactMetrizableWeakTopology
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hN : Chapter01.IsMeasurePreservingSystem N)
    (hcgM : Chapter00.CountablyGeneratedFamily M.𝓧)
    (hcgN : Chapter00.CountablyGeneratedFamily N.𝓧) :
    JoiningSpaceTopologyProperties M N := by
  sorry

/-- Source: Theorem 8.1.4, Chapter 8, Section 1. -/
theorem ergodicJoinings_areExtremePointsAndNonempty
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
      (∀ J : JoiningData M N, IsErgodicJoining M N J ↔
        IsJoining M N J ∧ IsExtremePoint (Joinings M N) J) ∧
        (ErgodicJoinings M N).Nonempty := by
  sorry

/-- Source: Example 8.1.5, Chapter 8, Section 1. -/
def graphJoiningExample
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v})
    (J : JoiningData M N) : Prop :=
  IsGraphJoining M N J

/-- Source: Example 8.1.6, the `(k+1)`-fold off-diagonal joining. -/
def offDiagonalJoiningExample
    (M : MeasurableSystem.{u}) (k : ℕ)
    (J : MultipleJoiningData (fun _ : Fin (k + 1) => M)) : Prop :=
  IsOffDiagonalJoining M k J

/-- Source: Example 8.1.6, products of off-diagonal joinings. -/
def poodJoiningExample
    (M : MeasurableSystem.{u}) (k : ℕ)
    (J : MultipleJoiningData (fun _ : Fin k => M)) : Prop :=
  IsPOODJoining M k J

/-- Source: Definition 8.1.7, `k`-simplicity. -/
def kSimpleSystem (M : MeasurableSystem.{u}) (k : ℕ) : Prop :=
  IsKSimple M k

/-- Source: Definition 8.1.7, simplicity in every order `k ≥ 2`. -/
def simpleSystem (M : MeasurableSystem.{u}) : Prop :=
  IsSimpleSystem M

/-- Source: Definition 8.1.7, minimal self-joinings of order `k`. -/
def minimalSelfJoiningsOfOrder
    (M : MeasurableSystem.{u}) (k : ℕ) : Prop :=
  HasMinimalSelfJoiningsOfOrder M k

/-- Source: Definition 8.1.8, Chapter 8, Section 1. -/
def relativelyIndependentJoining
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (Z : MeasurableSystem.{w})
    (π : M.X -> Z.X) (φ : N.X -> Z.X) (J : JoiningData M N) : Prop :=
  IsRelativelyIndependentJoining M N Z π φ J

/--
Source: Definition 8.1.8, Chapter 8, Section 1.
Conditional product measures relative to a joining of factor systems.
-/
def conditionalProductMeasureRelativeToJoining {ι : Type w} [Fintype ι]
    (M : ι -> MeasurableSystem.{u}) (Y : ι -> MeasurableSystem.{v})
    (π : ∀ i : ι, (M i).X -> (Y i).X)
    (ξ : MultipleJoiningData Y)
    (J : MultipleJoiningData M) : Prop :=
  IsConditionalProductMeasure M Y π ξ J

end Section01
end Chapter08
