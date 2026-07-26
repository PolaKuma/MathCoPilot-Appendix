import Chapter06.Section02

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter06

universe u v w

namespace Section03


/--
Source: Definition 6.3.1, Chapter 6, Section 3.
A generic point for an invariant measure is a point whose empirical orbit
measures converge weak-star to that measure.
-/
def genericPoint (S : System.{u}) (μ : MeasureOn S.X) (x : S.X) : Prop :=
  IsGenericPoint S μ x

/-- Source: Definition 6.3.1, Chapter 6, Section 3. -/
def genericPointSetForMeasure (S : System.{u}) (μ : MeasureOn S.X) : Set S.X :=
  genericPointSet S μ

/--
Source: Lemma 6.3.2, Chapter 6, Section 3.
The generic-point set is Borel, and an invariant measure is ergodic exactly when
its generic-point set has full measure.
-/
theorem genericPointSetBorelAndFullIffErgodic
    (S : System.{u}) (μ : MeasureOn S.X) :
    IsInvariantMeasure S μ -> IsBorelSet (genericPointSet S μ) ∧
      (IsErgodicMeasure S μ ↔ μ.measure (genericPointSet S μ) = 1) := by
  sorry

/-- Source: Definition 6.3.3, Chapter 6, Section 3. -/
def measureSupport {X : Type u} [TopologicalSpace X] (μ : MeasureOn X) : Set X :=
  support μ

/--
Source: Theorem 6.3.4, Chapter 6, Section 3.
The support of an invariant measure is nonempty, invariant, full measure, and
nonwandering; if the measure is ergodic, the support system is transitive and
almost every point in the support is transitive.
-/
theorem invariantMeasureSupportProperties
    (S : System.{u}) (μ : MeasureOn S.X) :
    IsInvariantMeasure S μ ->
      (support μ).Nonempty ∧ IsClosed (support μ) ∧
        ∃ hforward : S.T '' support μ ⊆ support μ,
          μ.measure (support μ) = 1 ∧
            Chapter05.nonwanderingSet (supportSystem S μ hforward) = Set.univ := by
  sorry

/--
Source: Theorem 6.3.4, Chapter 6, Section 3.
For an ergodic invariant measure, the support system is transitive and the set
of transitive points in the support has full measure.
-/
theorem ergodicMeasureSupportIsTransitive
    (S : System.{u}) (μ : MeasureOn S.X) :
    IsErgodicMeasure S μ ->
      ∃ hforward : S.T '' support μ ⊆ support μ,
        Chapter05.IsTopologicallyTransitive (supportSystem S μ hforward) ∧
          μ.measure (Subtype.val '' Chapter05.transitivePointSet (supportSystem S μ hforward)) = 1 := by
  sorry

/--
Source: Corollary 6.3.5, Chapter 6, Section 3.
On a minimal system, every invariant measure has full support.
-/
theorem minimalSystemInvariantMeasureHasFullSupport
    (S : System.{u}) (μ : MeasureOn S.X) :
    Chapter05.IsMinimalSystem S -> IsInvariantMeasure S μ -> support μ = Set.univ := by
  sorry

/--
Source: Corollary 6.3.5, Chapter 6, Section 3.
The density of recurrent points in the support gives another proof of Birkhoff
recurrence.
-/
def supportRecurrenceBirkhoffRemark (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  IsInvariantMeasure S μ ->
    ∃ hforward : S.T '' support μ ⊆ support μ,
      Dense (Chapter05.recurrentPointSet (supportSystem S μ hforward))

/--
Source: Theorem 6.3.6, Chapter 6, Section 3.
For every invariant measure, the recurrent point set has full measure.
-/
theorem recurrentPointsHaveFullInvariantMeasure
    (S : System.{u}) (μ : MeasureOn S.X) :
    IsInvariantMeasure S μ -> μ.measure (Chapter05.recurrentPointSet S) = 1 := by
  sorry

/--
Source: Remark 6.3.7, Chapter 6, Section 3.
Using a countable base, the complement of the recurrent set is a countable union
of wandering pieces of measure zero.
-/
def countableBaseProofOfFullRecurrenceRemark (S : System.{u}) (μ : MeasureOn S.X) : Prop :=
  IsInvariantMeasure S μ ->
    ∃ U : ℕ -> Set S.X,
      TopologicalSpace.IsTopologicalBasis (Set.range U) ∧
      let W := fun n : ℕ => U n \ ⋃ i : ℕ, (S.T^[i + 1]) ⁻¹' U n
      (∀ n : ℕ, μ.measure (W n) = 0) ∧
      Set.univ \ Chapter05.recurrentPointSet S = ⋃ n : ℕ, W n ∧
      μ.measure (Chapter05.recurrentPointSet S) = 1

end Section03
end Chapter06
