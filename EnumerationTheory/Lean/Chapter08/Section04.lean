import Chapter08.Section03

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter08

universe u v w

namespace Section04

/-- Source: Definition 8.4.1, Chapter 8, Section 4. -/
def disjointMeasurePreservingSystems
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) : Prop :=
  IsDisjoint M N

/-- Source: Definition 8.4.2, Chapter 8, Section 4. -/
def relativelyDisjointSystemsOverCommonFactor
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (Z : MeasurableSystem.{w})
    (π : M.X -> Z.X) (φ : N.X -> Z.X) : Prop :=
  IsRelativelyDisjointOver M N Z π φ

/-- Source: Proposition 8.4.3, Chapter 8, Section 4. -/
theorem nontrivialSystemsAreNotDisjointFromThemselvesOrFactors
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    (IsNontrivialSystem M -> ¬ IsDisjoint M M) ∧
      (Chapter01.IsFactorMap M N π -> IsNontrivialSystem N -> ¬ IsDisjoint M N) := by
  sorry

/-- Source: Theorem 8.4.4, Chapter 8, Section 4. -/
theorem ergodicIffDisjointFromAllIdentitySystems
    (Y : MeasurableSystem.{u}) :
    Chapter02.IsErgodic Y ↔
      ∀ X : MeasurableSystem.{u}, IsIdentitySystem X -> IsDisjoint X Y := by
  sorry

/-- Source: Theorem 8.4.5, Chapter 8, Section 4. -/
theorem furstenbergWeakMixingMultipleAverage
    (M : MeasurableSystem.{u}) (k : ℕ) (A : Fin (k + 1) -> Set M.X) :
    Chapter02.IsWeakMixing M -> (∀ i : Fin (k + 1), A i ∈ M.𝓧) ->
      Tendsto (fun N : ℕ => multipleRecurrenceAverage M k A N) atTop
        (nhds (multipleMeasureProduct M k A)) := by
  sorry

/-- Source: Definition 8.4.6, Chapter 8, Section 4. -/
def ergodicExtension
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) : Prop :=
  IsErgodicExtension M N π

/-- Source: Theorem 8.4.7, Chapter 8, Section 4. -/
theorem ergodicExtensionIffRelativelyDisjointFromIdentityExtensions
    (Y : MeasurableSystem.{u}) (Z : MeasurableSystem.{v}) (φ : Y.X -> Z.X) :
    IsIdentitySystem Z -> Chapter01.IsFactorMap Y Z φ ->
      (IsErgodicExtension Y Z φ ↔
        ∀ X : MeasurableSystem.{u}, ∀ π : X.X -> Z.X,
          IsIdentitySystem X -> Chapter01.IsFactorMap X Z π ->
            IsRelativelyDisjointOver Y X Z φ π) ∧
      (Chapter02.IsErgodic Y ↔
        ∀ X : MeasurableSystem.{u}, IsIdentitySystem X -> IsDisjoint X Y) := by
  sorry

/-- Source: Theorem 8.4.8, Chapter 8, Section 4. -/
theorem maximalCommonFactorGivesRelativeIndependenceTower :
    IsRelativeIndependentTowerStatement := by
  sorry

/-- Source: Theorem 8.4.9, Chapter 8, Section 4. -/
theorem disjointnessCharacterizationsForErgodicClasses
    (M : MeasurableSystem.{u}) :
    (Chapter02.IsErgodic M ↔
      ∀ X : MeasurableSystem.{u}, IsIdentitySystem X -> IsDisjoint X M) ∧
      (Chapter02.IsWeakMixing M ↔
        ∀ X : MeasurableSystem.{u}, IsDistalMeasureSystem X -> IsDisjoint X M) ∧
      (IsMildMixingMeasureSystem M ↔
        ∀ X : MeasurableSystem.{u}, IsRigidMeasureSystem X -> IsDisjoint X M) ∧
      (IsKMeasureSystem M ↔
        ∀ X : MeasurableSystem.{u}, IsZeroEntropyMeasureSystem X -> IsDisjoint X M) := by
  sorry

end Section04
end Chapter08
