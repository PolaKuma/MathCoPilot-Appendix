import Chapter09.Section06

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section07

universe u v

/-- Source: Definition 9.7.1, Chapter 9, Section 7. -/
def szPropertyDefinition (M : MeasurableSystem.{u}) : Prop :=
  HasSZProperty M

/-- Source: Lemma 9.7.2, Chapter 9, Section 7. -/
theorem compactExtensionHasPositiveRelativelyAlmostPeriodicSubset
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X)
    (B : Set M.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    IsCompactExtension M N π -> B ∈ M.𝓧 -> 0 < M.μ B ->
      ∃ D : FiberMeasureData M N π, ∃ Btilde : Set M.X, ∃ A : Set N.X,
        MeasurableSet Btilde ∧ Btilde ⊆ B ∧ 0 < M.μ Btilde ∧
        MeasurableSet A ∧ 0 < N.μ A ∧ A = π '' Btilde ∧
        RelativelyAlmostPeriodicFunction M N π
          (fun x => if x ∈ Btilde then 1 else 0) ∧
        (∀ᵐ y ∂N.μ, (y ∈ A →
          (2 : ENNReal)⁻¹ * M.μ Btilde < D.fiberMeasure y Btilde) ∧
          (y ∉ A → D.fiberMeasure y Btilde = 0)) := by
  sorry

/-- Source: Proposition 9.7.3, Chapter 9, Section 7. -/
theorem compactExtensionsPreserveSZProperty
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    IsCompactExtension M N π -> HasSZProperty N -> HasSZProperty M := by
  sorry

/-- Source: Theorem 9.7.4, Chapter 9, Section 7. -/
theorem relativelyWeakMixingExtensionFiberMultipleMixing
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    IsRelativelyWeakMixingExtension M N π ->
      ∃ D : FiberMeasureData M N π, ∀ k : ℕ,
      ∀ B : Fin (k + 1) -> Set M.X, (∀ i, B i ∈ M.𝓧) ->
      Tendsto (fun N0 : ℕ => if N0 = 0 then 0 else
        (N0 : ℝ)⁻¹ * (Finset.range N0).sum fun n =>
          ∫ y, (FiberMultipleMixingError M N π D k n B y) ^ 2 ∂N.μ)
        atTop (nhds 0) := by
  sorry

/-- Source: Remark 9.7.5, Chapter 9, Section 7. -/
theorem fiberMultipleMixingEpsilonApproximationNotation
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    IsRelativelyWeakMixingExtension M N π ->
      ∀ D : FiberMeasureData M N π, ∀ k : ℕ,
      ∀ B : Fin (k + 1) -> Set M.X, (∀ i, MeasurableSet (B i)) →
      ∀ ε : ℝ, 0 < ε ->
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ N1 : ℕ, N0 ≤ N1 ->
        ∃ exceptional : Set (ℕ × N.X),
          (N1 : ℝ)⁻¹ * (Finset.range N1).sum (fun n =>
            (N.μ {y : N.X | (n, y) ∈ exceptional}).toReal) < ε ∧
          ∀ n : ℕ, n < N1 -> ∀ y : N.X, (n, y) ∉ exceptional ->
            |FiberMultipleMixingError M N π D k n B y| < ε := by
  sorry

/-- Source: Proposition 9.7.6, Chapter 9, Section 7. -/
theorem relativelyWeakMixingExtensionsPreserveSZProperty
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    IsRelativelyWeakMixingExtension M N π -> HasSZProperty N -> HasSZProperty M := by
  sorry

/-- Source: Proposition 9.7.7, Chapter 9, Section 7. -/
theorem relativeWeakMixingConditionalExpectationCriterion
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    RelativeWeakMixingConditionalExpectationStatement M N π := by
  sorry

/-- Source: Theorem 9.7.8, Chapter 9, Section 7. -/
theorem relativeWeakMixingCharacteristicFactorForMultipleAverages
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    RelativeWeakMixingCharacteristicStatement M N π := by
  sorry

/-- Source: Theorem 9.7.9, Chapter 9, Section 7. -/
theorem relativelyWeakMixingExtensionStableUnderRelativeSelfProduct
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N ->
    IsRelativelyWeakMixingExtension M N π ->
      ∃ P : RelativeSelfProductData M N π,
        IsRelativelyWeakMixingExtension P.system N P.base := by
  sorry

/-- Source: Theorem 9.7.10, Chapter 9, Section 7. -/
theorem increasingFactorJoinsPreserveSZProperty
    (D : Chapter01.InverseSequenceData.{u})
    (Y : MeasurableSystem.{u}) (π : ∀ n : ℕ, Y.X -> (D.system n).X) :
    Chapter01.IsInverseLimitSystem D Y π ->
      Chapter01.IsInvertibleMeasurePreservingMap
        Y.𝓧 Y.μ Y.𝓧 Y.μ Y.T ->
      (∀ n : ℕ, HasSZProperty (D.system n)) -> HasSZProperty Y := by
  sorry

end Section07
end Chapter09
