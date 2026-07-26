import Chapter09.Section05

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators

namespace Chapter09
namespace Section06

universe u v

/-- Source: Definition 9.6.1, Chapter 9, Section 6. -/
def separatingSieveAndMeasureDistal
    (M : MeasurableSystem.{u}) : Prop :=
  IsParryMeasureDistal M

/-- Source: Definition 9.6.2, Chapter 9, Section 6. -/
def relativelyAlmostPeriodicOverFactor
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X)
    (f : M.X -> ℂ) : Prop :=
  RelativelyAlmostPeriodicFunction M N π f

/-- Source: Definition 9.6.3, Chapter 9, Section 6. -/
def compactAndRelativelyWeakMixingExtensions
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Prop × Prop :=
  (IsCompactExtension M N π, IsRelativelyWeakMixingExtension M N π)

/-- Source: Remark 9.6.4, Chapter 9, Section 6. -/
theorem compactAndWeakMixingExtensionEquivalentDefinitions
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    RelativeExtensionSpaceCharacterization M N π := by
  sorry

/-- Source: Remark 9.6.5, Chapter 9, Section 6. -/
theorem compactExtensionsRepresentedBySkewProducts
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
    Chapter04.IsLebesgueProbabilitySpace N.toProbabilitySpace ->
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N -> IsCompactExtension M N π ->
      ∃ G : Type u, ∃ _ : Group G, ∃ _ : TopologicalSpace G,
      ∃ _ : MeasurableSpace G, ∃ _ : BorelSpace G,
      ∃ _ : IsTopologicalGroup G, ∃ _ : CompactSpace G,
      ∃ Q : Type u, ∃ _ : TopologicalSpace Q, ∃ _ : MeasurableSpace Q,
      ∃ _ : BorelSpace Q, ∃ _ : CompactSpace Q, ∃ _ : PseudoMetricSpace Q,
      ∃ act : G -> Q ≃ₜ Q,
        act 1 = Homeomorph.refl Q ∧
        (∀ g h, act (g * h) = (act h).trans (act g)) ∧
        (∀ q r : Q, ∃ g : G, act g q = r) ∧
      ∃ mQ : Measure Q, IsProbabilityMeasure mQ ∧
        (∀ g, MeasurePreserving (act g) mQ mQ) ∧
      ∃ cocycle : N.X -> G, Measurable cocycle ∧
      ∃ e : M.X ≃ (N.X × Q), Measurable e ∧ Measurable e.symm ∧
        Measure.map e M.μ = N.μ.prod mQ ∧
        (∀ᵐ x ∂M.μ, (e x).1 = π x) ∧
        ∀ᵐ x ∂M.μ, e (M.T x) =
          (N.T (e x).1, act (cocycle (e x).1) (e x).2) := by
  sorry

/-- Source: Definition 9.6.6, Chapter 9, Section 6. -/
def zimmerMeasureDistalTowerDefinition
    (M : MeasurableSystem.{u}) : Prop :=
  IsMeasureDistal M

/-- Source: Remark 9.6.7, Chapter 9, Section 6. -/
theorem measureDistalTakenAsZimmerTowerDefinition
    (M : MeasurableSystem.{u}) :
    zimmerMeasureDistalTowerDefinition M ↔ IsMeasureDistal M := by
  rfl

/-- Source: Theorem 9.6.8, Chapter 9, Section 6. -/
theorem furstenbergZimmerStructureTheorem
    (M : MeasurableSystem.{u}) :
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter02.IsErgodic M -> IsFurstenbergZimmerTower M := by
  sorry

/-- Source: Theorem 9.6.9, Chapter 9, Section 6. -/
theorem furstenbergZimmerRelativeDichotomy
    (M : MeasurableSystem.{u}) (N : MeasurableSystem.{v}) (π : M.X -> N.X) :
    Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
    Chapter04.IsLebesgueProbabilitySpace N.toProbabilitySpace ->
    Chapter02.IsErgodic M -> Chapter02.IsErgodic N -> Chapter01.IsFactorMap M N π ->
      RelativeStructureDichotomy M N π := by
  sorry

/-- Source: Definition 9.6.10, Chapter 9, Section 6. -/
def relativeErgodicExtensionForGroupElement
    {Γ : Type u} [Group Γ] (X Y : GammaSystem.{u, v} Γ)
    (π : X.X -> Y.X) (γ : Γ) : Prop :=
  IsGammaErgodicExtensionForElement X Y π γ

/-- Source: Definition 9.6.11, Chapter 9, Section 6. -/
def relativeWeakMixingExtensionForGroupAction
    {Γ : Type u} [Group Γ] (X Y : GammaSystem.{u, v} Γ)
    (π : X.X -> Y.X) : Prop :=
  ∀ γ : Γ, γ ≠ 1 -> IsGammaWeakMixingExtensionForElement X Y π γ

/-- Source: Definition 9.6.12, Chapter 9, Section 6. -/
def compactExtensionForGroupAction
    {Γ : Type u} [Group Γ] (X Y : GammaSystem.{u, v} Γ)
    (π : X.X -> Y.X) : Prop :=
  IsGammaCompactExtension X Y π

/-- Source: Theorem 9.6.13, Chapter 9, Section 6. -/
theorem furstenbergZimmerStructureForFiniteRankFreeAbelianActions :
    FiniteRankFreeAbelianFurstenbergZimmerStatement := by
  sorry

/-- Source: Theorem 9.6.14, Chapter 9, Section 6. -/
theorem commutingTransformationsPositiveCesaroMultipleRecurrence
    (M : MeasurableSystem.{u}) :
    CommutingMultipleRecurrenceStatement M := by
  sorry

/-- Source: Theorem 9.6.15, Chapter 9, Section 6. -/
theorem commutingTransformationsMultipleRecurrence
    (M : MeasurableSystem.{u}) :
    CommutingMultiplePoincareRecurrenceStatement M := by
  sorry

end Section06
end Chapter09
