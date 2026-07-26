import Chapter09.Section07

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter09
namespace Section08

universe u v w

/-- Source: Theorem 9.8.1, Chapter 9, Section 8. -/
theorem hostKraMultipleErgodicAverageConvergence
    (M : MeasurableSystem.{u}) (d : ℕ) :
    MultipleErgodicAverageConvergesL2 M d := by
  sorry

/-- Source: Theorem 9.8.2, Chapter 9, Section 8. -/
theorem taoCommutingTransformationsAverageConvergence
    (M : MeasurableSystem.{u}) (d : ℕ) :
    CommutingMultipleErgodicAverageConvergesL2 M d := by
  sorry

/-- Source: Definition 9.8.3, Chapter 9, Section 8. -/
def idempotentAndHereditaryClasses
    (Γ : Type u) [Group Γ] (C : IdempotentClass.{u, v} Γ) : Prop :=
  IsIdempotentClass C ∧ IsHereditaryIdempotentClass C

/-- Source: Remark 9.8.4, Chapter 9, Section 8. -/
theorem examplesAndNonexamplesOfHereditaryIdempotentClasses
    : IdempotentClassExamplesStatement.{u, v} := by
  sorry

/-- Source: Lemma 9.8.5, Chapter 9, Section 8. -/
theorem maximalIdempotentClassFactorExists
    (Γ : Type u) [Group Γ]
    (C : IdempotentClass.{u, v} Γ) (X : GammaSystem.{u, v} Γ) :
    MaximalCfactorStatement C X := by
  sorry

/-- Source: Definition 9.8.6, Chapter 9, Section 8. -/
def maximalCfactor
    (Γ : Type u) [Group Γ]
    (C : IdempotentClass.{u, v} Γ) (X : GammaSystem.{u, v} Γ) : Prop :=
  MaximalCfactorStatement C X

/-- Source: Definition 9.8.7, Chapter 9, Section 8. -/
def joinOfIdempotentClasses
    (Γ : Type u) [Group Γ]
    (C D : IdempotentClass.{u, v} Γ) : IdempotentClass.{u, v} Γ :=
  JoinIdempotentClasses C D

/-- Source: Definition 9.8.8, Chapter 9, Section 8. -/
def satedSystemForIdempotentClass
    (Γ : Type u) [Group Γ]
    (C : IdempotentClass.{u, v} Γ) (X : GammaSystem.{u, v} Γ) : Prop :=
  IsSatedForClass C X

/-- Source: Theorem 9.8.9, Chapter 9, Section 8. -/
theorem austinSatedExtensionTheorem :
    AustinSatedExtensionStatement := by
  sorry

end Section08
end Chapter09
