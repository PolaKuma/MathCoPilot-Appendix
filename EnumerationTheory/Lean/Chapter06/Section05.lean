import Chapter06.Section04

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter06

universe u v w

namespace Section05


/-- Source: Definition 6.5.1, Chapter 6, Section 5. -/
def topologicalModel (M : MeasurableSystem.{u}) (D : TopologicalModelData M) : Prop :=
  IsTopologicalModel M D

/-- Source: Definition 6.5.1, Chapter 6, Section 5. -/
def hasTopologicalRealization (M : MeasurableSystem.{u}) : Prop :=
  HasTopologicalModel M

/--
Source: Theorem 6.5.2, Chapter 6, Section 5.
Furstenberg theorem: every invertible measure-preserving system has a
topological model.
-/
theorem furstenbergEveryInvertibleSystemHasTopologicalModel
    (M : MeasurableSystem.{u}) :
    Chapter01.IsMeasurePreservingSystem M ->
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T ->
        HasTopologicalModel M := by
  sorry

/--
Source: Theorem 6.5.3, Chapter 6, Section 5.
Weiss universal model theorem: there is a reversible minimal system on which
every reversible nonatomic ergodic system appears as a measure model.
-/
theorem weissUniversalMinimalTopologicalModel :
    HasMinimalUniversalTopologicalModel := by
  sorry

/--
Source: Theorem 6.5.4, Chapter 6, Section 5.
Jewett-Krieger theorem: every invertible ergodic system has a uniquely ergodic
minimal topological model.
-/
theorem jewettKriegerTheorem
    (M : MeasurableSystem.{u}) :
    Chapter01.IsMeasurePreservingSystem M ->
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T ->
      Chapter02.IsErgodic M -> HasUniquelyErgodicMinimalTopologicalModel M := by
  sorry

/--
Source: Theorem 6.5.5, Chapter 6, Section 5.
Lehrer's strengthening: every invertible nonatomic ergodic system has a minimal,
uniquely ergodic, strongly mixing topological model.
-/
theorem lehrerStrongMixingModelTheorem
    (M : MeasurableSystem.{u}) :
    Chapter01.IsMeasurePreservingSystem M ->
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter01.IsInvertibleMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ M.T ->
      IsNonatomicSystem M -> Chapter02.IsErgodic M ->
        HasStrongMixingUniquelyErgodicTopologicalModel M := by
  sorry

/--
Source: Theorem 6.5.5, Chapter 6, Section 5.
A topological model of a factor map is a commuting topological factor map
between topological models of the two measure systems.
-/
def topologicalModelOfFactorMap
    (M N : MeasurableSystem.{u}) (D : TopologicalModelData M) (E : TopologicalModelData N)
    (πm : M.X → N.X) (πt : D.topologicalSystem.X -> E.topologicalSystem.X) : Prop :=
  IsTopologicalModelOfFactor M N D E πm πt

/--
Source: Theorem 6.5.6, Chapter 6, Section 5.
Relative Jewett-Krieger-Weiss theorem: a factor map over a uniquely ergodic
model of the factor admits a uniquely ergodic topological model realizing the
whole extension.
-/
theorem weissRelativeJewettKriegerTheorem
    (M N : MeasurableSystem.{u}) (πm : M.X → N.X) (E : TopologicalModelData N) :
    Chapter01.IsFactorMap M N πm ->
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace ->
      Chapter04.IsLebesgueProbabilitySpace N.toProbabilitySpace ->
      Chapter02.IsErgodic M ->
      IsTopologicalModel N E -> IsUniquelyErgodic E.topologicalSystem ->
      ∃ D : TopologicalModelData M, ∃ π : D.topologicalSystem.X -> E.topologicalSystem.X,
        IsTopologicalModelOfFactor M N D E πm π ∧ IsUniquelyErgodic D.topologicalSystem := by
  sorry

end Section05
end Chapter06
