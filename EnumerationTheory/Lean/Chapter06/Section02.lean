import Chapter06.Section01

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter06

universe u v w

namespace Section02


/--
Source: Lemma 6.2.1, Chapter 6, Section 2.
A measure is invariant iff integrals of `f ∘ T` and `f` agree for every
continuous test function.
-/
theorem invariantMeasureIffIntegralInvariant
    (S : System.{u}) (μ : MeasureOn S.X) :
    IsInvariantMeasure S μ ↔
      Chapter05.IsTopologicalSystem S ∧ IsProbabilityBorelMeasure μ ∧
        ∀ f : S.X -> ℂ, Continuous f ->
        μ.integral (fun x => f (S.T x)) = μ.integral f := by
  sorry

/--
Source: Lemma 6.2.1, Chapter 6, Section 2.
The invariant-measure set of every topological dynamical system is nonempty.
-/
theorem invariantMeasureSetNonempty (S : System.{u}) :
    Chapter05.IsTopologicalSystem S -> (invariantMeasures S).Nonempty := by
  sorry

/--
Source: Proposition 6.2.2, Chapter 6, Section 2.
Any weak-star limit of Cesaro averages of push-forwards is invariant; in
particular invariant measures exist.
-/
theorem weakStarLimitsOfAveragedPushForwardsAreInvariant
    (S : System.{u}) (σ : ℕ -> MeasureOn S.X) (μ : MeasureOn S.X) :
    Chapter05.IsTopologicalSystem S -> (∀ n, IsProbabilityBorelMeasure (σ n)) ->
      weakStarConverges (fun n : ℕ => averagedPushForwardMeasure S σ (n + 1)) μ ->
      IsInvariantMeasure S μ := by
  sorry

/--
Source: Corollary 6.2.3, Chapter 6, Section 2.
Every weak-star limit of empirical orbit measures is invariant.
-/
theorem weakStarLimitsOfEmpiricalOrbitMeasuresAreInvariant
    (S : System.{u}) (x : S.X) (μ : MeasureOn S.X) :
    Chapter05.IsTopologicalSystem S ->
      weakStarConverges (fun n : ℕ => orbitAverageMeasure S x (n + 1)) μ ->
      IsInvariantMeasure S μ := by
  sorry

/--
Source: Theorem 6.2.4, Chapter 6, Section 2.
The set of invariant measures is a compact convex subset of the space of
probability measures.
-/
theorem invariantMeasuresCompactConvex (S : System.{u}) :
    Chapter05.IsTopologicalSystem S -> IsCompactConvexSet (invariantMeasures S) := by
  sorry

/--
Source: Definition 6.2.5, Chapter 6, Section 2.
An extreme point of a convex set is a point that cannot be written as a
nontrivial convex combination of two different points of the set.
-/
def extremePointOfConvexSet {E : Type u} [Add E] [SMul ℝ E]
    (K : Set E) (x : E) : Prop :=
  IsExtremePoint K x

/--
Source: Definition 6.2.5, Chapter 6, Section 2.
The set of extreme points of a convex set.
-/
def extremePointSet {E : Type u} [Add E] [SMul ℝ E] (K : Set E) : Set E :=
  extremePoints K

/--
Source: Theorem 6.2.6, Chapter 6, Section 2.
Krein-Milman theorem: a compact convex subset of a locally convex Hausdorff
space has nonempty `G_delta` extreme boundary whose convex hull is dense.
-/
theorem kreinMilmanTheoremStatement
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] [SecondCountableTopology E] (K : Set E) :
    IsCompactConvexSet K -> K.Nonempty ->
      (extremePoints K).Nonempty ∧ IsGDeltaSet (extremePoints K) ∧
      closure (convexHullSet (extremePoints K)) = K := by
  sorry

/--
Source: Proposition 6.2.7, Chapter 6, Section 2.
Invariant measures are ergodic exactly when they are extreme points of the
compact convex invariant-measure set.
-/
theorem ergodicMeasureIffExtremeInvariantMeasure
    (S : System.{u}) (μ : MeasureOn S.X) :
    μ ∈ invariantMeasures S -> (IsErgodicMeasure S μ ↔ IsExtremePoint (invariantMeasures S) μ) := by
  sorry

/--
Source: Proposition 6.2.8, Chapter 6, Section 2.
Distinct ergodic invariant measures are mutually singular, and absolute
continuity between ergodic invariant measures forces equality.
-/
theorem ergodicMeasuresMutuallySingularOrEqual
    (S : System.{u}) (μ ν : MeasureOn S.X) :
    IsErgodicMeasure S μ -> IsErgodicMeasure S ν ->
      (μ ≠ ν -> MutuallySingular μ ν) ∧ (AbsolutelyContinuous μ ν -> μ = ν) := by
  sorry

/--
Source: Theorem 6.2.9, Chapter 6, Section 2.
The ergodic measures form a nonempty `G_delta` subset of the invariant-measure
simplex, and their convex hull is dense.
-/
theorem ergodicMeasuresDenseExtremeBoundary (S : System.{u}) :
    Chapter05.IsTopologicalSystem S ->
      (ergodicMeasures S).Nonempty ∧ IsGDeltaSet (ergodicMeasures S) ∧
        closure (convexHullSet (ergodicMeasures S)) = invariantMeasures S := by
  sorry

/--
Source: Theorem 6.2.10, Chapter 6, Section 2.
Choquet theorem: points in a compact convex set have representing probability
measures supported on the extreme boundary.  The book prints uniqueness for an
arbitrary compact convex set; that clause is false without the simplex
hypothesis, so this statement records the standard existence theorem.
-/
theorem choquetTheoremStatement
    {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] [SecondCountableTopology E] (K : Set E) (m : E) :
    IsCompactConvexSet K -> m ∈ K -> HasChoquetRepresentation K m := by
  sorry

/--
Source: Theorem 6.2.11, Chapter 6, Section 2.
Ergodic decomposition theorem for topological systems: every invariant measure
has a representing probability measure on the ergodic measures, and continuous
integrals decompose accordingly.
-/
theorem topologicalErgodicDecompositionTheorem
    (S : System.{u}) (μ : MeasureOn S.X) :
    IsInvariantMeasure S μ -> HasErgodicDecomposition S μ := by
  sorry

/--
Source: Theorem 6.2.12, Chapter 6, Section 2.
A factor map sends invariant measures onto invariant measures and ergodic
measures onto ergodic measures.
-/
theorem factorMapPushesInvariantAndErgodicMeasuresOnto
    (S : System.{u}) (R : System.{v}) (π : S.X -> R.X) :
    Chapter05.IsFactorMap S R π ->
      factorPushForwardMap S R π '' invariantMeasures S = invariantMeasures R ∧
        factorPushForwardMap S R π '' ergodicMeasures S = ergodicMeasures R := by
  sorry

end Section02
end Chapter06
