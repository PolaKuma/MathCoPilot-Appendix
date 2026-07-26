import Chapter05.Section01

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

namespace Section02

/-- The complete list of conditions (2)--(18) in Theorem 5.2.5. -/
def TransitivityCharacterizations (S : System.{u}) : Prop :=
  let openPairs (P : Set S.X -> Set S.X -> Prop) :=
    ∀ U V : Set S.X, IsOpen U -> IsOpen V -> U.Nonempty -> V.Nonempty -> P U V
  let forwardUnion (U : Set S.X) (first : ℕ) := ⋃ n : ℕ, (S.T^[n + first]) '' U
  let backwardUnion (U : Set S.X) (first : ℕ) := ⋃ n : ℕ, (S.T^[n + first]) ⁻¹' U
  openPairs (fun U V => ∃ n : ℕ, 0 < n ∧ (((S.T^[n]) '' U) ∩ V).Nonempty) ∧
  openPairs (fun U V => ∃ n : ℕ, (((S.T^[n]) '' U) ∩ V).Nonempty) ∧
  openPairs (fun U V => ∃ n : ℕ, 0 < n ∧ (U ∩ (S.T^[n]) ⁻¹' V).Nonempty) ∧
  (∀ U : Set S.X, IsOpen U -> U.Nonempty -> Dense (forwardUnion U 1)) ∧
  (∀ U : Set S.X, IsOpen U -> U.Nonempty -> Dense (forwardUnion U 0)) ∧
  (∀ U : Set S.X, IsOpen U -> U.Nonempty -> Dense (backwardUnion U 1)) ∧
  (∀ U : Set S.X, IsOpen U -> U.Nonempty -> Dense (backwardUnion U 0)) ∧
  (∀ A : Set S.X, IsClosed A -> IsForwardInvariant S A ->
    A = Set.univ ∨ IsNowhereDense A) ∧
  (∀ U : Set S.X, IsOpen U -> IsBackwardInvariant S U -> Dense U ∨ U = ∅) ∧
  (∃ x : S.X, omegaLimitSet S x = Set.univ) ∧
  IsDenseGDelta {x : S.X | omegaLimitSet S x = Set.univ} ∧
  IsDenseGDelta (transitivePointSet S) ∧
  (Function.Surjective S.T ∧ (transitivePointSet S).Nonempty) ∧
  (nonwanderingSet S = Set.univ ∧ (transitivePointSet S).Nonempty) ∧
  (∃ x : S.X, Dense (positiveOrbit S x)) ∧
  openPairs (fun U V => (hittingTimeSet S U V).Infinite) ∧
  (transitivePointSet S).Nonempty


/-- Source: Definition 5.2.1, Chapter 5, Section 2. -/
def fixedPointDefinition (S : System.{u}) (x : S.X) : Prop :=
  fixedPoint S x

/-- Source: Definition 5.2.1, Chapter 5, Section 2. -/
def periodicPointDefinition (S : System.{u}) (x : S.X) : Prop :=
  periodicPoint S x

/--
Source: Definition 5.2.1, Chapter 5, Section 2.
The fixed and periodic point sets of a topological system.
-/
def fixedAndPeriodicPointSets (S : System.{u}) : Set S.X × Set S.X :=
  (fixedPointSet S, periodicPointSet S)

/-- Source: Definition 5.2.2, Chapter 5, Section 2. -/
def omegaLimitSetDefinition (S : System.{u}) (x : S.X) : Set S.X :=
  omegaLimitSet S x

/-- Source: Definition 5.2.2, Chapter 5, Section 2. -/
def returnTimeSetDefinition (S : System.{u}) (U V : Set S.X) : Set ℕ :=
  hittingTimeSet S U V

/-- Source: Definition 5.2.3, Chapter 5, Section 2. -/
def topologicalTransitivity (S : System.{u}) : Prop :=
  IsTopologicallyTransitive S

/-- Source: Definition 5.2.3, Chapter 5, Section 2. -/
def pointTransitivity (S : System.{u}) : Prop :=
  ∃ x : S.X, IsTransitivePoint S x

def reciprocalSequenceSpace : Set ℝ :=
  {x | x = 0 ∨ ∃ n : ℕ, x = 1 / (n + 1 : ℝ)}

def tentMap (x : ℝ) : ℝ :=
  1 - |2 * x - 1|

def tentPeriodicSet : Set ℝ :=
  {x | x ∈ Set.Icc 0 1 ∧ ∃ n : ℕ, 0 < n ∧ (tentMap^[n]) x = x}

/--
Source: Remark 5.2.4, Chapter 5, Section 2.
For general topological spaces, transitivity and point transitivity need not
coincide; under compact metric hypotheses and no isolated points they do.
-/
def transitivityPointTransitivityRemark : Prop :=
  (∃ S : System.{0}, ∃ e : S.X ≃ₜ reciprocalSequenceSpace,
    ∃ origin : S.X, ∃ a : ℕ -> S.X,
      IsTopologicalSystem S ∧
      (e origin : ℝ) = 0 ∧
      (∀ n, (e (a n) : ℝ) = 1 / (n + 1 : ℝ)) ∧
      S.T origin = origin ∧ (∀ n, S.T (a n) = a (n + 1)) ∧
      transitivePointSet S = {a 0} ∧
      pointTransitivity S ∧ ¬ IsTopologicallyTransitive S) ∧
  (∃ S : System.{0}, ∃ e : S.X ≃ₜ tentPeriodicSet,
      IsTopologicalSystem S ∧
      (∀ x : S.X, (e (S.T x) : ℝ) = tentMap (e x : ℝ)) ∧
      IsTopologicallyTransitive S ∧ ¬ pointTransitivity S) ∧
  (∀ S : System.{u}, HasNoIsolatedPoints S ->
    pointTransitivity S -> IsTopologicallyTransitive S) ∧
  (∀ S : System.{u}, HasCountableDenseSubset S -> IsSecondCategorySpace S ->
    Continuous S.T -> IsTopologicallyTransitive S -> pointTransitivity S) ∧
  ∀ S : System.{u}, IsCompactTopologicalSystem S ->
    IsTopologicallyTransitive S -> pointTransitivity S

/--
Source: Theorem 5.2.5, Chapter 5, Section 2.
Equivalent characterizations of topological transitivity, including dense
forward/backward images, existence of full omega-limit points, and dense
transitive points.
-/
theorem topologicalTransitivityEquivalentCharacterizations (S : System.{u}) :
    IsCompactTopologicalSystem S ->
    (IsTopologicallyTransitive S ↔ TransitivityCharacterizations S) ∧
    (IsTopologicallyTransitive S -> (transitivePointSet S).Nonempty) ∧
    ((∀ x : S.X, ¬ IsOpen ({x} : Set S.X)) ->
      (IsTopologicallyTransitive S ↔ (transitivePointSet S).Nonempty)) := by
  sorry

/--
Source: Remark 5.2.6, Chapter 5, Section 2.
The transitive points and full omega-limit points are described as countable
intersections of open dense sets with respect to a countable basis.
-/
def transitivePointsGdeltaFormulaRemark (S : System.{u}) : Prop :=
  IsTopologicalSystem S ->
    ∃ U : ℕ -> Set S.X,
      TopologicalSpace.IsTopologicalBasis (Set.range U) ∧
      transitivePointSet S = ⋂ i : ℕ, ⋃ m : ℕ, (S.T^[m]) ⁻¹' U i ∧
      {x : S.X | omegaLimitSet S x = Set.univ} =
        ⋂ i : ℕ, ⋂ m : ℕ, ⋃ n : ℕ, (S.T^[n + m]) ⁻¹' U i

/--
Source: Theorem 5.2.7, Chapter 5, Section 2.
For a transitive system, transitive points form a dense `G_delta`; factor maps
send transitive points into transitive points, with equality for minimal factor
maps.
-/
theorem transitivePointsUnderFactorMaps
    (S R : System.{u}) (π : S.X -> R.X) :
    IsCompactTopologicalSystem S -> IsCompactTopologicalSystem R ->
    IsFactorMap S R π ->
      (IsTopologicallyTransitive S -> IsDenseGDelta (transitivePointSet S)) ∧
      (IsTopologicallyTransitive S -> IsTopologicallyTransitive R) ∧
      transitivePointSet S ⊆ π ⁻¹' transitivePointSet R ∧
      (IsMinimalFactorMap S R π ->
        transitivePointSet S = π ⁻¹' transitivePointSet R) := by
  sorry

/--
Source: Theorem 5.2.8, Chapter 5, Section 2.
A topologically transitive system has no nonconstant continuous invariant
functions.
-/
theorem transitiveSystemHasNoNonconstantContinuousInvariantFunctions
    (S : System.{u}) :
    IsTopologicallyTransitive S -> HasNoNonconstantContinuousInvariantFunctions S := by
  sorry

/-- The `n`-torus, represented as a finite product of additive circles. -/
abbrev Torus (n : ℕ) := Fin n -> AddCircle (1 : ℝ)

/-- A continuous additive automorphism of a finite-dimensional torus. -/
structure ToralAutomorphism (n : ℕ) where
  toEquiv : Torus n ≃ Torus n
  continuous_toFun : Continuous toEquiv
  continuous_invFun : Continuous toEquiv.symm
  map_add : ∀ x y, toEquiv (x + y) = toEquiv x + toEquiv y

def ToralAutomorphism.toSystem {n : ℕ} (A : ToralAutomorphism n) : System where
  X := Torus n
  topology := inferInstance
  T := A.toEquiv

/-- A system obtained by gluing two copies of `𝕋²` at their identity and
letting the same toral automorphism act on both copies. -/
def IsTwoTorusWedgeSystem (S : System.{u}) (A : ToralAutomorphism 2) : Prop :=
  ∃ ι : Fin 2 -> Torus 2 -> S.X,
    (∀ i, Continuous (ι i) ∧ Function.Injective (ι i) ∧
      IsClosed (Set.range (ι i))) ∧
    Set.range (ι 0) ∪ Set.range (ι 1) = Set.univ ∧
    (∀ x y, ι 0 x = ι 1 y ↔ x = 0 ∧ y = 0) ∧
    ∀ i x, S.T (ι i x) = ι i (A.toEquiv x)

/--
Source: Example 5.2.9, Chapter 5, Section 2.
There exists a nontransitive system with no nonconstant continuous invariant
functions.
-/
theorem noNonconstantInvariantFunctionsDoesNotImplyTransitiveExample :
    ∃ A : ToralAutomorphism 2,
    ∃ μ : MeasureTheory.Measure (Torus 2),
      MeasureTheory.IsProbabilityMeasure μ ∧
      (∀ a : Torus 2, ∀ B : Set (Torus 2), MeasurableSet B ->
        μ ((fun x => a + x) ⁻¹' B) = μ B) ∧
      Chapter02.IsErgodic
        { X := Torus 2, measurableSpace := inferInstance, μ := μ, T := A.toEquiv } ∧
      ∃ S : System.{0}, IsTwoTorusWedgeSystem S A ∧
        HasNoNonconstantContinuousInvariantFunctions S ∧
        ¬ IsTopologicallyTransitive S := by
  sorry

/-- Source: Definition 5.2.10, Chapter 5, Section 2. -/
def recurrentPointDefinition (S : System.{u}) (x : S.X) : Prop :=
  recurrentPoint S x

/--
Source: Definition 5.2.10, Chapter 5, Section 2.
A recurrent point has transitive orbit closure, and every transitive point in a
transitive system is recurrent.
-/
theorem recurrentPointOrbitClosureIsTransitive (S : System.{u}) (x : S.X) :
    IsCompactTopologicalSystem S -> recurrentPoint S x ->
      IsTopologicallyTransitiveOn S (orbitClosure S x) := by
  sorry

/--
Source: Theorem 5.2.11, Chapter 5, Section 2.
Birkhoff recurrence theorem: every topological dynamical system has a recurrent
point; periodic points are recurrent.
-/
theorem birkhoffRecurrenceTheorem (S : System.{u}) :
    IsCompactTopologicalSystem S -> (Set.univ : Set S.X).Nonempty ->
      (∃ x : S.X, recurrentPoint S x) ∧ periodicPointSet S ⊆ recurrentPointSet S := by
  sorry

/--
Source: Theorem 5.2.12, Chapter 5, Section 2.
The recurrent set is invariant, unchanged by positive iterates, and maps onto
recurrent sets under factor maps.
-/
theorem recurrentPointSetBasicProperties
    (S R : System.{u}) (π : S.X -> R.X) :
    IsFactorMap S R π ->
      S.T '' recurrentPointSet S = recurrentPointSet S ∧
        (∀ n : ℕ, 0 < n -> recurrentPointSet { S with T := S.T^[n] } = recurrentPointSet S) ∧
          π '' recurrentPointSet S = recurrentPointSet R := by
  sorry

/--
Source: Theorem 5.2.13, Chapter 5, Section 2.
For a transitive system and an iterate `T^n`, the space decomposes cyclically
into transitive components for the iterate.
-/
theorem transitiveSystemIterateCyclicDecomposition (S : System.{u}) (n : ℕ) :
    IsCompactTopologicalSystem S -> IsTopologicallyTransitive S -> 0 < n ->
      ∃ k : ℕ, ∃ Xpart : Fin k -> Set S.X,
        IsTransitiveCyclicDecomposition S n k Xpart := by
  sorry

/--
Source: Proposition 5.2.14, Chapter 5, Section 2.
The full shift is transitive and its periodic points are dense.
-/
theorem fullShiftTransitiveWithDensePeriodicPoints (S : System.{u}) (k : ℕ) :
    IsFullShift S k -> IsTopologicallyTransitive S ∧ Dense (periodicPointSet S) := by
  sorry

/--
Source: Proposition 5.2.15, Chapter 5, Section 2.
A point in the full shift is recurrent exactly when every word appearing in it
appears infinitely often.
-/
theorem fullShiftRecurrentIffWordsAppearInfinitelyOften
    (S : System.{u}) (k : ℕ) (x : S.X) :
    IsFullShift S k ->
      (recurrentPoint S x ↔ ∀ U : Set S.X, IsOpen U -> x ∈ U -> Set.Infinite (pointHittingTimeSet S x U)) := by
  sorry

/--
Source: Example 5.2.16, Chapter 5, Section 2.
There exists a recurrent point in a shift system which is not periodic.
-/
theorem nonperiodicRecurrentShiftPointExample :
    ∃ S : System.{0}, ∃ x : S.X, recurrentPoint S x ∧ ¬ periodicPoint S x := by
  sorry

/-- Points of the torus whose coordinates have rational representatives. -/
def rationalTorusPoints (n : ℕ) : Set (Torus n) :=
  {x | ∀ j, ∃ q : ℚ, x j = (q : ℝ)}

/-- A normalized translation-invariant probability measure on the torus. -/
def IsNormalizedTorusHaarMeasure {n : ℕ}
    (μ : MeasureTheory.Measure (Torus n)) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧
  ∀ a : Torus n, ∀ B : Set (Torus n), MeasurableSet B ->
    μ ((fun x => a + x) ⁻¹' B) = μ B

/-- Source: Theorem 5.2.17.  Ergodicity is with respect to normalized Haar
measure.  Without ergodicity, every rational torus point is still periodic. -/
theorem toralAutomorphismPeriodicPointsDenseExample
    (n : ℕ) (A : ToralAutomorphism n) (μ : MeasureTheory.Measure (Torus n)) :
    IsNormalizedTorusHaarMeasure μ ->
    let S := A.toSystem
    let M : Chapter02.System :=
      { X := Torus n, measurableSpace := inferInstance, μ := μ, T := A.toEquiv }
    (Chapter02.IsErgodic M ->
      IsTopologicallyTransitive S ∧ periodicPointSet S = rationalTorusPoints n) ∧
    rationalTorusPoints n ⊆ periodicPointSet S ∧ Dense (rationalTorusPoints n) := by
  sorry

/--
Source: Theorem 5.2.18, Chapter 5, Section 2.
Return times of recurrent points contain IP sets; conversely every IP set occurs
as a return-time container for a transitive point in a suitable system.
-/
theorem recurrentReturnTimesAndIpSets :
    (∀ (S : System.{u}) (x : S.X), recurrentPoint S x ->
      ∀ U : Set S.X, IsOpen U -> x ∈ U ->
        ∃ R : Set ℕ, IsIpSet R ∧ R ⊆ pointHittingTimeSet S x U) ∧
    (∀ R : Set ℕ, IsIpSet R ->
      ∃ X : Type u, ∃ _ : MetricSpace X, ∃ T : X -> X, ∃ x₀ : X,
        let S : System.{u} := { X := X, topology := inferInstance, T := T }
        IsCompactTopologicalSystem S ∧ IsTopologicallyTransitive S ∧
        IsTransitivePoint S x₀ ∧
        pointHittingTimeSet S x₀ (Metric.ball x₀ 1) ⊆ R ∪ {0}) := by
  sorry

/-- Source: Definition 5.2.19, Chapter 5, Section 2. -/
def ramseyProperty (𝓕 : Set (Set ℕ)) : Prop :=
  HasRamseyProperty 𝓕

/--
Source: Theorem 5.2.20, Chapter 5, Section 2.
Hindman's theorem: the family of IP sets has the Ramsey property.
-/
theorem hindmanTheoremIpSetsRamsey :
    HasRamseyProperty {A : Set ℕ | IsIpSet A} := by
  sorry

end Section02
end Chapter05
