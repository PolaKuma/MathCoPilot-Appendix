import Chapter05.Section02

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

namespace Section03


/-- Source: Definition 5.3.1, Chapter 5, Section 3. -/
def minimalSystem (S : System.{u}) : Prop :=
  IsMinimalSystem S

/-- Source: Definition 5.3.1, Chapter 5, Section 3. -/
def minimalSet (S : System.{u}) (M : Set S.X) : Prop :=
  IsMinimalSet S M

/--
Source: Theorem 5.3.2, Chapter 5, Section 3.
A system is minimal iff every orbit is dense iff finitely many inverse images of
each nonempty open set cover the space.
-/
theorem minimalSystemEquivalentCharacterizations (S : System.{u}) :
    IsCompactTopologicalSystem S -> (Set.univ : Set S.X).Nonempty ->
    (IsMinimalSystem S ↔
      ((∀ x : S.X, orbitClosure S x = Set.univ) ∧
        ∀ U : Set S.X, IsOpen U -> U.Nonempty ->
          ∃ A : Finset ℕ, Set.univ = ⋃ n ∈ (A : Set ℕ), (S.T^[n]) ⁻¹' U)) := by
  sorry

/--
Source: Remark 5.3.3, Chapter 5, Section 3.
On a minimal homeomorphism, continuous invariant functions are constant, and
minimal points are recurrent.
-/
def minimalInvariantFunctionAndRecurrenceRemark (S : System.{u}) : Prop :=
  IsCompactTopologicalSystem S -> IsMinimalSystem S ->
    HasNoNonconstantContinuousInvariantFunctions S ∧
    recurrentPointSet S = Set.univ

/--
Source: Theorem 5.3.4, Chapter 5, Section 3.
Every topological dynamical system has a minimal set.
-/
theorem everyTopologicalSystemHasMinimalSet (S : System.{u}) :
    IsCompactTopologicalSystem S -> (Set.univ : Set S.X).Nonempty ->
      ∃ M : Set S.X, IsMinimalSet S M := by
  sorry

/--
Source: Remark 5.3.5, Chapter 5, Section 3.
Syndetic and thick sets are dual in the sense that each syndetic set meets every
thick set and conversely.
-/
def syndeticThickDualityRemark : Prop :=
  (∀ A : Set ℕ, IsSyndetic A ↔ ∀ B : Set ℕ, IsThick B -> (A ∩ B).Nonempty) ∧
    ∀ A : Set ℕ, IsThick A ↔ ∀ B : Set ℕ, IsSyndetic B -> (A ∩ B).Nonempty

/-- Source: Definition 5.3.6, Chapter 5, Section 3. -/
def almostPeriodicPointDefinition (S : System.{u}) (x : S.X) : Prop :=
  almostPeriodicPoint S x

/--
Source: Theorem 5.3.7, Chapter 5, Section 3.
Almost periodic points have minimal orbit closures; minimal sets consist of
almost periodic points; minimality passes to factors, and minimal factors are
semi-open.
-/
theorem almostPeriodicPointsAndMinimalFactors
    (S R : System.{u}) (π : S.X -> R.X) :
    IsFactorMap S R π ->
      (∀ x : S.X, almostPeriodicPoint S x -> IsMinimalSet S (orbitClosure S x)) ∧
      (∀ M : Set S.X, IsMinimalSet S M -> M ⊆ almostPeriodicPointSet S) ∧
      (IsMinimalSystem S -> IsMinimalSystem R) ∧
      (IsMinimalSystem S -> IsSemiOpenFactorMap S R π) := by
  sorry

/--
Source: Remark 5.3.8, Chapter 5, Section 3.
For compact systems, minimal points and almost periodic points are the same.
-/
def minimalPointsAlmostPeriodicRemark (S : System.{u}) : Prop :=
  IsCompactTopologicalSystem S ->
    almostPeriodicPointSet S = {x : S.X | ∃ M : Set S.X, x ∈ M ∧ IsMinimalSet S M}

/--
Source: Theorem 5.3.9, Chapter 5, Section 3.
The almost-periodic set is invariant, unchanged by positive iterates, and maps
onto the almost-periodic set of every factor.
-/
theorem almostPeriodicPointSetBasicProperties
    (S R : System.{u}) (π : S.X -> R.X) :
    IsFactorMap S R π ->
      S.T '' almostPeriodicPointSet S = almostPeriodicPointSet S ∧
        (∀ n : ℕ, 0 < n -> almostPeriodicPointSet { S with T := S.T^[n] } = almostPeriodicPointSet S) ∧
          π '' almostPeriodicPointSet S = almostPeriodicPointSet R := by
  sorry

/--
Source: Example 5.3.10, Chapter 5, Section 3.
Irrational circle rotations, adding machines, and transitive Kronecker systems
are minimal, and compact group rotations have all points almost periodic.
-/
theorem compactGroupRotationAlmostPeriodicExample :
    (∀ α : ℝ, Irrational α ->
      IsMinimalSystem (circleRotationTopologicalSystem α)) ∧
    IsMinimalSystem addingMachineTopologicalSystem ∧
    (∀ (G : Type u) [AddCommGroup G] [TopologicalSpace G]
      [IsTopologicalAddGroup G] [CompactSpace G],
      TopologicalSpace.MetrizableSpace G -> ∀ g₀ : G,
        let S := compactGroupRotationTopologicalSystem G g₀
        almostPeriodicPointSet S = Set.univ ∧
          (IsTopologicallyTransitive S -> IsMinimalSystem S)) := by
  sorry

/--
Source: Proposition 5.3.11, Chapter 5, Section 3.
In the full shift, a point is almost periodic iff each word appearing in it
appears syndetically.
-/
theorem fullShiftAlmostPeriodicIffWordsOccurSyndetically
    (S : System.{u}) (k : ℕ) (x : S.X) :
    ∀ e : S.X ≃ₜ (ℤ -> Fin k),
      (∀ y : S.X, ∀ n : ℤ, e (S.T y) n = e y (n + 1)) ->
      (almostPeriodicPoint S x ↔ WordOccursSyndetically (e x)) := by
  sorry

/--
Source: Example 5.3.12, Chapter 5, Section 3.
Primitive substitution systems, including the Morse substitution system, give
minimal symbolic systems.
-/
theorem substitutionSystemsAreMinimalExamples :
    ∀ σ : Substitution Bool, IsPrimitiveSubstitution σ ->
      ∃ S : System.{0}, IsSubstitutionSystem S σ ∧
        IsMinimalSystem S ∧ IsMSystem S := by
  sorry

/--
Source: Example 5.3.13, Chapter 5, Section 3.
The recursive Morse word construction agrees with the substitution construction
of the Morse minimal system.
-/
theorem morseWordConstructionsAgreeExample :
    ∃ S : System.{0}, IsSubstitutionSystem S morseSubstitution ∧
      IsGeneratedByWordTower S morseWords ∧ IsMinimalSystem S := by
  sorry

/--
Source: Example 5.3.14, Chapter 5, Section 3.
The Chacon construction yields a minimal symbolic system.
-/
theorem chaconSystemMinimalExample :
    ∃ S : System.{0}, IsGeneratedByWordTower S chaconWords ∧ IsMinimalSystem S := by
  sorry

/--
Source: Example 5.3.15, Chapter 5, Section 3.
Toeplitz systems are minimal and are characterized as almost one-to-one
extensions of adding machines among subshifts.
-/
theorem toeplitzSystemsMinimalAndAddingMachineExtensionsExample :
    ∃ S A : System.{0}, IsToeplitzSystem (A := Bool) S ∧ IsMinimalSystem S ∧
      IsCompactGroupRotationModel A ∧
      ∃ π : S.X -> A.X, IsFactorMap S A π ∧
        Dense {y : A.X | ∃! x : S.X, π x = y} := by
  sorry

/--
Source: Example 5.3.16, Chapter 5, Section 3.
Sturmian systems obtained from irrational circle rotations are minimal.
-/
theorem sturmianSystemMinimalExample :
    ∀ α : ℝ, Irrational α ->
      ∃ S : System.{0}, IsSturmianSystem S α ∧ IsMinimalSystem S := by
  sorry

/-- Source: Definition 5.3.17, Chapter 5, Section 3. -/
def pSystem (S : System.{u}) : Prop :=
  IsPSystem S

/-- Source: Definition 5.3.17, Chapter 5, Section 3. -/
def mSystem (S : System.{u}) : Prop :=
  IsMSystem S

/--
Source: Remark 5.3.18, Chapter 5, Section 3.
Every P-system is an M-system, full shifts are P-systems, and minimal
nonperiodic systems are M-systems but not P-systems.
-/
def pSystemMSystemExamplesRemark : Prop :=
  (∀ S : System.{u}, IsPSystem S -> IsMSystem S) ∧
  (∀ k : ℕ, ∀ S : System.{u}, IsFullShift S k -> IsPSystem S) ∧
  (∀ S : System.{u}, IsMinimalSystem S ->
    ¬ Set.Finite (Set.univ : Set S.X) -> IsMSystem S ∧ ¬ IsPSystem S) ∧
  ∃ S : System.{0}, IsTopologicallyTransitive S ∧
    ∃ z : S.X, fixedPoint S z ∧
      ∀ M : Set S.X, IsMinimalSet S M ↔ M = {z}

/-- Source: Definition 5.3.19, Chapter 5, Section 3. -/
def piecewiseSyndeticSet (A : Set ℕ) : Prop :=
  IsPiecewiseSyndetic A

/-- Source: Definition 5.3.19, Chapter 5, Section 3. -/
def thicklySyndeticSet (A : Set ℕ) : Prop :=
  IsThicklySyndetic A

/--
Source: Theorem 5.3.20, Chapter 5, Section 3.
For a transitive point, M-systems and uniqueness of minimal sets are detected by
piecewise syndetic and thickly syndetic return times.
-/
theorem mSystemsAndUniqueMinimalSetsViaReturnTimes
    (S : System.{u}) (x : S.X) :
    IsTransitivePoint S x ->
      (IsMSystem S ↔ ∀ U : Set S.X, IsOpen U -> x ∈ U -> IsPiecewiseSyndetic (pointHittingTimeSet S x U)) ∧
      (∀ K : Set S.X, IsMinimalSet S K ->
        ((∀ M : Set S.X, IsMinimalSet S M -> M = K) ↔
          ∀ U : Set S.X, IsOpen U -> K ⊆ U -> IsThicklySyndetic (pointHittingTimeSet S x U))) := by
  sorry

/--
Source: Theorem 5.3.21, Chapter 5, Section 3.
In every finite partition of the natural numbers, at least one cell is piecewise
syndetic.
-/
theorem finitePartitionHasPiecewiseSyndeticCell (q : ℕ) (B : Fin q -> Set ℕ) :
    0 < q -> (⋃ j : Fin q, B j) = Set.univ ->
      (∀ i j, i ≠ j -> Disjoint (B i) (B j)) ->
      ∃ j : Fin q, IsPiecewiseSyndetic (B j) := by
  sorry

/--
Source: Lemma 5.3.22, Chapter 5, Section 3.
For a minimal system and an integer `m`, the space decomposes into finitely many
cyclic components for `T^m`, each minimal for the iterate.
-/
theorem minimalSystemIterateCyclicDecomposition (S : System.{u}) (m : ℕ) :
    IsCompactTopologicalSystem S -> IsMinimalSystem S -> 0 < m ->
      ∃ l : ℕ, ∃ Xpart : Fin l -> Set S.X,
        IsMinimalCyclicDecomposition S m l Xpart := by
  sorry

/-- Source: Definition 5.3.23, Chapter 5, Section 3. -/
def recurrenceSet (A : Set ℕ) : Prop :=
  IsRecurrenceSet.{u} A

/--
Source: Theorem 5.3.24, Chapter 5, Section 3.
A set is a recurrence set iff it meets the difference set of every syndetic set.
-/
theorem recurrenceSetIffMeetsSyndeticDifferences (A : Set ℕ) :
    IsRecurrenceSet A ↔ ∀ S : Set ℕ, IsSyndetic S -> ((fun n : ℕ => (n : ℤ)) '' A ∩ differenceSet S).Nonempty := by
  sorry

/--
Source: Theorem 5.3.25, Chapter 5, Section 3.
A set is a recurrence set iff it produces a return time in every nonempty open
set of every minimal system.
-/
theorem recurrenceSetIffMinimalOpenReturn (A : Set ℕ) :
    IsRecurrenceSet A ↔ ∀ S : System.{u}, IsCompactTopologicalSystem S ->
      IsMinimalSystem S -> ∀ U : Set S.X, IsOpen U -> U.Nonempty ->
      ∃ n ∈ A, 0 < n ∧ (U ∩ (S.T^[n]) ⁻¹' U).Nonempty := by
  sorry

/--
Source: Theorem 5.3.26, Chapter 5, Section 3.
If a transitive topological system is not minimal, then the complement of its
transitive points is dense.
-/
theorem nonminimalTransitiveSystemHasDenseNontransitivePoints (S : System.{u}) :
    IsCompactTopologicalSystem S -> IsTopologicallyTransitive S ->
      ¬ IsMinimalSystem S -> Dense ((transitivePointSet S)ᶜ) := by
  sorry

/--
Source: Remark 5.3.27, Chapter 5, Section 3.
Two-sided and one-sided point transitivity can differ, while two-sided and
one-sided minimality coincide for the systems under discussion.
-/
def oneSidedTwoSidedTransitivityRemark : Prop :=
  (∃ S : System.{0}, IsTopologicalSystem S ∧
    ∃ inv : S.X -> S.X, IsContinuousInverse S inv ∧
    ∃ x : S.X, IsTwoSidedTransitivePoint S inv x ∧
      ¬ IsTransitivePoint S x ∧
      ∃ p q : S.X, p ≠ q ∧ nonwanderingSet S = {p, q}) ∧
  ∀ S : System.{u}, IsTopologicalSystem S -> ∀ inv : S.X -> S.X,
    IsContinuousInverse S inv ->
      (IsTwoSidedMinimalSystem S inv ↔ IsMinimalSystem S)

end Section03
end Chapter05
