import Chapter05.Section04

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

namespace Section05

/-- Nonwandering points of the subsystem supported on `A`, expressed in the
ambient space so that no hidden subtype invariance proof is needed. -/
def nonwanderingWithin (S : System.{u}) (A : Set S.X) : Set S.X :=
  {x : S.X | x ∈ A ∧ ∀ U : Set S.X, IsOpen U -> x ∈ U ->
    ∃ n : ℕ, 0 < n ∧
      ((U ∩ A) ∩ (S.T^[n]) ⁻¹' (U ∩ A)).Nonempty}

def omegaDepthSet (S : System.{u}) (n : ℕ) : Set S.X :=
  Nat.iterate (nonwanderingWithin S) n Set.univ

/-- The transfinite nonwandering derivative used in Theorem 5.5.8. -/
structure NonwanderingDerivativeTower (S : System.{u}) where
  stage : Ordinal -> Set S.X
  zero_stage : stage 0 = Set.univ
  successor_stage : ∀ α : Ordinal,
    stage (α + 1) = nonwanderingWithin S (stage α)
  limit_stage : ∀ limitOrd : Ordinal,
    limitOrd ≠ 0 -> (∀ α : Ordinal, α < limitOrd -> α + 1 < limitOrd) ->
    stage limitOrd = ⋂ α : { α : Ordinal // α < limitOrd }, stage α.1

def IsCenterDepth (S : System.{u}) (D : NonwanderingDerivativeTower S)
    (θ : Ordinal) : Prop :=
  D.stage (θ + 1) = D.stage θ ∧
    ∀ α : Ordinal, α < θ -> D.stage (α + 1) ≠ D.stage α

def transfiniteNonwanderingCenter (S : System.{u}) (D : NonwanderingDerivativeTower S)
    (θ : Ordinal) : Set S.X :=
  D.stage θ

def BirkhoffCenter (S : System.{u}) : Set S.X :=
  closure (recurrentPointSet S)

def IsCentralSystem (S : System.{u}) : Prop :=
  nonwanderingSet S = Set.univ

def chainRecurrentPoint (S : System.{u}) [PseudoMetricSpace S.X] (x : S.X) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ p : ℕ -> S.X, ∃ n : ℕ,
    0 < n ∧ p 0 = x ∧ p n = x ∧ ∀ i : ℕ, i < n ->
      dist (S.T (p i)) (p (i + 1)) < ε


/-- Source: Definition 5.5.1, Chapter 5, Section 5. -/
def omegaLimitOfSystem (S : System.{u}) : Set S.X :=
  totalOmegaLimitSet S

/--
Source: Definition 5.5.1, Chapter 5, Section 5.
A recurrent point is exactly a point lying in its own omega-limit set, although
omega-limit points need not be recurrent.
-/
def recurrentPointOmegaCharacterizationRemark (S : System.{u}) : Prop :=
  ∀ x : S.X, recurrentPoint S x ↔ x ∈ omegaLimitSet S x

/--
Source: Theorem 5.5.2, Chapter 5, Section 5.
Omega-limit sets are nonempty and invariant; total omega-limits are invariant,
compatible with iterates, and contain recurrent points.
-/
theorem omegaLimitSetBasicProperties (S : System.{u}) (x : S.X) :
    IsCompactTopologicalSystem S -> (Set.univ : Set S.X).Nonempty ->
    (omegaLimitSet S x).Nonempty ∧ IsClosed (omegaLimitSet S x) ∧
    S.T '' omegaLimitSet S x = omegaLimitSet S x ∧
    S.T '' totalOmegaLimitSet S = totalOmegaLimitSet S ∧
    (∀ i : ℕ, ∀ n : ℕ, 0 < n ->
      let Sn : System.{u} := { S with T := S.T^[n] }
      S.T '' omegaLimitSet Sn ((S.T^[i]) x) =
        omegaLimitSet Sn ((S.T^[i + 1]) x)) ∧
    (∀ n : ℕ, 0 < n ->
      let Sn : System.{u} := { S with T := S.T^[n] }
      omegaLimitSet S x = ⋃ i : Fin n, omegaLimitSet Sn ((S.T^[i.1]) x)) ∧
    (∀ n : ℕ, 0 < n ->
      totalOmegaLimitSet S = totalOmegaLimitSet { S with T := S.T^[n] }) ∧
    recurrentPointSet S ⊆ totalOmegaLimitSet S := by
  sorry

/--
Source: Remark 5.5.3, Chapter 5, Section 5.
For homeomorphisms, alpha-limit sets are omega-limit sets for the inverse map,
and the total omega-limit set need not be closed.
-/
def alphaLimitAndNonclosedOmegaRemark : Prop :=
  (∀ S : System.{u}, ∀ inv : S.X -> S.X, IsContinuousInverse S inv ->
    ∀ x : S.X, alphaLimitSet S inv x = omegaLimitSet { S with T := inv } x) ∧
  ∃ S : System.{0}, IsCompactTopologicalSystem S ∧
    ¬ IsClosed (totalOmegaLimitSet S)

/--
Source: Theorem 5.5.4, Chapter 5, Section 5.
If an omega-limit set contains an isolated periodic point, then the omega-limit
set is that periodic orbit; in particular every finite omega-limit set is a
periodic orbit.
-/
theorem isolatedPeriodicPointInOmegaLimitForcesPeriodicOrbit
    (S : System.{u}) (x p : S.X) :
    p ∈ omegaLimitSet S x -> periodicPoint S p ->
      IsOpen ({p} : Set S.X) -> ∃ n : ℕ, 0 < n ∧ omegaLimitSet S x = orbit S p := by
  sorry

/-- Source: Definition 5.5.5, Chapter 5, Section 5. -/
def nonwanderingPointDefinition (S : System.{u}) (x : S.X) : Prop :=
  nonwanderingPoint S x

/-- Source: Definition 5.5.5, Chapter 5, Section 5. -/
def nonwanderingPointSetDefinition (S : System.{u}) : Set S.X :=
  nonwanderingSet S

/--
Source: Theorem 5.5.6, Chapter 5, Section 5.
The nonwandering set is closed, contains the closure of the total omega-limit
set, and is forward invariant.
-/
theorem nonwanderingSetBasicProperties (S : System.{u}) :
    IsCompactTopologicalSystem S -> (Set.univ : Set S.X).Nonempty ->
    IsClosed (nonwanderingSet S) ∧ (nonwanderingSet S).Nonempty ∧
      closure (totalOmegaLimitSet S) ⊆ nonwanderingSet S ∧
      S.T '' nonwanderingSet S ⊆ nonwanderingSet S := by
  sorry

/--
Source: Theorem 5.5.7, Chapter 5, Section 5.
If every point is nonwandering, then recurrent points form a dense `G_delta`.
-/
theorem recurrentPointsDenseGdeltaWhenAllNonwandering (S : System.{u}) :
    IsCompactTopologicalSystem S -> nonwanderingSet S = Set.univ ->
      IsDenseGDelta (recurrentPointSet S) := by
  sorry

/--
Source: Theorem 5.5.8, Chapter 5, Section 5.
The transfinite nonwandering core is nonempty; for metric systems the center
depth is countable, the core is nonwandering, and its closure of recurrent
points is the Birkhoff center.
-/
theorem birkhoffCenterAndOmegaDepthProperties (S : System.{u}) :
    IsCompactTopologicalSystem S -> (Set.univ : Set S.X).Nonempty ->
    ∃ D : NonwanderingDerivativeTower S, ∃ θ : Ordinal,
      IsCenterDepth S D θ ∧
      (transfiniteNonwanderingCenter S D θ).Nonempty ∧
      Set.Countable (Set.Iio θ) ∧
      nonwanderingWithin S (transfiniteNonwanderingCenter S D θ) =
        transfiniteNonwanderingCenter S D θ ∧
      BirkhoffCenter S = transfiniteNonwanderingCenter S D θ := by
  sorry

/-- Polar-coordinate quotient model of the closed unit disk.  The second
coordinate is measured in turns, so angles differing by an integer agree;
all angles agree at radius zero. -/
def IsPolarDiskCoordinateModel (S : System.{u})
    (polar : Set.Icc (0 : ℝ) 1 × ℝ -> S.X) : Prop :=
  Continuous polar ∧ Function.Surjective polar ∧
  (∀ p q, polar p = polar q ↔
    (p.1 : ℝ) = (q.1 : ℝ) ∧
      ((p.1 : ℝ) = 0 ∨ ∃ k : ℤ, p.2 - q.2 = k)) ∧
  (∃ inv : S.X -> S.X, IsContinuousInverse S inv) ∧
  ∀ r : Set.Icc (0 : ℝ) 1, ∀ θ : ℝ,
    ∃ r' : Set.Icc (0 : ℝ) 1,
      (r' : ℝ) = Real.sqrt (r : ℝ) ∧
      S.T (polar (r, θ)) =
        polar (r', θ / 2 + 1 - (r : ℝ))

/--
Source: Example 5.5.9, Chapter 5, Section 5.
There are systems where the second nonwandering core is strictly smaller than
the nonwandering set.
-/
theorem secondNonwanderingCoreCanBeProperExample :
    ∃ S : System.{0},
    ∃ polar : Set.Icc (0 : ℝ) 1 × ℝ -> S.X,
      IsTopologicalSystem S ∧ IsPolarDiskCoordinateModel S polar ∧
      nonwanderingSet S =
        {polar (⟨0, ⟨le_rfl, zero_le_one⟩⟩, 0)} ∪
          {x | ∃ θ : ℝ, x = polar (⟨1, ⟨zero_le_one, le_rfl⟩⟩, θ)} ∧
      omegaDepthSet S 2 =
        {polar (⟨0, ⟨le_rfl, zero_le_one⟩⟩, 0),
          polar (⟨1, ⟨zero_le_one, le_rfl⟩⟩, 0)} ∧
      omegaDepthSet S 2 ≠ nonwanderingSet S := by
  sorry

/-- Source: Definition 5.5.10, Chapter 5, Section 5. -/
def chainRecurrentPointDefinition (S : System.{u}) [PseudoMetricSpace S.X] (x : S.X) : Prop :=
  (∃ inv : S.X -> S.X, IsContinuousInverse S inv) ∧ chainRecurrentPoint S x

/--
Source: Definition 5.5.10, Chapter 5, Section 5.
The fixed, periodic, almost-periodic, recurrent, nonwandering, and chain
recurrent point sets form the standard inclusion chain.
-/
theorem recurrenceInclusionChain (S : System.{u}) [PseudoMetricSpace S.X] :
    IsCompactTopologicalSystem S ->
    (∃ inv : S.X -> S.X, IsContinuousInverse S inv) ->
    fixedPointSet S ⊆ periodicPointSet S ∧ periodicPointSet S ⊆ almostPeriodicPointSet S ∧
      almostPeriodicPointSet S ⊆ recurrentPointSet S ∧ recurrentPointSet S ⊆ nonwanderingSet S ∧
        nonwanderingSet S ⊆ {x : S.X | chainRecurrentPoint S x} := by
  sorry

end Section05
end Chapter05
