import Chapter04.Section06

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

abbrev SetFamily (X : Type u) := Chapter00.SetFamily X

structure TopologicalSystemData where
  X : Type u
  topology : TopologicalSpace X
  T : X -> X

attribute [instance] TopologicalSystemData.topology

abbrev System := TopologicalSystemData

def IsTopologicalSystem (S : System.{u}) : Prop :=
  Continuous S.T ∧ IsCompact (Set.univ : Set S.X) ∧
    TopologicalSpace.MetrizableSpace S.X ∧ (Set.univ : Set S.X).Nonempty

/-- The standing convention of Chapter 5: a topological dynamical system has
compact underlying space and continuous time-one map.  Metrizability is carried
by a typeclass in the statements that use a metric. -/
def IsCompactTopologicalSystem (S : System.{u}) : Prop :=
  IsTopologicalSystem S

def IsFactorMap (S₁ : System.{u}) (S₂ : System.{v}) (π : S₁.X -> S₂.X) : Prop :=
  IsTopologicalSystem S₁ ∧ IsTopologicalSystem S₂ ∧
    Continuous π ∧ Function.Surjective π ∧
      ∀ x : S₁.X, π (S₁.T x) = S₂.T (π x)

def IsTopologicallyConjugate (S₁ : System.{u}) (S₂ : System.{v}) : Prop :=
  ∃ φ : S₁.X -> S₂.X, ∃ ψ : S₂.X -> S₁.X,
    IsFactorMap S₁ S₂ φ ∧ IsFactorMap S₂ S₁ ψ ∧
      Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ

/-- A minimal factor map in the sense used immediately before Theorem 5.2.7. -/
def IsMinimalFactorMap (S₁ : System.{u}) (S₂ : System.{v})
    (π : S₁.X -> S₂.X) : Prop :=
  IsFactorMap S₁ S₂ π ∧
    ∀ A : Set S₁.X, A.Nonempty -> IsClosed A -> S₁.T '' A ⊆ A ->
      π '' A = Set.univ -> A = Set.univ

def IsClosedInvariantEquivalence {X : Type u} [TopologicalSpace X]
    (T : X -> X) (R : X -> X -> Prop) : Prop :=
  Equivalence R ∧ IsClosed {p : X × X | R p.1 p.2} ∧
    ∀ x y : X, R x y -> R (T x) (T y)

/-- The equivalence relation on the source induced by a factor map. -/
def factorKernel (S₁ : System.{u}) (S₂ : System.{v}) (π : S₁.X -> S₂.X) :
    S₁.X -> S₁.X -> Prop :=
  fun x y => π x = π y

def eventualImage (S : System.{u}) : Set S.X :=
  ⋂ n : ℕ, (S.T^[n]) '' Set.univ

def IsNaturalExtension (S : System.{u}) (E : System.{v}) (π : E.X -> S.X) : Prop :=
  IsFactorMap E S π ∧
  ∃ inv : E.X -> E.X,
    Continuous inv ∧ Function.LeftInverse inv E.T ∧ Function.RightInverse inv E.T ∧
  ∃ code : E.X -> (ℕ -> S.X),
    Continuous code ∧ Function.Injective code ∧
    (∀ x n, S.T (code x (n + 1)) = code x n) ∧
    (∀ a : ℕ -> S.X, (∀ n, S.T (a (n + 1)) = a n) -> ∃ x, code x = a) ∧
    (∀ x, π x = code x 0) ∧
    ∀ x n, code (inv x) n = code x (n + 1)

def orbit (S : System.{u}) (x : S.X) : Set S.X :=
  {y : S.X | ∃ n : ℕ, (S.T^[n]) x = y}

def orbitClosure (S : System.{u}) (x : S.X) : Set S.X :=
  closure (orbit S x)

def positiveOrbit (S : System.{u}) (x : S.X) : Set S.X :=
  {y : S.X | ∃ n : ℕ, 0 < n ∧ (S.T^[n]) x = y}

def IsForwardInvariant (S : System.{u}) (A : Set S.X) : Prop :=
  S.T '' A ⊆ A

def IsBackwardInvariant (S : System.{u}) (A : Set S.X) : Prop :=
  S.T ⁻¹' A ⊆ A

def fixedPoint (S : System.{u}) (x : S.X) : Prop :=
  S.T x = x

def periodicPoint (S : System.{u}) (x : S.X) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (S.T^[n]) x = x

def minimalPeriod (S : System.{u}) (x : S.X) (n : ℕ) : Prop :=
  0 < n ∧ (S.T^[n]) x = x ∧ ∀ m : ℕ, 0 < m -> (S.T^[m]) x = x -> n ≤ m

def fixedPointSet (S : System.{u}) : Set S.X :=
  {x : S.X | fixedPoint S x}

def periodicPointSet (S : System.{u}) : Set S.X :=
  {x : S.X | periodicPoint S x}

def omegaLimitSet (S : System.{u}) (x : S.X) : Set S.X :=
  ⋂ n : ℕ, closure ((fun k : ℕ => (S.T^[k + n]) x) '' Set.univ)

def hittingTimeSet (S : System.{u}) (U V : Set S.X) : Set ℕ :=
  {n : ℕ | (U ∩ (S.T^[n]) ⁻¹' V).Nonempty}

def pointHittingTimeSet (S : System.{u}) (x : S.X) (U : Set S.X) : Set ℕ :=
  {n : ℕ | (S.T^[n]) x ∈ U}

def IsTopologicallyTransitive (S : System.{u}) : Prop :=
  ∀ U V : Set S.X, IsOpen U -> IsOpen V -> U.Nonempty -> V.Nonempty ->
    (hittingTimeSet S U V).Nonempty

def IsTopologicallyTransitiveOn (S : System.{u}) (A : Set S.X) : Prop :=
  S.T '' A ⊆ A ∧
    ∀ U V : Set S.X, IsOpen U -> IsOpen V ->
      (U ∩ A).Nonempty -> (V ∩ A).Nonempty ->
        ∃ n : ℕ, (U ∩ A ∩ (S.T^[n]) ⁻¹' (V ∩ A)).Nonempty

def IsTransitivePoint (S : System.{u}) (x : S.X) : Prop :=
  orbitClosure S x = Set.univ

def transitivePointSet (S : System.{u}) : Set S.X :=
  {x : S.X | IsTransitivePoint S x}

def HasNoIsolatedPoints (S : System.{u}) : Prop :=
  ∀ x : S.X, ¬ IsOpen ({x} : Set S.X)

def HasCountableDenseSubset (S : System.{u}) : Prop :=
  ∃ D : Set S.X, D.Countable ∧ Dense D

def IsSecondCategorySpace (S : System.{u}) : Prop :=
  ¬ ∃ A : ℕ -> Set S.X,
    (∀ n, IsNowhereDense (A n)) ∧ Set.univ ⊆ ⋃ n, A n

def IsDenseGDelta {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  Dense A ∧ ∃ U : ℕ -> Set X, (∀ n : ℕ, IsOpen (U n)) ∧ A = ⋂ n : ℕ, U n

def HasNoNonconstantContinuousInvariantFunctions (S : System.{u}) : Prop :=
  ∀ f : S.X -> ℂ, Continuous f -> (∀ x : S.X, f (S.T x) = f x) ->
    ∃ c : ℂ, ∀ x : S.X, f x = c

def recurrentPoint (S : System.{u}) (x : S.X) : Prop :=
  x ∈ omegaLimitSet S x

def recurrentPointSet (S : System.{u}) : Set S.X :=
  {x : S.X | recurrentPoint S x}

def IsIpSet (A : Set ℕ) : Prop :=
  ∃ a : ℕ -> ℕ, StrictMono a ∧ {n : ℕ | ∃ F : Finset ℕ, F.Nonempty ∧ n = F.sum a} ⊆ A

def HasRamseyProperty (𝓕 : Set (Set ℕ)) : Prop :=
  ∀ F : Set ℕ, F ∈ 𝓕 -> ∀ F₁ F₂ : Set ℕ, F = F₁ ∪ F₂ -> F₁ ∈ 𝓕 ∨ F₂ ∈ 𝓕

end Chapter05
