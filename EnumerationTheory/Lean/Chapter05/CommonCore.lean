import Chapter05.CommonFoundation

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

def IsMinimalSet (S : System.{u}) (M : Set S.X) : Prop :=
  M.Nonempty ∧ IsClosed M ∧ S.T '' M ⊆ M ∧
    ∀ N : Set S.X, N.Nonempty -> IsClosed N -> N ⊆ M -> S.T '' N ⊆ N -> N = M

def IsMinimalSystem (S : System.{u}) : Prop :=
  IsMinimalSet S Set.univ

/-- The next index in a nonempty cyclic family. -/
def cyclicSucc (pieces : ℕ) (hpieces : 0 < pieces) (i : Fin pieces) : Fin pieces :=
  ⟨(i.1 + 1) % pieces, Nat.mod_lt _ hpieces⟩

/-- A finite closed cyclic cover, together with the invariance needed to form
the systems obtained by restricting `T^[step]` to its pieces. -/
structure IsCyclicDecomposition (S : System.{u}) (step pieces : ℕ)
    (Xpart : Fin pieces -> Set S.X) : Prop where
  pieces_pos : 0 < pieces
  pieces_dvd_step : pieces ∣ step
  closed : ∀ i, IsClosed (Xpart i)
  pairwise_distinct : ∀ i j, i ≠ j -> Xpart i ≠ Xpart j
  cover : Set.univ = ⋃ i, Xpart i
  cyclic_image : ∀ i : Fin pieces,
    S.T '' Xpart i = Xpart (cyclicSucc pieces pieces_pos i)
  iterate_maps : ∀ i : Fin pieces, Set.MapsTo (S.T^[step]) (Xpart i) (Xpart i)

/-- The system induced by the `step`-th iterate on an invariant subset. -/
def iterateRestriction (S : System.{u}) (step : ℕ) (A : Set S.X)
    (hA : Set.MapsTo (S.T^[step]) A A) : System.{u} where
  X := A
  topology := inferInstance
  T := fun x => ⟨(S.T^[step]) x, hA x.2⟩

/-- The cyclic decomposition in Theorem 5.2.13, including transitivity of
the `step`-th iterate on every piece. -/
def IsTransitiveCyclicDecomposition (S : System.{u}) (step pieces : ℕ)
    (Xpart : Fin pieces -> Set S.X) : Prop :=
  ∃ hcyclic : IsCyclicDecomposition S step pieces Xpart,
    ∀ i, IsTopologicallyTransitive
      (iterateRestriction S step (Xpart i) (hcyclic.iterate_maps i))

/-- The disjoint cyclic decomposition in Lemma 5.3.22, including minimality
of the `step`-th iterate on every piece. -/
def IsMinimalCyclicDecomposition (S : System.{u}) (step pieces : ℕ)
    (Xpart : Fin pieces -> Set S.X) : Prop :=
  ∃ hcyclic : IsCyclicDecomposition S step pieces Xpart,
    (∀ i j, i ≠ j -> Disjoint (Xpart i) (Xpart j)) ∧
    ∀ i, IsMinimalSystem
      (iterateRestriction S step (Xpart i) (hcyclic.iterate_maps i))

def IsSyndetic (A : Set ℕ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, ∃ a ∈ A, n ≤ a ∧ a ≤ n + N

def IsThick (A : Set ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, ∀ k : ℕ, k ≤ N -> n + k ∈ A

def IsPiecewiseSyndetic (A : Set ℕ) : Prop :=
  ∃ S T : Set ℕ, IsSyndetic S ∧ IsThick T ∧ A = S ∩ T

def IsThicklySyndetic (A : Set ℕ) : Prop :=
  ∀ N : ℕ, ∃ S : Set ℕ, IsSyndetic S ∧ ∀ s ∈ S, ∀ k : ℕ, k ≤ N -> s + k ∈ A

def almostPeriodicPoint (S : System.{u}) (x : S.X) : Prop :=
  ∀ U : Set S.X, IsOpen U -> x ∈ U -> IsSyndetic (pointHittingTimeSet S x U)

def almostPeriodicPointSet (S : System.{u}) : Set S.X :=
  {x : S.X | almostPeriodicPoint S x}

def IsSemiOpenFactorMap (S₁ : System.{u}) (S₂ : System.{v}) (π : S₁.X -> S₂.X) : Prop :=
  IsFactorMap S₁ S₂ π ∧ ∀ U : Set S₁.X, IsOpen U -> U.Nonempty -> (interior (π '' U)).Nonempty

def IsFullShift (S : System.{u}) (k : ℕ) : Prop :=
  ∃ e : S.X ≃ₜ (ℤ -> Fin k),
    ∀ x : S.X, ∀ n : ℤ, e (S.T x) n = e x (n + 1)

/-- The two-sided subshift selected by a zero-one adjacency relation. -/
def adjacencySubshift (k : ℕ) (A : Fin k -> Fin k -> Prop) : Set (ℤ -> Fin k) :=
  {x | ∀ n : ℤ, A (x n) (x (n + 1))}

noncomputable abbrev circleRotationTopologicalSystem (α : ℝ) : System where
  X := AddCircle (1 : ℝ)
  topology := inferInstance
  T := fun x => x + (α : AddCircle (1 : ℝ))

noncomputable abbrev addingMachineTopologicalSystem : System where
  X := Chapter01.BinarySequence
  topology := inferInstance
  T := Chapter01.addingOne

noncomputable def compactGroupRotationTopologicalSystem
    (G : Type u) [TopologicalSpace G] [Add G] (g₀ : G) : System.{u} where
  X := G
  topology := inferInstance
  T := fun g => g₀ + g

def WordOccursSyndetically {A : Type u} (x : ℤ -> A) : Prop :=
  ∀ w : List A, (∃ i : ℤ, ∀ j : Fin w.length, x (i + j) = w.get j) ->
    ∃ N : ℕ, 0 < N ∧ ∀ i : ℤ, ∃ j : ℤ,
      i ≤ j ∧ j ≤ i + N ∧
      ∀ r : Fin w.length, x (j + r) = w.get r

def IsPSystem (S : System.{u}) : Prop :=
  IsTopologicallyTransitive S ∧ Dense (periodicPointSet S)

def IsMSystem (S : System.{u}) : Prop :=
  IsTopologicallyTransitive S ∧ Dense (almostPeriodicPointSet S)

def IsRecurrenceSet (A : Set ℕ) : Prop :=
  ∀ S : System.{u}, IsTopologicalSystem S -> IsCompact (Set.univ : Set S.X) ->
    ∀ U : Set S.X, IsOpen U -> U.Nonempty ->
      ∃ n ∈ A, 0 < n ∧ (U ∩ (S.T^[n]) ⁻¹' U).Nonempty

def differenceSet (A : Set ℕ) : Set ℤ :=
  {n : ℤ | ∃ a ∈ A, ∃ b ∈ A, n = (a : ℤ) - (b : ℤ)}

def IsWeaklyDisjoint (S : System.{u}) (R : System.{v}) : Prop :=
  IsTopologicallyTransitive { X := S.X × R.X, topology := inferInstance, T := fun p => (S.T p.1, R.T p.2) }

def IsCofinite (A : Set ℕ) : Prop :=
  Set.Finite Aᶜ

def IsWeakMixing (S : System.{u}) : Prop :=
  IsWeaklyDisjoint S S

def IsStrongMixing (S : System.{u}) : Prop :=
  ∀ U V : Set S.X, IsOpen U -> IsOpen V -> U.Nonempty -> V.Nonempty -> IsCofinite (hittingTimeSet S U V)

def IsFilterFamily (𝓕 : Set (Set ℕ)) : Prop :=
  ∅ ∉ 𝓕 ∧ (∀ A B : Set ℕ, A ∈ 𝓕 -> A ⊆ B -> B ∈ 𝓕) ∧
    ∀ A B : Set ℕ, A ∈ 𝓕 -> B ∈ 𝓕 -> A ∩ B ∈ 𝓕

end Chapter05

