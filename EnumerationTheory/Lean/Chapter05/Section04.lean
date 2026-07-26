import Chapter05.Section03

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

namespace Section04


/-- Source: Definition 5.4.1, Chapter 5, Section 4. -/
def weaklyDisjointSystems (S R : System.{u}) : Prop :=
  IsWeaklyDisjoint S R

/-- Source: Definition 5.4.1, Chapter 5, Section 4. -/
def cofiniteSet (A : Set ℕ) : Prop :=
  IsCofinite A

/-- Source: Definition 5.4.1, Chapter 5, Section 4. -/
def topologicalHittingTimeSet (S : System.{u}) (A B : Set S.X) : Set ℕ :=
  hittingTimeSet S A B

/-- Source: Definition 5.4.2, Chapter 5, Section 4. -/
def topologicalWeakMixing (S : System.{u}) : Prop :=
  IsWeakMixing S

/-- Source: Definition 5.4.2, Chapter 5, Section 4. -/
def topologicalStrongMixing (S : System.{u}) : Prop :=
  IsStrongMixing S

/-- Source: Definition 5.4.3, Chapter 5, Section 4. -/
def filterFamily (𝓕 : Set (Set ℕ)) : Prop :=
  IsFilterFamily 𝓕

/-- Source: Definition 5.4.3, Chapter 5, Section 4. -/
def familyUpwardClosure (𝓕 : Set (Set ℕ)) : Set (Set ℕ) :=
  upwardClosure 𝓕

/--
Source: Theorem 5.4.4, Chapter 5, Section 4.
Furstenberg intersection lemma: weak mixing is equivalent to the filter property
of the upward closure of hitting-time sets.
-/
theorem furstenbergIntersectionLemma (S : System.{u}) :
    IsWeakMixing S ↔ IsFilterFamily (upwardClosure {A : Set ℕ | ∃ U V : Set S.X,
      IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧ A = hittingTimeSet S U V}) := by
  sorry

/--
Source: Theorem 5.4.5, Chapter 5, Section 4.
Equivalent characterizations of topological weak mixing, including thickness of
all nonempty open hitting-time sets.
-/
theorem weakMixingEquivalentCharacterizations (S : System.{u}) :
    IsWeakMixing S ↔
      ∀ U V : Set S.X, IsOpen U -> IsOpen V -> U.Nonempty -> V.Nonempty ->
        IsThick (hittingTimeSet S U V) := by
  sorry

/-- Source: Definition 5.4.6, Chapter 5, Section 4. -/
def topologicalMildMixing (S : System.{u}) : Prop :=
  IsMildMixing S

/--
Source: Definition 5.4.6, Chapter 5, Section 4.
The product of two mild-mixing systems is mild mixing.
-/
theorem mildMixingProductRemark (S R : System.{u}) :
    IsMildMixing S -> IsMildMixing R ->
      IsMildMixing { X := S.X × R.X, topology := inferInstance, T := fun p => (S.T p.1, R.T p.2) } := by
  sorry

/--
Source: Theorem 5.4.7, Chapter 5, Section 4.
A system is topologically mild mixing iff every nonempty open hitting-time set
meets every IP-difference set.
-/
theorem mildMixingIffHitsIpDifferenceSets (S : System.{u}) :
    IsMildMixing S ↔ ∀ U V : Set S.X, IsOpen U -> IsOpen V -> U.Nonempty -> V.Nonempty ->
      MeetsEvery (hittingTimeSet S U V) (FamilyDifference {A : Set ℕ | IsIpSet A}) := by
  sorry

end Section04
end Chapter05
