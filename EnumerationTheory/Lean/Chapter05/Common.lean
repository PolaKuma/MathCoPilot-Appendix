import Chapter05.CommonCore

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

def upwardClosure (𝓕 : Set (Set ℕ)) : Set (Set ℕ) :=
  {A : Set ℕ | ∃ F ∈ 𝓕, F ⊆ A}

def IsMildMixing (S : System.{u}) : Prop :=
  ∀ R : System.{u}, IsTopologicallyTransitive R -> IsWeaklyDisjoint S R

def FamilyDifference (𝓕 : Set (Set ℕ)) : Set (Set ℤ) :=
  {D : Set ℤ | ∃ F ∈ 𝓕, D = differenceSet F}

def MeetsEvery (A : Set ℕ) (𝓖 : Set (Set ℤ)) : Prop :=
  ∀ G ∈ 𝓖, ((fun n : ℕ => (n : ℤ)) '' A ∩ G).Nonempty

def totalOmegaLimitSet (S : System.{u}) : Set S.X :=
  ⋃ x : S.X, omegaLimitSet S x

def alphaLimitSet (S : System.{u}) (inv : S.X -> S.X) (x : S.X) : Set S.X :=
  omegaLimitSet { S with T := inv } x

def nonwanderingPoint (S : System.{u}) (x : S.X) : Prop :=
  ∀ U : Set S.X, IsOpen U -> x ∈ U -> ∃ n : ℕ, 0 < n ∧ (U ∩ (S.T^[n]) ⁻¹' U).Nonempty

def nonwanderingSet (S : System.{u}) : Set S.X :=
  {x : S.X | nonwanderingPoint S x}

def IsEquicontinuousForDistance (S : System.{u}) (d : S.X -> S.X -> ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ δ : ℝ, 0 < δ ∧ ∀ x y : S.X,
    d x y < δ -> ∀ n : ℕ, d ((S.T^[n]) x) ((S.T^[n]) y) < ε

def IsCompatibleMetric (S : System.{u}) (d : S.X -> S.X -> ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧
  (∀ x y, d x y = 0 ↔ x = y) ∧
  (∀ x y, d x y = d y x) ∧
  (∀ x y z, d x z ≤ d x y + d y z) ∧
  ∀ U : Set S.X, IsOpen U ↔
    ∀ x ∈ U, ∃ ε : ℝ, 0 < ε ∧ {y : S.X | d x y < ε} ⊆ U

def IsEquicontinuous (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsCompatibleMetric S dist ∧ IsEquicontinuousForDistance S dist

def orbitSupDistance (S : System.{u}) [PseudoMetricSpace S.X] (x y : S.X) : ℝ :=
  sSup {r : ℝ | ∃ n : ℕ, r = dist ((S.T^[n]) x) ((S.T^[n]) y)}

/-- A metric which induces the stored topology of `S` and makes `T` an
isometry.  This spells out the word "equivalent" in the discussion after
Definition 5.6.1 without relying on an unrelated metric typeclass instance. -/
def IsCompatibleInvariantMetric (S : System.{u}) (d : S.X -> S.X -> ℝ) : Prop :=
  IsCompatibleMetric S d ∧ ∀ x y, d (S.T x) (S.T y) = d x y

def IsUniformlyAlmostPeriodic (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ A : Set ℕ, IsSyndetic A ∧ ∀ n ∈ A, ∀ x : S.X,
    dist x ((S.T^[n]) x) < ε

def IsTopologicalEigenfunction (S : System.{u}) (lam : ℂ) (f : S.X -> ℂ) : Prop :=
  Continuous f ∧ f ≠ 0 ∧ ∀ x : S.X, f (S.T x) = lam * f x

def topologicalEigenvalueSet (S : System.{u}) : Set ℂ :=
  {lam : ℂ | ∃ f : S.X -> ℂ, IsTopologicalEigenfunction S lam f}

def HasTopologicalDiscreteSpectrum (S : System.{u}) : Prop :=
  ∀ f : S.X -> ℂ, Continuous f -> ∀ ε : ℝ, 0 < ε ->
    ∃ s : Finset (S.X -> ℂ),
      (∀ g ∈ s, ∃ lam : ℂ, IsTopologicalEigenfunction S lam g) ∧
      ∃ c : (S.X -> ℂ) -> ℂ,
        ∀ x : S.X, ‖f x - ∑ g ∈ s, c g * g x‖ < ε

def IsCompactGroupRotationModel (S : System.{u}) : Prop :=
  IsMinimalSystem S ∧
  ∃ G : Type u, ∃ _ : AddCommGroup G, ∃ _ : TopologicalSpace G,
  ∃ _ : IsTopologicalAddGroup G, ∃ _ : CompactSpace G,
  ∃ e : S.X ≃ₜ G, ∃ g₀ : G,
    ∀ x : S.X, e (S.T x) = g₀ + e x

def proximalPair (S : System.{u}) [PseudoMetricSpace S.X] (x y : S.X) : Prop :=
  ∀ ε : ℝ, 0 < ε -> ∃ n : ℕ, dist ((S.T^[n]) x) ((S.T^[n]) y) < ε

def asymptoticPair (S : System.{u}) [PseudoMetricSpace S.X] (x y : S.X) : Prop :=
  Tendsto (fun n : ℕ => dist ((S.T^[n]) x) ((S.T^[n]) y)) atTop (nhds 0)

def distalPair (S : System.{u}) [PseudoMetricSpace S.X] (x y : S.X) : Prop :=
  x ≠ y -> ¬ proximalPair S x y

def IsDistalSystem (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  ∀ x y : S.X, x ≠ y -> distalPair S x y

def IsContinuousInverse (S : System.{u}) (inv : S.X -> S.X) : Prop :=
  Continuous inv ∧ Function.LeftInverse inv S.T ∧ Function.RightInverse inv S.T

/-- The iterate indexed by the acting group `ℤ`; negative indices use the
specified continuous inverse. -/
def ziterate (S : System.{u}) (inv : S.X -> S.X) (n : ℤ) : S.X -> S.X :=
  if 0 ≤ n then S.T^[n.toNat] else inv^[n.natAbs]

def twoSidedOrbit (S : System.{u}) (inv : S.X -> S.X) (x : S.X) : Set S.X :=
  Set.range fun n : ℤ => ziterate S inv n x

def IsTwoSidedTransitivePoint (S : System.{u}) (inv : S.X -> S.X) (x : S.X) : Prop :=
  IsContinuousInverse S inv ∧ Dense (twoSidedOrbit S inv x)

def IsTwoSidedMinimalSystem (S : System.{u}) (inv : S.X -> S.X) : Prop :=
  IsContinuousInverse S inv ∧ ∀ x : S.X, Dense (twoSidedOrbit S inv x)

def IsEquicontinuousExtension (S₁ : System.{u}) (S₂ : System.{v})
    [PseudoMetricSpace S₁.X] [PseudoMetricSpace S₂.X] (π : S₁.X -> S₂.X) : Prop :=
  IsFactorMap S₁ S₂ π ∧ IsCompatibleMetric S₁ dist ∧
  IsCompatibleMetric S₂ dist ∧
  ∃ inv : S₁.X -> S₁.X, IsContinuousInverse S₁ inv ∧
  ∃ inv₂ : S₂.X -> S₂.X, IsContinuousInverse S₂ inv₂ ∧
  ∀ ε : ℝ, 0 < ε -> ∃ δ : ℝ, 0 < δ ∧ ∀ x y : S₁.X,
    π x = π y -> dist x y < δ -> ∀ n : ℤ,
      dist (ziterate S₁ inv n x) (ziterate S₁ inv n y) < ε

abbrev SymbolicSequence (A : Type u) := ℤ -> A

def symbolicShift {A : Type u} (x : SymbolicSequence A) : SymbolicSequence A :=
  fun n => x (n + 1)

abbrev Substitution (A : Type u) := A -> List A

def substituteWord {A : Type u} (σ : Substitution A) (w : List A) : List A :=
  w.flatMap σ

def IsPrimitiveSubstitution {A : Type u} [Fintype A] [DecidableEq A]
    (σ : Substitution A) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∀ a b : A, b ∈ ((substituteWord σ)^[r]) [a]

def WordOccursInSequence {A : Type u} (w : List A) (x : SymbolicSequence A) : Prop :=
  ∃ start : ℤ, ∀ i : Fin w.length, x (start + i.val) = w.get i

def WordOccursInWord {A : Type u} (u w : List A) : Prop :=
  ∃ pre suff : List A, u = pre ++ w ++ suff

def HasSubstitutionLanguage {A : Type u} [Fintype A] [DecidableEq A]
    (σ : Substitution A) (x : SymbolicSequence A) : Prop :=
  ∀ w : List A, WordOccursInSequence w x ↔
    ∃ r : ℕ, ∃ a : A, WordOccursInWord (((substituteWord σ)^[r]) [a]) w

def IsOrbitClosurePresentation {A : Type u} [TopologicalSpace (SymbolicSequence A)]
    (S : System.{u}) (x : SymbolicSequence A) : Prop :=
  ∃ e : S.X -> SymbolicSequence A,
    Continuous e ∧ Function.Injective e ∧
    e '' Set.univ = closure {y | ∃ n : ℕ, (symbolicShift^[n]) x = y} ∧
    ∀ y : S.X, e (S.T y) = symbolicShift (e y)

def IsSubstitutionSystem {A : Type u} [Fintype A] [DecidableEq A]
    [TopologicalSpace (SymbolicSequence A)]
    (S : System.{u}) (σ : Substitution A) : Prop :=
  ∃ x : SymbolicSequence A, HasSubstitutionLanguage σ x ∧
    IsOrbitClosurePresentation S x

def morseSubstitution : Substitution Bool
  | false => [false, true]
  | true => [true, false]

def morseWords : ℕ -> List Bool
  | 0 => [false]
  | n + 1 => morseWords n ++ (morseWords n).map (!·)

def chaconWords : ℕ -> List Bool
  | 0 => [false]
  | n + 1 => chaconWords n ++ chaconWords n ++ [true] ++ chaconWords n

def IsGeneratedByWordTower (S : System.{0}) (words : ℕ -> List Bool) : Prop :=
  ∃ x : SymbolicSequence Bool, IsOrbitClosurePresentation S x ∧
    ∀ w : List Bool, WordOccursInSequence w x ↔
      ∃ n : ℕ, WordOccursInWord (words n) w

def IsToeplitzSequence {A : Type u} (x : SymbolicSequence A) : Prop :=
  ∀ n : ℤ, ∃ p : ℕ, 0 < p ∧ ∀ k : ℤ, x (n + k * p) = x n

def IsToeplitzSystem {A : Type u} [TopologicalSpace (SymbolicSequence A)]
    (S : System.{u}) : Prop :=
  ∃ x : SymbolicSequence A, IsToeplitzSequence x ∧ IsOrbitClosurePresentation S x

def fractionalPart (x : ℝ) : ℝ :=
  x - (Int.floor x : ℝ)

def sturmianCoding (α ρ : ℝ) : SymbolicSequence Bool :=
  fun n => decide (1 - α ≤ fractionalPart (ρ + n * α))

def IsSturmianSystem (S : System.{0}) (α : ℝ) : Prop :=
  Irrational α ∧ ∃ ρ : ℝ, IsOrbitClosurePresentation S (sturmianCoding α ρ)

end Chapter05
