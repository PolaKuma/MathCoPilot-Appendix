import Chapter05.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

namespace Section01


/--
Source: Definition 5.1.1, Chapter 5, Section 1.
A factor map, or semi-conjugacy, between topological dynamical systems is a
continuous surjection intertwining the dynamics.
-/
def topologicalFactorMap (S₁ : System.{u}) (S₂ : System.{v}) (π : S₁.X -> S₂.X) : Prop :=
  IsFactorMap S₁ S₂ π

/--
Source: Definition 5.1.1, Chapter 5, Section 1.
Topological conjugacy is factor equivalence through mutually inverse continuous
intertwining maps.
-/
def topologicalConjugacy (S₁ : System.{u}) (S₂ : System.{v}) : Prop :=
  IsTopologicallyConjugate S₁ S₂

/--
Source: Proposition 5.1.2, Chapter 5, Section 1.
Factor systems of a topological system correspond to closed invariant
equivalence relations on the underlying space.
-/
theorem factorSystemsCorrespondToClosedInvariantEquivalences (S : System.{u}) :
    IsTopologicalSystem S ->
    (∀ (Q : System.{u}) (π : S.X -> Q.X), IsFactorMap S Q π ->
      IsClosedInvariantEquivalence S.T (factorKernel S Q π)) ∧
    (∀ R : S.X -> S.X -> Prop, IsClosedInvariantEquivalence S.T R ->
      ∃ Q : System.{u}, ∃ π : S.X -> Q.X,
        IsFactorMap S Q π ∧ factorKernel S Q π = R) ∧
    ∀ (Q₁ Q₂ : System.{u}) (π₁ : S.X -> Q₁.X) (π₂ : S.X -> Q₂.X),
      IsFactorMap S Q₁ π₁ -> IsFactorMap S Q₂ π₂ ->
      factorKernel S Q₁ π₁ = factorKernel S Q₂ π₂ ->
      ∃ φ : Q₁.X -> Q₂.X, ∃ ψ : Q₂.X -> Q₁.X,
        IsFactorMap Q₁ Q₂ φ ∧ IsFactorMap Q₂ Q₁ ψ ∧
        Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ ∧
        φ ∘ π₁ = π₂ := by
  sorry

/--
Source: Proposition 5.1.2, Chapter 5, Section 1.
The restriction of a continuous self-map to the eventual image is surjective.
-/
theorem eventualImageRestrictionSurjective (S : System.{u}) :
    IsTopologicalSystem S -> Set.SurjOn S.T (eventualImage S) (eventualImage S) := by
  sorry

/--
Source: Proposition 5.1.2, Chapter 5, Section 1.
A surjective topological system has a natural extension which is invertible and
factors onto the original system.
-/
theorem naturalExtensionOfSurjectiveSystem (S : System.{u}) :
    IsTopologicalSystem S -> Function.Surjective S.T ->
      ∃ E : System.{u}, ∃ π : E.X -> S.X, IsNaturalExtension S E π := by
  sorry

/-- The Euclidean unit circle with centre `(0,1)` used in Example 5.1.3. -/
abbrev ShiftedUnitCircle :=
  {p : ℝ × ℝ // p.1 ^ 2 + (p.2 - 1) ^ 2 = 1}

/-- The point `z_θ` obtained by intersecting the circle with the ray from the
north pole making angle `θ` with the downward vertical axis. -/
def northSouthCircleParam (θ : ℝ) : ℝ × ℝ :=
  (Real.sin (2 * θ), 1 - Real.cos (2 * θ))

/--
Source: Example 5.1.3, Chapter 5, Section 1.
The north-south system on the circle has two fixed poles, with non-pole forward
orbits converging to the south pole and backward orbits converging to the north
pole.
-/
theorem northSouthSystemExample :
    ∃ S : System.{0}, ∃ _ : PseudoMetricSpace S.X,
      ∃ e : S.X ≃ₜ ShiftedUnitCircle,
      ∃ z : ℝ -> S.X, ∃ north south : S.X, ∃ inv : S.X -> S.X,
      IsCompactTopologicalSystem S ∧ IsContinuousInverse S inv ∧
      ((e north : ℝ × ℝ) = (0, 2)) ∧
      ((e south : ℝ × ℝ) = (0, 0)) ∧
      (∀ θ : ℝ, -Real.pi / 2 < θ -> θ < Real.pi / 2 ->
        (e (z θ) : ℝ × ℝ) = northSouthCircleParam θ ∧
        S.T (z θ) = z (Real.arctan (Real.tan θ / 2))) ∧
      (∀ x : S.X, x ≠ north -> ∃ θ : ℝ,
        -Real.pi / 2 < θ ∧ θ < Real.pi / 2 ∧ x = z θ) ∧
      fixedPoint S north ∧ fixedPoint S south ∧ north ≠ south ∧
      (∀ x : S.X, x ≠ north -> x ≠ south ->
        Tendsto (fun n : ℕ => (S.T^[n]) x) atTop (nhds south)) ∧
      ∀ x : S.X, x ≠ north -> x ≠ south ->
        Tendsto (fun n : ℕ => (inv^[n]) x) atTop (nhds north) := by
  sorry

/--
Source: Example 5.1.4, Chapter 5, Section 1.
A zero-one adjacency matrix defines a closed shift-invariant subshift of finite
type, with the full shift and finite periodic shifts as basic cases.
-/
theorem subshiftOfFiniteTypeExamples :
    ∀ k : ℕ, 2 ≤ k -> ∀ A : Fin k -> Fin k -> Prop,
      IsClosed (adjacencySubshift k A) ∧
      (∀ x ∈ adjacencySubshift k A, symbolicShift x ∈ adjacencySubshift k A) ∧
      adjacencySubshift k (fun _ _ => True) = Set.univ ∧
      adjacencySubshift k (fun i j => i = j) =
        {x : ℤ -> Fin k | ∀ n : ℤ, x n = x 0} ∧
      adjacencySubshift 2 (fun i j => i.1 = 1 ∧ j.1 = 0) = ∅ ∧
      adjacencySubshift 2 (fun i j => j.1 = 1) =
        adjacencySubshift 2 (fun i j => i.1 = 1 ∧ j.1 = 1) := by
  sorry

abbrev RealTwoMatrix := Matrix (Fin 2) (Fin 2) ℝ

def IsSL2Matrix (A : RealTwoMatrix) : Prop :=
  Matrix.det A = 1

def horocycleMatrix (t : ℝ) : RealTwoMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1 else
    if i = 0 ∧ j = 1 then t else
    if i = 1 ∧ j = 1 then 1 else 0

def geodesicMatrix (s : ℝ) : RealTwoMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then Real.exp (-s) else
    if i = 1 ∧ j = 1 then Real.exp s else 0

/-- Concrete data for a compact homogeneous space `SL(2,ℝ)/Γ`, including
the discrete cocompact lattice and its unique invariant probability measure. -/
structure CompactSL2QuotientModel where
  X : Type u
  topology : TopologicalSpace X
  measurableSpace : MeasurableSpace X
  μ : MeasureTheory.Measure X
  lattice : Set RealTwoMatrix
  quotient : RealTwoMatrix -> X
  action : RealTwoMatrix -> X -> X
  lattice_is_sl2 : ∀ γ ∈ lattice, IsSL2Matrix γ
  lattice_one : (1 : RealTwoMatrix) ∈ lattice
  lattice_mul : ∀ A ∈ lattice, ∀ B ∈ lattice, A * B ∈ lattice
  lattice_inv : ∀ A ∈ lattice, ∃ B ∈ lattice, A * B = 1 ∧ B * A = 1
  lattice_discrete : ∃ U : Set RealTwoMatrix,
    IsOpen U ∧ (1 : RealTwoMatrix) ∈ U ∧ U ∩ lattice = {1}
  quotient_surjective : ∀ x : X, ∃ A, IsSL2Matrix A ∧ quotient A = x
  quotient_kernel : ∀ A B, IsSL2Matrix A -> IsSL2Matrix B ->
    (quotient A = quotient B ↔ ∃ γ ∈ lattice, B = A * γ)
  quotient_continuous : Continuous quotient
  quotient_compact : IsCompact (Set.univ : Set X)
  action_law : ∀ A B, IsSL2Matrix A -> IsSL2Matrix B -> ∀ x,
    action (A * B) x = action A (action B x)
  action_on_quotient : ∀ A B, IsSL2Matrix A -> IsSL2Matrix B ->
    action A (quotient B) = quotient (A * B)
  action_continuous : ∀ A, IsSL2Matrix A -> Continuous (action A)
  probability : MeasureTheory.IsProbabilityMeasure μ
  invariant : ∀ A, IsSL2Matrix A ->
    MeasureTheory.MeasurePreserving (action A) μ μ
  unique_invariant_probability : ∀ ν : MeasureTheory.Measure X,
    MeasureTheory.IsProbabilityMeasure ν ->
    (∀ A, IsSL2Matrix A -> MeasureTheory.MeasurePreserving (action A) ν ν) ->
    ν = μ

attribute [instance] CompactSL2QuotientModel.topology
attribute [instance] CompactSL2QuotientModel.measurableSpace

/--
Source: Example 5.1.5, Chapter 5, Section 1.
Horocycle and geodesic flows on a compact quotient of `SL(2, R)` satisfy the
standard conjugation relation between the unipotent and diagonal flows.
-/
theorem horocycleGeodesicFlowRelationExample
    (M : CompactSL2QuotientModel.{u}) :
    let h : ℝ -> M.X -> M.X := fun t => M.action (horocycleMatrix t)
    let g : ℝ -> M.X -> M.X := fun s => M.action (geodesicMatrix s)
    (∀ t, IsSL2Matrix (horocycleMatrix t)) ∧
    (∀ s, IsSL2Matrix (geodesicMatrix s)) ∧
    (∀ s t x, g (s + t) x = g s (g t x)) ∧
    (∀ s t x, h (s + t) x = h s (h t x)) ∧
    (∀ t, MeasureTheory.MeasurePreserving (h t) M.μ M.μ) ∧
    (∀ s, MeasureTheory.MeasurePreserving (g s) M.μ M.μ) ∧
    ∀ s t : ℝ, ∀ x : M.X,
      g s (h t (g (-s) x)) = h (Real.exp (-2 * s) * t) x := by
  sorry

end Section01
end Chapter05
