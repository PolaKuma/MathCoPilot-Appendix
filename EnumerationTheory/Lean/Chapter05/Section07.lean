import Chapter05.Section06

noncomputable section

open Classical Filter
open scoped BigOperators Manifold

namespace Chapter05

universe u v w

namespace Section07

-- Statement-fidelity review: all metric claims below use the compatible
-- metrics required by the Chapter 5 common interface.

def IsExpansiveForDistance (S : System.{u}) (d : S.X -> S.X -> ℝ) : Prop :=
  ∃ inv : S.X -> S.X, IsContinuousInverse S inv ∧
  ∃ δ : ℝ, 0 < δ ∧ ∀ x y : S.X, x ≠ y -> ∃ n : ℤ,
    d (ziterate S inv n x) (ziterate S inv n y) > δ

def IsExpansive (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsCompatibleMetric S dist ∧ IsExpansiveForDistance S dist

def IsExpansiveWithConstant (S : System.{u}) [PseudoMetricSpace S.X]
    (inv : S.X -> S.X) (δ : ℝ) : Prop :=
  IsCompatibleMetric S dist ∧ IsContinuousInverse S inv ∧ 0 < δ ∧
    ∀ x y : S.X, x ≠ y -> ∃ n : ℤ,
      dist (ziterate S inv n x) (ziterate S inv n y) > δ

def IsSensitive (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsCompatibleMetric S dist ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : S.X, ∀ δ : ℝ, 0 < δ ->
    ∃ y : S.X, ∃ n : ℕ,
      dist x y < δ ∧ dist ((S.T^[n]) x) ((S.T^[n]) y) > ε

def IsGeneratorCover (S : System.{u}) [PseudoMetricSpace S.X]
    (α : Set (Set S.X)) : Prop :=
  Set.Finite α ∧ (∀ A ∈ α, IsOpen A) ∧ (⋃₀ α = Set.univ) ∧
    ∃ inv : S.X -> S.X, IsContinuousInverse S inv ∧
    ∀ choice : ℤ -> Set S.X, (∀ n : ℤ, choice n ∈ α) ->
      Set.Subsingleton (⋂ n : ℤ, (ziterate S inv n) ⁻¹' closure (choice n))

def IsWeakGeneratorCover (S : System.{u}) [PseudoMetricSpace S.X]
    (α : Set (Set S.X)) : Prop :=
  Set.Finite α ∧ (∀ A ∈ α, IsOpen A) ∧ (⋃₀ α = Set.univ) ∧
    ∃ inv : S.X -> S.X, IsContinuousInverse S inv ∧
    ∀ choice : ℤ -> Set S.X, (∀ n : ℤ, choice n ∈ α) ->
      Set.Subsingleton (⋂ n : ℤ, (ziterate S inv n) ⁻¹' choice n)

def HasGenerator (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  ∃ α : Set (Set S.X), IsGeneratorCover S α

def HasWeakGenerator (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  ∃ α : Set (Set S.X), IsWeakGeneratorCover S α

def coverJoinDiameterTendsToZero (S : System.{u}) [PseudoMetricSpace S.X]
    (γ : Set (Set S.X)) : Prop :=
  Set.Finite γ ∧ ∃ inv : S.X -> S.X, IsContinuousInverse S inv ∧
    ∀ ε : ℝ, 0 < ε -> ∃ N : ℕ, ∀ n : ℕ, N ≤ n ->
      ∀ choice : ℤ -> Set S.X, (∀ k, choice k ∈ γ) ->
        Metric.diam (⋂ k ∈ Set.Icc (-(n : ℤ)) (n : ℤ),
          (ziterate S inv k) ⁻¹' closure (choice k)) < ε

def IsSubshiftExtensionOf (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  ∃ k : ℕ, ∃ Ω : System.{u}, ∃ C : Set (ℤ -> Fin k),
    IsClosed C ∧
    (∀ x ∈ C, (fun n => x (n + 1)) ∈ C) ∧
    (∃ e : Ω.X ≃ₜ C,
      ∀ x n, (e (Ω.T x) : ℤ -> Fin k) n = (e x : ℤ -> Fin k) (n + 1)) ∧
    ∃ φ : Ω.X -> S.X, IsFactorMap Ω S φ

def IsSubshift (S : System.{u}) (k : ℕ) : Prop :=
  ∃ C : Set (ℤ -> Fin k), IsClosed C ∧
    (∀ x ∈ C, symbolicShift x ∈ C) ∧
    ∃ e : S.X ≃ₜ C,
      ∀ x : S.X, ∀ n : ℤ,
        (e (S.T x) : ℤ -> Fin k) n = (e x : ℤ -> Fin k) (n + 1)

/-- Source: Definition 5.7.1, Chapter 5, Section 7. -/
def expansiveHomeomorphism (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsExpansive S

/--
Source: Remark 5.7.2, Chapter 5, Section 7.
Expansiveness is contrasted with Lyapunov instability and sensitive dependence
on initial conditions; for transitive systems pointwise instability yields a
uniform sensitivity constant.
-/
def sensitivityRemark (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsExpansive S -> IsSensitive S

/-- Source: Definition 5.7.3, Chapter 5, Section 7. -/
def generatorCover (S : System.{u}) [PseudoMetricSpace S.X] (α : Set (Set S.X)) : Prop :=
  IsGeneratorCover S α

/-- Source: Definition 5.7.3, Chapter 5, Section 7. -/
def weakGeneratorCover (S : System.{u}) [PseudoMetricSpace S.X] (α : Set (Set S.X)) : Prop :=
  IsWeakGeneratorCover S α

/--
Source: Remark 5.7.4, Chapter 5, Section 7.
A finite open cover is a generator iff every bi-infinite itinerary determines at
most one point, equivalently each full refined atom is empty or a singleton.
-/
def generatorItineraryReformulationRemark (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  HasGenerator S ↔ ∃ α : Set (Set S.X), IsGeneratorCover S α

/--
Source: Theorem 5.7.5, Chapter 5, Section 7.
A compact metric homeomorphism has a generator iff it has a weak generator.
-/
theorem generatorIffWeakGenerator (S : System.{u}) [PseudoMetricSpace S.X] :
    IsCompactTopologicalSystem S ->
    (∃ inv : S.X -> S.X, IsContinuousInverse S inv) ->
      (HasGenerator S ↔ HasWeakGenerator S) := by
  sorry

/--
Source: Theorem 5.7.6, Chapter 5, Section 7.
For a generator, sufficiently long finite joins have arbitrarily small diameter,
and conversely small balls fit into atoms of finite joins.
-/
theorem generatorFiniteJoinDiameterControl
    (S : System.{u}) [PseudoMetricSpace S.X] (α : Set (Set S.X)) :
    IsCompactTopologicalSystem S ->
    (∃ inv : S.X -> S.X, IsContinuousInverse S inv) ->
    (IsGeneratorCover S α -> coverJoinDiameterTendsToZero S α) ∧
    (∀ N : ℕ, 0 < N -> ∃ ε : ℝ, 0 < ε ∧ ∀ x y : S.X,
      dist x y < ε -> ∃ inv : S.X -> S.X, IsContinuousInverse S inv ∧
      ∃ choice : ℤ -> Set S.X, (∀ n, choice n ∈ α) ∧
        x ∈ ⋂ n ∈ Set.Icc (-(N : ℤ)) (N : ℤ),
          (ziterate S inv n) ⁻¹' choice n ∧
        y ∈ ⋂ n ∈ Set.Icc (-(N : ℤ)) (N : ℤ),
          (ziterate S inv n) ⁻¹' choice n) := by
  sorry

/--
Source: Theorem 5.7.7, Chapter 5, Section 7.
Reddy-Keynes-Robertson theorem: expansiveness is equivalent to having a generator
and to having a weak generator.
-/
theorem expansiveIffGeneratorIffWeakGenerator
    (S : System.{u}) [PseudoMetricSpace S.X] :
    IsCompactTopologicalSystem S ->
    (∃ inv : S.X -> S.X, IsContinuousInverse S inv) ->
      (IsExpansive S ↔ HasGenerator S) ∧
      (IsExpansive S ↔ HasWeakGenerator S) := by
  sorry

/-- Expansiveness expressed without selecting a global metric typeclass. -/
def HasCompatibleExpansiveMetric (S : System.{u}) : Prop :=
  ∃ d : S.X -> S.X -> ℝ,
    IsCompatibleMetric S d ∧ IsExpansiveForDistance S d

def integerIterateSystem (S : System.{u}) (inv : S.X -> S.X) (k : ℤ) : System.{u} :=
  { S with T := ziterate S inv k }

def countableProductTopologicalSystem (S : ℕ -> System.{u}) : System.{u} where
  X := ∀ n, (S n).X
  topology := inferInstance
  T := fun x n => (S n).T (x n)

def finiteProductTopologicalSystem {n : ℕ} (S : Fin n -> System.{u}) : System.{u} where
  X := ∀ i, (S i).X
  topology := inferInstance
  T := fun x i => (S i).T (x i)

def IsTopologicalSubsystem (S : System.{u}) (R : System.{v})
    (ι : R.X -> S.X) : Prop :=
  IsTopologicalSystem S ∧ IsTopologicalSystem R ∧
  Continuous ι ∧ Function.Injective ι ∧ IsClosed (Set.range ι) ∧
  ∀ x : R.X, ι (R.T x) = S.T (ι x)

/--
Source: Remark 5.7.8, Chapter 5, Section 7.
Expansiveness is metric-independent, invariant under nonzero iterates and
conjugacy, inherited by subsystems, and preserved by finite products.
-/
def expansivenessStabilityPropertiesRemark (S : System.{u}) : Prop :=
  IsTopologicalSystem S ->
  (∀ d : S.X -> S.X -> ℝ, IsCompatibleMetric S d ->
    (IsExpansiveForDistance S d ↔ HasCompatibleExpansiveMetric S)) ∧
  (∀ inv : S.X -> S.X, IsContinuousInverse S inv ->
    ∀ k : ℤ, k ≠ 0 ->
      (HasCompatibleExpansiveMetric S ↔
        HasCompatibleExpansiveMetric (integerIterateSystem S inv k))) ∧
  (∀ R : System.{u}, IsTopologicallyConjugate S R ->
    (HasCompatibleExpansiveMetric S ↔ HasCompatibleExpansiveMetric R)) ∧
  (∀ R : System.{u}, ∀ ι : R.X -> S.X,
    IsTopologicalSubsystem S R ι ->
      HasCompatibleExpansiveMetric S -> HasCompatibleExpansiveMetric R) ∧
  (∀ n : ℕ, ∀ family : Fin n -> System.{u},
    (∀ i, IsTopologicalSystem (family i) ∧
      HasCompatibleExpansiveMetric (family i)) ->
      HasCompatibleExpansiveMetric (finiteProductTopologicalSystem family)) ∧
  ∃ family : ℕ -> System.{0},
    (∀ n, IsTopologicalSystem (family n) ∧
      HasCompatibleExpansiveMetric (family n)) ∧
    IsTopologicalSystem (countableProductTopologicalSystem family) ∧
    ¬ HasCompatibleExpansiveMetric (countableProductTopologicalSystem family)

/--
Source: Remark 5.7.9, Chapter 5, Section 7.
For noninvertible continuous maps one uses positive expansiveness, asking only
for positive-time separation.
-/
def positiveExpansiveness (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x y : S.X, x ≠ y -> ∃ n : ℕ,
    dist ((S.T^[n]) x) ((S.T^[n]) y) > δ

def IsUnimodularIntegerMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) ℤ, A * B = 1 ∧ B * A = 1

def HasUnitModulusEigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ eig : ℂ, ‖eig‖ = 1 ∧ ∃ v : Fin n -> ℂ, v ≠ 0 ∧
    Matrix.mulVec (fun i j => (A i j : ℂ)) v = fun i => eig * v i

def toralMatrixMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Section02.Torus n -> Section02.Torus n :=
  fun x i => ∑ j, (A i j) • x j

def toralMatrixSystem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : System where
  X := Section02.Torus n
  topology := inferInstance
  T := toralMatrixMap A

/-- The antipodal equivalence relation used to identify `𝕋²/{±1}` with the
two-sphere in Example 5.7.10. -/
def torusAntipodalRelation (x y : Section02.Torus 2) : Prop :=
  y = x ∨ y = -x

abbrev TwoSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/--
Source: Example 5.7.10, Chapter 5, Section 7.
An expansive toral automorphism can have a nonexpansive factor on a quotient
sphere.
-/
theorem expansiveFactorNeedNotBeExpansiveTorusSphereExample
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    IsUnimodularIntegerMatrix A -> ¬ HasUnitModulusEigenvalue A ->
    ∃ R : System.{0}, ∃ π : (toralMatrixSystem A).X -> R.X,
      IsFactorMap (toralMatrixSystem A) R π ∧
      (∀ x y, π x = π y ↔ torusAntipodalRelation x y) ∧
      Nonempty (R.X ≃ₜ TwoSphere) ∧
      HasCompatibleExpansiveMetric (toralMatrixSystem A) ∧
      ¬ HasCompatibleExpansiveMetric R := by
  sorry

/--
Source: Example 5.7.11, Chapter 5, Section 7.
A symbolic extension built from an irrational rotation gives another example
where expansiveness need not descend to factors.
-/
theorem expansiveFactorNeedNotBeExpansiveRotationCodingExample
    (α : ℝ) (hα : Irrational α) :
    ∃ Λ : System.{0},
      IsSturmianSystem Λ α ∧
      HasCompatibleExpansiveMetric Λ ∧
      (∃ π : Λ.X -> (circleRotationTopologicalSystem α).X,
        IsFactorMap Λ (circleRotationTopologicalSystem α) π) ∧
      ¬ HasCompatibleExpansiveMetric (circleRotationTopologicalSystem α) := by
  sorry

/--
Source: Theorem 5.7.12, Chapter 5, Section 7.
For an expansive homeomorphism, every finite cover of diameter below an
expansive constant has iterated joins whose diameters tend to zero.
-/
theorem expansiveSmallCoverJoinDiametersTendToZero
    (S : System.{u}) [PseudoMetricSpace S.X] (γ : Set (Set S.X))
    (inv : S.X -> S.X) (δ : ℝ) :
    IsCompactTopologicalSystem S -> IsExpansiveWithConstant S inv δ ->
    Set.Finite γ -> ⋃₀ γ = Set.univ ->
    (∀ C ∈ γ, Metric.diam C < δ) -> coverJoinDiameterTendsToZero S γ := by
  sorry

/--
Source: Theorem 5.7.13, Chapter 5, Section 7.
Every expansive compact metric homeomorphism is a factor of a subshift over a
finite alphabet.
-/
theorem expansiveSystemHasSubshiftExtension
    (S : System.{u}) [PseudoMetricSpace S.X] :
    IsCompactTopologicalSystem S -> IsExpansive S -> IsSubshiftExtensionOf S := by
  sorry

/--
Source: Example 5.7.14, Chapter 5, Section 7.
Equicontinuous systems are nonexpansive unless finite; toral automorphisms are
expansive exactly when no eigenvalue has modulus one; every subshift is
expansive.
-/
def expansiveSystemExamplesRemark : Prop :=
  (∀ S : System.{u}, ∀ d : S.X -> S.X -> ℝ,
    IsCompatibleMetric S d -> IsEquicontinuousForDistance S d ->
      (Set.Finite (Set.univ : Set S.X) ∨ ¬ IsExpansiveForDistance S d)) ∧
  (∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℤ,
    IsUnimodularIntegerMatrix A ->
      ((∃ d : (toralMatrixSystem A).X -> (toralMatrixSystem A).X -> ℝ,
          IsCompatibleMetric (toralMatrixSystem A) d ∧
          IsExpansiveForDistance (toralMatrixSystem A) d) ↔
        ¬ HasUnitModulusEigenvalue A)) ∧
  ∀ k : ℕ, ∀ S : System.{u}, IsSubshift S k ->
    ∃ d : S.X -> S.X -> ℝ,
      IsCompatibleMetric S d ∧ IsExpansiveForDistance S d

/-- The dynamical system associated to a self-homeomorphism. -/
def homeomorphismSystem {X : Type u} [TopologicalSpace X]
    (T : X ≃ₜ X) : System.{u} where
  X := X
  topology := inferInstance
  T := T

/-- A topological space admits an expansive homeomorphism, with expansiveness
measured by some metric inducing its given topology. -/
def AdmitsExpansiveHomeomorphism (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ T : X ≃ₜ X, HasCompatibleExpansiveMetric (homeomorphismSystem T)

/-- A compact topological one-manifold, allowing boundary. -/
def IsCompactOneManifold (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 1) X] : Prop :=
  IsCompact (Set.univ : Set X) ∧ Nonempty X ∧ IsManifold (𝓡∂ 1) 0 X

/-- A compact two-manifold whose manifold boundary is nonempty. -/
def IsCompactSurfaceWithBoundary (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 2) X] : Prop :=
  IsCompact (Set.univ : Set X) ∧ Nonempty ((𝓡∂ 2).boundary X) ∧
    IsManifold (𝓡∂ 2) 0 X

/-- A closed connected topological surface. -/
def IsClosedSurface (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] : Prop :=
  IsCompact (Set.univ : Set X) ∧ Nonempty X ∧ ConnectedSpace X ∧
    TopologicalSpace.MetrizableSpace X ∧ IsManifold (𝓡 2) 0 X

/-- A finite two-dimensional simplicial complex, presented by its triangular
facets.  Its realization below ties the combinatorics to the surface rather
than treating genus as an unrelated numerical label. -/
structure FiniteTriangularComplex where
  vertexCount : ℕ
  triangles : Finset (Finset (Fin vertexCount))
  triangle_card : ∀ τ ∈ triangles, τ.card = 3
  vertex_used : ∀ i : Fin vertexCount, ∃ τ ∈ triangles, i ∈ τ

namespace FiniteTriangularComplex

/-- The edges occurring in the triangular facets. -/
def edges (K : FiniteTriangularComplex) : Finset (Finset (Fin K.vertexCount)) :=
  Finset.univ.filter fun e =>
    e.card = 2 ∧ ∃ τ ∈ K.triangles, e ⊆ τ

/-- The ordinary barycentric geometric realization. -/
abbrev Realization (K : FiniteTriangularComplex) :=
  {x : Fin K.vertexCount -> ℝ //
    (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
      ∃ τ ∈ K.triangles, ∀ i, x i ≠ 0 -> i ∈ τ}

/-- The combinatorial Euler characteristic `V - E + F`. -/
def eulerCharacteristic (K : FiniteTriangularComplex) : ℤ :=
  (K.vertexCount : ℤ) - (K.edges.card : ℤ) + (K.triangles.card : ℤ)

/-- A cyclic ordering of the vertices of one triangular facet. -/
abbrev TriangleOrdering (K : FiniteTriangularComplex)
    (τ : {τ // τ ∈ K.triangles}) := Fin 3 ≃ τ.1

/-- The directed edge relation induced by a cyclic ordering of a triangle. -/
def OrientsEdge {K : FiniteTriangularComplex}
    {τ : {τ // τ ∈ K.triangles}} (o : K.TriangleOrdering τ)
    (a b : Fin K.vertexCount) : Prop :=
  ((o 0 : Fin K.vertexCount) = a ∧ (o 1 : Fin K.vertexCount) = b) ∨
  ((o 1 : Fin K.vertexCount) = a ∧ (o 2 : Fin K.vertexCount) = b) ∨
  ((o 2 : Fin K.vertexCount) = a ∧ (o 0 : Fin K.vertexCount) = b)

/-- Coherent orientations give opposite directions to every edge shared by
two distinct triangles. -/
def IsCoherentOrientation (K : FiniteTriangularComplex)
    (o : ∀ τ : {τ // τ ∈ K.triangles}, K.TriangleOrdering τ) : Prop :=
  ∀ τ σ : {τ // τ ∈ K.triangles}, τ ≠ σ ->
    ∀ a b : Fin K.vertexCount, a ≠ b ->
      a ∈ τ.1 -> b ∈ τ.1 -> a ∈ σ.1 -> b ∈ σ.1 ->
        OrientsEdge (o τ) a b ↔ OrientsEdge (o σ) b a

end FiniteTriangularComplex

/-- A closed surface is orientable of genus `g` when it has a coherently
oriented finite triangulation with Euler characteristic `2 - 2g`. -/
def IsOrientableSurfaceOfGenus (X : Type u) [TopologicalSpace X]
    (g : ℕ) : Prop :=
  ∃ K : FiniteTriangularComplex,
    Nonempty (X ≃ₜ K.Realization) ∧
    (∃ o : ∀ τ : {τ // τ ∈ K.triangles}, K.TriangleOrdering τ,
      K.IsCoherentOrientation o) ∧
    K.eulerCharacteristic = 2 - 2 * (g : ℤ)

/-- The metric axioms without point separation.  Stable and unstable
transverse measures of a pseudo-Anosov map induce such pseudodistances. -/
def IsPseudoDistance {X : Type u} (d : X -> X -> ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧
  (∀ x y, d x y = d y x) ∧
  ∀ x y z, d x z ≤ d x y + d y z

/-- A concrete metric/measured-foliation interface for a pseudo-Anosov
homeomorphism: the stable and unstable transverse pseudodistances scale by
reciprocal factors, and their sum is a compatible metric. -/
def IsPseudoAnosovHomeomorphism {X : Type u} [TopologicalSpace X]
    (T : X ≃ₜ X) : Prop :=
  ∃ stretch : ℝ, 1 < stretch ∧
  ∃ stable unstable : X -> X -> ℝ,
    IsPseudoDistance stable ∧ IsPseudoDistance unstable ∧
    IsCompatibleMetric (homeomorphismSystem T)
      (fun x y => stable x y + unstable x y) ∧
    (∀ x y, stable (T x) (T y) = stretch⁻¹ * stable x y) ∧
    ∀ x y, unstable (T x) (T y) = stretch * unstable x y

/-- The orbit setoid of an involution. -/
def involutionSetoid {X : Type u} (τ : X -> X)
    (hτ : Function.Involutive τ) : Setoid X where
  r x y := y = x ∨ y = τ x
  iseqv := by
    constructor
    · intro x
      exact Or.inl rfl
    · intro x y hxy
      rcases hxy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (hτ x).symm
    · intro x y z hxy hyz
      rcases hxy with rfl | rfl <;> rcases hyz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (hτ x)

/-- The antipodal involution of the unit two-sphere. -/
noncomputable def twoSphereAntipodal : TwoSphere -> TwoSphere :=
  fun x => ⟨-x.1, by simp [TwoSphere]⟩

theorem twoSphereAntipodal_involutive :
    Function.Involutive twoSphereAntipodal := by
  intro x
  ext i
  simp [twoSphereAntipodal]

/-- The real projective plane `S²/{x ∼ -x}`. -/
abbrev RealProjectivePlane :=
  Quotient (involutionSetoid twoSphereAntipodal twoSphereAntipodal_involutive)

/-- The fixed-point-free involution `(x,y) ↦ (x+1/2,-y)` on the two-torus. -/
noncomputable def kleinBottleInvolution :
    Section02.Torus 2 -> Section02.Torus 2 :=
  fun x i => if i = 0 then x i + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) else -x i

theorem kleinBottleInvolution_involutive :
    Function.Involutive kleinBottleInvolution := by
  intro x
  funext i
  fin_cases i
  · simp [kleinBottleInvolution]
    rw [add_assoc, ← AddCircle.coe_add]
    norm_num
  · simp [kleinBottleInvolution]

/-- The Klein bottle as the quotient of the two-torus by the standard free
involution `(x,y) ↦ (x+1/2,-y)`. -/
abbrev KleinBottle :=
  Quotient (involutionSetoid kleinBottleInvolution kleinBottleInvolution_involutive)

/--
Source: Remark 5.7.15, Chapter 5, Section 7.
The five conjuncts preserve, in order, every mathematical assertion in the
remark: the one-dimensional obstruction, the boundary obstruction, the
positive-genus orientable existence theorem, the closed-surface classification,
and the three named exceptional surfaces.
-/
def expansiveHomeomorphismManifoldExistenceRemark : Prop :=
  (∀ (X : Type u) [TopologicalSpace X]
      [ChartedSpace (EuclideanHalfSpace 1) X],
      IsCompactOneManifold X -> ¬ AdmitsExpansiveHomeomorphism X) ∧
  (∀ (X : Type u) [TopologicalSpace X]
      [ChartedSpace (EuclideanHalfSpace 2) X],
      IsCompactSurfaceWithBoundary X -> ¬ AdmitsExpansiveHomeomorphism X) ∧
  (∀ (X : Type u) [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X],
      IsClosedSurface X -> ∀ g : ℕ, 0 < g ->
        IsOrientableSurfaceOfGenus X g -> AdmitsExpansiveHomeomorphism X) ∧
  (∀ (X : Type u) [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X],
      IsClosedSurface X -> ∀ T : X ≃ₜ X,
        HasCompatibleExpansiveMetric (homeomorphismSystem T) ->
        ∃ P : X ≃ₜ X, IsPseudoAnosovHomeomorphism P ∧
          IsTopologicallyConjugate (homeomorphismSystem T) (homeomorphismSystem P)) ∧
  ¬ AdmitsExpansiveHomeomorphism TwoSphere ∧
  ¬ AdmitsExpansiveHomeomorphism RealProjectivePlane ∧
  ¬ AdmitsExpansiveHomeomorphism KleinBottle

/-- Source: the final, literature-status sentence of Remark 5.7.15.  It is
narrative rather than a truth-valued theorem, so it is kept separately from the
five mathematical conjuncts above. -/
def expansiveHomeomorphismHigherDimensionalLiteratureStatus : String :=
  "The higher-dimensional case is more complicated, and only partial results are known."

/--
Source: Theorem 5.7.16, Chapter 5, Section 7.
For an expansive homeomorphism, the fixed point set of every positive iterate is
finite.
-/
theorem expansiveHomeomorphismHasFinitePeriodicPointSets
    (S : System.{u}) [PseudoMetricSpace S.X] (p : ℕ) :
    IsCompactTopologicalSystem S -> IsExpansive S -> 0 < p ->
      Set.Finite (fixedPointSet { S with T := S.T^[p] }) := by
  sorry

/--
Source: Theorem 5.7.17, Chapter 5, Section 7.
No closed interval admits an expansive homeomorphism.
-/
theorem closedIntervalHasNoExpansiveHomeomorphism
    (T : Set.Icc (0 : ℝ) 1 ≃ₜ Set.Icc (0 : ℝ) 1) :
    ¬ IsExpansive
      ({ X := Set.Icc (0 : ℝ) 1, topology := inferInstance, T := T } : System) := by
  sorry

/--
Source: Theorem 5.7.18, Chapter 5, Section 7.
The circle admits no expansive homeomorphism.
-/
theorem circleHasNoExpansiveHomeomorphism (T : Circle ≃ₜ Circle) :
    ¬ IsExpansive ({ X := Circle, topology := inferInstance, T := T } : System) := by
  sorry

end Section07

-- Preserve the chapter-level public names used by later chapters while the
-- heavier declarations themselves remain in the small Section 5.7 module.
abbrev IsExpansiveForDistance := Section07.IsExpansiveForDistance
abbrev IsExpansive := Section07.IsExpansive
abbrev IsExpansiveWithConstant := Section07.IsExpansiveWithConstant
abbrev IsSensitive := Section07.IsSensitive
abbrev IsGeneratorCover := Section07.IsGeneratorCover
abbrev IsWeakGeneratorCover := Section07.IsWeakGeneratorCover
abbrev HasGenerator := Section07.HasGenerator
abbrev HasWeakGenerator := Section07.HasWeakGenerator
abbrev coverJoinDiameterTendsToZero := Section07.coverJoinDiameterTendsToZero
abbrev IsSubshiftExtensionOf := Section07.IsSubshiftExtensionOf
abbrev IsSubshift := Section07.IsSubshift

end Chapter05
