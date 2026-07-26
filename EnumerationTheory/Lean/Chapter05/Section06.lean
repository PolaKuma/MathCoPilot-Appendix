import Chapter05.Section05

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter05

universe u v w

namespace Section06


/-- Source: Definition 5.6.1, Chapter 5, Section 6. -/
def equicontinuousSystem (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsEquicontinuous S

/--
Source: Definition 5.6.1, Chapter 5, Section 6.
For an equicontinuous system, the supremum orbit metric is equivalent to the
original metric and is invariant under the dynamics.
-/
def orbitSupMetricRemark (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  Function.Surjective S.T -> IsEquicontinuous S ->
    IsCompatibleInvariantMetric S (orbitSupDistance S)

/--
Source: Example 5.6.2, Chapter 5, Section 6.
Circle rotations and adding machines are equicontinuous systems.
-/
theorem basicEquicontinuousExamples :
    (∀ α : ℝ, ∃ d : (circleRotationTopologicalSystem α).X ->
        (circleRotationTopologicalSystem α).X -> ℝ,
      IsCompatibleMetric (circleRotationTopologicalSystem α) d ∧
        IsEquicontinuousForDistance (circleRotationTopologicalSystem α) d) ∧
    ∃ d : addingMachineTopologicalSystem.X -> addingMachineTopologicalSystem.X -> ℝ,
      IsCompatibleMetric addingMachineTopologicalSystem d ∧
        IsEquicontinuousForDistance addingMachineTopologicalSystem d := by
  sorry

/-- Source: Definition 5.6.3, Chapter 5, Section 6. -/
def uniformlyAlmostPeriodicSystem (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsUniformlyAlmostPeriodic S

/--
Source: Theorem 5.6.4, Chapter 5, Section 6.
A topological dynamical system is equicontinuous iff it is uniformly almost
periodic.
-/
theorem equicontinuousIffUniformlyAlmostPeriodic
    (S : System.{u}) [PseudoMetricSpace S.X] :
    IsCompactTopologicalSystem S -> Function.Surjective S.T ->
      (IsEquicontinuous S ↔ IsUniformlyAlmostPeriodic S) := by
  sorry

/-- Source: Definition 5.6.5, Chapter 5, Section 6. -/
def topologicalEigenfunction (S : System.{u}) (lam : ℂ) (f : S.X -> ℂ) : Prop :=
  IsTopologicalEigenfunction S lam f

/-- Source: Definition 5.6.5, Chapter 5, Section 6. -/
def topologicalEigenvalue (S : System.{u}) (lam : ℂ) : Prop :=
  lam ∈ topologicalEigenvalueSet S

/--
Source: Proposition 5.6.6, Chapter 5, Section 6.
For a transitive system, eigenvalues have modulus one, eigenfunctions with the
same eigenvalue differ by a scalar, eigenfunctions for distinct eigenvalues are
linearly independent, and the eigenvalues form a countable subgroup of the
circle.
-/
theorem transitiveSystemEigenfunctionProperties (S : System.{u}) :
    IsCompactTopologicalSystem S -> IsTopologicallyTransitive S ->
      (∀ lam : ℂ, ∀ f : S.X -> ℂ, IsTopologicalEigenfunction S lam f ->
        ‖lam‖ = 1 ∧ ∃ c : ℝ, 0 < c ∧ ∀ x : S.X, ‖f x‖ = c) ∧
      (∀ lam : ℂ, ∀ f g : S.X -> ℂ,
        IsTopologicalEigenfunction S lam f -> IsTopologicalEigenfunction S lam g ->
        ∃ c : ℂ, f = fun x => c * g x) ∧
      (∀ m : ℕ, ∀ lam : Fin m -> ℂ, ∀ f : Fin m -> S.X -> ℂ,
        Function.Injective lam ->
        (∀ i, IsTopologicalEigenfunction S (lam i) (f i)) ->
        LinearIndependent ℂ f) ∧
      Set.Countable (topologicalEigenvalueSet S) ∧
      1 ∈ topologicalEigenvalueSet S ∧
      (∀ a ∈ topologicalEigenvalueSet S, ∀ b ∈ topologicalEigenvalueSet S,
        a * b ∈ topologicalEigenvalueSet S) ∧
      (∀ a ∈ topologicalEigenvalueSet S, a⁻¹ ∈ topologicalEigenvalueSet S) ∧
      topologicalEigenvalueSet S ⊆ {z : ℂ | ‖z‖ = 1} := by
  sorry

/-- Source: Definition 5.6.7, Chapter 5, Section 6. -/
def topologicalDiscreteSpectrum (S : System.{u}) : Prop :=
  HasTopologicalDiscreteSpectrum S

/--
Source: Theorem 5.6.8, Chapter 5, Section 6.
Halmos-von Neumann theorem for reversible topological systems: minimal
equicontinuity, transitive isometry models, minimal compact abelian rotations,
and topological discrete spectrum are equivalent.
-/
theorem topologicalHalmosVonNeumannTheorem
    (S : System.{u}) [PseudoMetricSpace S.X] :
    IsCompactTopologicalSystem S ->
    (∃ inv : S.X -> S.X, IsContinuousInverse S inv) ->
    let minimalEquicontinuous := IsMinimalSystem S ∧ IsEquicontinuous S
    let transitiveIsometry := IsTopologicallyTransitive S ∧
      ∃ ρ : S.X -> S.X -> ℝ,
        (∀ x y, 0 ≤ ρ x y) ∧
        (∀ x y, ρ x y = 0 ↔ x = y) ∧
        (∀ x y, ρ x y = ρ y x) ∧
        (∀ x y z, ρ x z ≤ ρ x y + ρ y z) ∧
        (∀ U : Set S.X, IsOpen U ↔
          ∀ x ∈ U, ∃ ε : ℝ, 0 < ε ∧ {y : S.X | ρ x y < ε} ⊆ U) ∧
        ∀ x y, ρ (S.T x) (S.T y) = ρ x y
    let minimalRotation := IsCompactGroupRotationModel S
    let minimalDiscrete := IsMinimalSystem S ∧ HasTopologicalDiscreteSpectrum S
    let transitiveDiscrete := IsTopologicallyTransitive S ∧ HasTopologicalDiscreteSpectrum S
    (minimalEquicontinuous ↔ transitiveIsometry) ∧
    (transitiveIsometry ↔ minimalRotation) ∧
    (minimalRotation ↔ minimalDiscrete) ∧
    (minimalDiscrete ↔ transitiveDiscrete) := by
  sorry

/-- Source: Definition 5.6.9, Chapter 5, Section 6. -/
def proximalPairDefinition (S : System.{u}) [PseudoMetricSpace S.X] (x y : S.X) : Prop :=
  proximalPair S x y

/-- Source: Definition 5.6.9, Chapter 5, Section 6. -/
def asymptoticPairDefinition (S : System.{u}) [PseudoMetricSpace S.X] (x y : S.X) : Prop :=
  asymptoticPair S x y

/-- Source: Definition 5.6.9, Chapter 5, Section 6. -/
def distalSystem (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsDistalSystem S

/-- Source: Definition 5.6.9, Chapter 5, Section 6. -/
def equicontinuousExtension (S R : System.{u}) [PseudoMetricSpace S.X] [PseudoMetricSpace R.X]
    (π : S.X -> R.X) : Prop :=
  IsEquicontinuousExtension S R π

/-- Metric-free packaging of an equicontinuous extension.  The two displayed
distance functions are required to induce the already stored topologies. -/
def IsEquicontinuousExtensionForDistances (S₁ : System.{u}) (S₂ : System.{u})
    (π : S₁.X -> S₂.X) (d₁ : S₁.X -> S₁.X -> ℝ)
    (d₂ : S₂.X -> S₂.X -> ℝ) : Prop :=
  IsFactorMap S₁ S₂ π ∧ IsCompatibleMetric S₁ d₁ ∧
  IsCompatibleMetric S₂ d₂ ∧
  ∃ inv₁ : S₁.X -> S₁.X, IsContinuousInverse S₁ inv₁ ∧
  ∃ inv₂ : S₂.X -> S₂.X, IsContinuousInverse S₂ inv₂ ∧
  ∀ ε : ℝ, 0 < ε -> ∃ δ : ℝ, 0 < δ ∧ ∀ x y : S₁.X,
    π x = π y -> d₁ x y < δ -> ∀ n : ℤ,
      d₁ (ziterate S₁ inv₁ n x) (ziterate S₁ inv₁ n y) < ε

/-- A complete transfinite inverse system as used in Theorem 5.6.10.  The
successor maps are equicontinuous extensions, while every limit stage is the
topological inverse limit of all earlier stages. -/
structure EquicontinuousExtensionTower (final : Ordinal.{0}) where
  system : Ordinal.{0} -> System.{u}
  factorMap : ∀ ξ ξ' : Ordinal.{0}, (system ξ').X -> (system ξ).X
  topological : ∀ ξ, ξ ≤ final -> IsTopologicalSystem (system ξ)
  bottom_trivial : Subsingleton (system 0).X
  factor : ∀ ξ ξ', ξ ≤ ξ' -> ξ' ≤ final ->
    IsFactorMap (system ξ') (system ξ) (factorMap ξ ξ')
  identity : ∀ ξ, ξ ≤ final -> factorMap ξ ξ = id
  composition : ∀ ξ ξ' ξ'', ξ ≤ ξ' -> ξ' ≤ ξ'' -> ξ'' ≤ final ->
    factorMap ξ ξ'' = factorMap ξ ξ' ∘ factorMap ξ' ξ''
  successor : ∀ ξ, ξ < final ->
    ∃ d₁ d₂,
      IsEquicontinuousExtensionForDistances (system (ξ + 1)) (system ξ)
        (factorMap ξ (ξ + 1)) d₁ d₂
  limit_compatible : ∀ limit, limit ≤ final -> limit ≠ 0 ->
    (∀ ξ, ξ < limit -> ξ + 1 < limit) ->
    ∀ x : (system limit).X,
    ∀ (ξ ξ' : { ξ : Ordinal.{0} // ξ < limit }), ξ.1 ≤ ξ'.1 ->
      factorMap ξ.1 ξ'.1 (factorMap ξ'.1 limit x) = factorMap ξ.1 limit x
  limit_separates : ∀ limit, limit ≤ final -> limit ≠ 0 ->
    (∀ ξ, ξ < limit -> ξ + 1 < limit) ->
    ∀ x y : (system limit).X,
      (∀ ξ : { ξ : Ordinal.{0} // ξ < limit },
        factorMap ξ.1 limit x = factorMap ξ.1 limit y) -> x = y
  limit_surjective : ∀ limit, limit ≤ final -> limit ≠ 0 ->
    (∀ ξ, ξ < limit -> ξ + 1 < limit) ->
    ∀ thread : ∀ ξ : { ξ : Ordinal.{0} // ξ < limit }, (system ξ.1).X,
      (∀ (ξ ξ' : { ξ : Ordinal.{0} // ξ < limit }), ξ.1 ≤ ξ'.1 ->
        factorMap ξ.1 ξ'.1 (thread ξ') = thread ξ) ->
      ∃ x : (system limit).X, ∀ ξ, factorMap ξ.1 limit x = thread ξ
  limit_topology : ∀ limit, limit ≤ final -> limit ≠ 0 ->
    (∀ ξ, ξ < limit -> ξ + 1 < limit) ->
    TopologicalSpace.induced
      (fun x : (system limit).X =>
        fun ξ : { ξ : Ordinal.{0} // ξ < limit } => factorMap ξ.1 limit x)
      inferInstance = (system limit).topology

def IsInverseLimitOfEquicontinuousExtensions
    (S : System.{u}) [PseudoMetricSpace S.X] : Prop :=
  IsCompatibleMetric S dist ∧
  ∃ α : Ordinal.{0}, ∃ tower : EquicontinuousExtensionTower.{u} α,
    tower.system α = S

/--
Source: Theorem 5.6.10, Chapter 5, Section 6.
Furstenberg structure theorem: a minimal system is distal iff it is an inverse
limit of equicontinuous extensions.
-/
theorem furstenbergDistalStructureTheorem
    (S : System.{u}) [PseudoMetricSpace S.X] :
    IsCompactTopologicalSystem S -> IsMinimalSystem S ->
      (IsDistalSystem S ↔ IsInverseLimitOfEquicontinuousExtensions S) := by
  sorry

end Section06
end Chapter05
