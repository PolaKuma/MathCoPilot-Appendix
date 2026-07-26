import Chapter06.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter06

universe u v w

namespace Section01


/--
Source: Proposition 6.1.1, Chapter 6, Section 1.
Every Borel probability measure on a metric space is regular.
-/
theorem metricSpaceProbabilityMeasuresAreRegular
    {X : Type u} [PseudoMetricSpace X] (μ : MeasureOn X) :
    IsProbabilityBorelMeasure μ -> IsRegularMeasure μ := by
  sorry

/--
Source: Corollary 6.1.2, Chapter 6, Section 1.
On a metric space, the measure of a Borel set is recovered as the supremum over
closed subsets and the infimum over open supersets.
-/
theorem regularMeasureInnerOuterValues
    {X : Type u} [PseudoMetricSpace X] (μ : MeasureOn X) (B : Set X) :
    @MeasurableSet X (borel X) B -> IsRegularMeasure μ ->
      μ.measure B = innerRegularValue μ B ∧
      μ.measure B = outerRegularValue μ B := by
  sorry

/--
Source: Proposition 6.1.3, Chapter 6, Section 1.
Two probability measures on a metric space agree iff their integrals agree on
every continuous function.
-/
theorem measuresEqualIffContinuousIntegralsEqual
    {X : Type u} [PseudoMetricSpace X] (μ ν : MeasureOn X) :
    IsProbabilityBorelMeasure μ -> IsProbabilityBorelMeasure ν ->
      (μ = ν ↔ MeasuresAgreeOnContinuousFunctions μ ν) := by
  sorry

/--
Source: Theorem 6.1.4, Chapter 6, Section 1.
Riesz representation identifies probability measures on a compact metric space
with normalized positive functionals on `C(X)`.
-/
theorem rieszRepresentationForProbabilityMeasures
    {X : Type u} [MetricSpace X] [CompactSpace X] :
    IsRieszCorrespondence (X := X) := by
  sorry

/-- A standard finite-test-function basic weak-star neighborhood. -/
def weakStarBasicNeighborhood {X : Type u} [TopologicalSpace X]
    (μ : MeasureOn X) (F : Finset C(X, ℂ)) (ε : ℝ) : Set (MeasureOn X) :=
  {ν | ∀ f ∈ F, ‖μ.integral f - ν.integral f‖ < ε}

/--
Source: Theorem 6.1.4, Chapter 6, Section 1.
Weak-star convergence of measures is convergence of integrals against every
continuous test function, and finite families of test functions give a
neighborhood basis.
-/
def weakStarTopologyOnMeasuresRemark {X : Type u} [TopologicalSpace X] : Prop :=
  (∀ μn : ℕ -> MeasureOn X, ∀ μ : MeasureOn X,
    Tendsto μn atTop (nhds μ) ↔ weakStarConverges μn μ) ∧
  ∀ μ : MeasureOn X, ∀ V : Set (MeasureOn X),
    V ∈ nhds μ ↔ ∃ F : Finset C(X, ℂ), ∃ ε : ℝ, 0 < ε ∧
      weakStarBasicNeighborhood μ F ε ⊆ V

theorem weakStarTopologyOnMeasuresRemark_holds
    {X : Type u} [TopologicalSpace X] :
    weakStarTopologyOnMeasuresRemark (X := X) := by
  sorry

/--
Source: Theorem 6.1.5, Chapter 6, Section 1.
For compact metric `X`, the weak-star space of probability measures is compact
and metrizable, with a compatible metric obtained from a countable dense family
in `C(X)`.
-/
theorem weakStarMeasureSpaceCompactMetrizable
    {X : Type u} [MetricSpace X] [CompactSpace X] :
    IsCompact {μ : MeasureOn X | IsProbabilityBorelMeasure μ} ∧
      ∃ P : MeasureOn X -> MeasureOn X -> ℝ, CompatibleMeasureMetric P := by
  sorry

/--
Source: Proposition 6.1.6, Chapter 6, Section 1.
The Dirac map `x ↦ δ_x` is a topological embedding into the measure space.
-/
theorem diracMapIsTopologicalEmbedding
    {X : Type u} [MetricSpace X] [CompactSpace X] :
    IsTopologicalEmbedding (diracEmbedding : X -> MeasureOn X) := by
  sorry

/--
Source: Theorem 6.1.7, Chapter 6, Section 1.
Portmanteau theorem: weak-star convergence is equivalent to closed-set upper
bounds, open-set lower bounds, and convergence on continuity sets.
-/
theorem portmanteauTheorem
    {X : Type u} [PseudoMetricSpace X]
    (μn : ℕ -> MeasureOn X) (μ : MeasureOn X) :
    (∀ n, IsProbabilityBorelMeasure (μn n)) -> IsProbabilityBorelMeasure μ ->
      PortmanteauEquivalent μn μ := by
  sorry

/--
Source: Lemma 6.1.8, Chapter 6, Section 1.
A continuous map induces a continuous affine push-forward on probability
measures, and this push-forward is onto exactly when the original map is onto.
-/
theorem pushForwardContinuousAffineSurjectiveIff
    {X : Type u} {Y : Type v} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [CompactSpace Y]
    (φ : X -> Y) :
    Continuous φ ->
      IsAffineMap (pushForwardMeasure φ : MeasureOn X -> MeasureOn Y) ∧
      (Function.Surjective φ ↔
        ∀ ν : MeasureOn Y, IsProbabilityBorelMeasure ν ->
          ∃ μ : MeasureOn X, IsProbabilityBorelMeasure μ ∧ pushForwardMeasure φ μ = ν) := by
  sorry

end Section01
end Chapter06
