import Chapter02.HallPetresco.HallPetrescoLattice
import Mathlib.MeasureTheory.Measure.Prokhorov

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoMeasureOrbit

universe u v

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoLattice

/-- Coordinatewise progression shift
`(x₀,x₁,x₂,x₃) ↦ (x₀,T x₁,T² x₂,T³ x₃)`. -/
def progressionStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (y : Vertex → X) : Vertex → X :=
  fun j ↦ (N.nilrotation^[j.val]) (y j)

theorem continuous_progressionStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (progressionStep N) := by
  rw [continuous_pi_iff]
  intro j
  exact (N.continuous_nilrotation.iterate j.val).comp
    (continuous_apply j)

/-- The canonical configuration map from the actual Hall--Petresco quotient
intertwines quotient translation by the progression generator with the
coordinatewise progression step. -/
theorem quotientConfiguration_quotientStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : Quotient N P.lattice) :
    quotientConfiguration N P
        (quotientStep N P.lattice q) =
      progressionStep N (quotientConfiguration N P q) := by
  change quotientConfiguration N P (progressionGenerator N • q) =
    progressionStep N (quotientConfiguration N P q)
  rw [quotientConfiguration_smul]
  funext j
  change N.ambientAction.toMulAction.smul
      (N.translation ^ j.val) (quotientConfiguration N P q j) =
    (N.nilrotation^[j.val]) (quotientConfiguration N P q j)
  rw [N.nilrotation_iterate]

/-- Push a probability measure on the actual Hall--Petresco quotient to
the corresponding probability measure on four configurations. -/
def quotientConfigurationMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (ν : ProbabilityMeasure (Quotient N P.lattice)) :
    ProbabilityMeasure (Vertex → X) :=
  ν.map (continuous_quotientConfiguration N P).measurable.aemeasurable

theorem continuous_quotientConfigurationMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)] :
    Continuous (quotientConfigurationMeasure N P) :=
  ProbabilityMeasure.continuous_map
    (continuous_quotientConfiguration N P)

/-- The diagonal embedding used to turn the base probability measure into
a probability measure on four configurations. -/
def diagonalMap {X : Type v} (x : X) : Vertex → X :=
  fun _ ↦ x

theorem continuous_diagonalMap
    {X : Type v} [TopologicalSpace X] :
    Continuous (diagonalMap : X → Vertex → X) := by
  rw [continuous_pi_iff]
  intro _
  exact continuous_id

/-- The diagonal probability measure on four configurations. -/
def diagonalMeasure
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ProbabilityMeasure (Vertex → X) :=
  ProbabilityMeasure.map
    (⟨μ, inferInstance⟩ : ProbabilityMeasure X)
    continuous_diagonalMap.measurable.aemeasurable

/-- Push a configuration measure forward by one progression step. -/
def measureStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (ν : ProbabilityMeasure (Vertex → X)) :
    ProbabilityMeasure (Vertex → X) :=
  ν.map (continuous_progressionStep N).measurable.aemeasurable

theorem continuous_measureStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    Continuous (measureStep N) :=
  ProbabilityMeasure.continuous_map (continuous_progressionStep N)

/-- The configuration-measure map is equivariant: quotient translation
pushforward becomes the established progression-measure step. -/
theorem quotientConfigurationMeasure_map_quotientStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (ν : ProbabilityMeasure (Quotient N P.lattice)) :
    quotientConfigurationMeasure N P
        (ν.map (continuous_quotientStep N P.lattice).measurable.aemeasurable) =
      measureStep N (quotientConfigurationMeasure N P ν) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [quotientConfigurationMeasure, measureStep,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (continuous_quotientConfiguration N P).measurable
    (continuous_quotientStep N P.lattice).measurable]
  rw [Measure.map_map
    (continuous_progressionStep N).measurable
    (continuous_quotientConfiguration N P).measurable]
  congr 1
  funext q
  exact quotientConfiguration_quotientStep N P q

/-- The product of a continuous observation over the four coordinates. -/
def fourfoldContinuous
    {X : Type v} [TopologicalSpace X]
    (f : C(X, ℝ)) : C(Vertex → X, ℝ) where
  toFun := fourfoldObservation f
  continuous_toFun := by
    unfold fourfoldObservation
    fun_prop

/-- Integrating the fourfold product is a continuous scalar observation on
the compact space of configuration probability measures. -/
def measureObservation
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (f : C(X, ℝ)) (ν : ProbabilityMeasure (Vertex → X)) : ℝ :=
  ∫ y, fourfoldContinuous f y ∂(ν : Measure (Vertex → X))

theorem continuous_measureObservation
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (f : C(X, ℝ)) :
    Continuous (measureObservation f) :=
  ProbabilityMeasure.continuous_integral_continuousMap
    (fourfoldContinuous f)

/-- The time-`n` diagonal configuration map. -/
def configurationMap
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (n : ℕ) : X → Vertex → X :=
  fun x ↦ orbitConfiguration N x n

theorem continuous_configurationMap
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (n : ℕ) :
    Continuous (configurationMap N n) := by
  rw [continuous_pi_iff]
  intro j
  simpa only [configurationMap, orbitConfiguration_apply] using
    N.continuous_nilrotation.iterate (j.val * n)

/-- The pushforward of the base measure to its time-`n` four-point
configuration. -/
def configurationMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (n : ℕ) : ProbabilityMeasure (Vertex → X) :=
  ProbabilityMeasure.map
    (⟨μ, inferInstance⟩ : ProbabilityMeasure X)
    (continuous_configurationMap N n).measurable.aemeasurable

/-- Evaluating the measure observation on the configuration measure is
exactly the usual fourfold progression integral. -/
theorem measureObservation_configurationMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (f : C(X, ℝ)) (n : ℕ) :
    measureObservation f (configurationMeasure N n) =
      ∫ x, f x * f ((N.nilrotation^[n]) x) *
        f ((N.nilrotation^[2 * n]) x) *
          f ((N.nilrotation^[3 * n]) x) ∂μ := by
  rw [measureObservation, configurationMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map
    (continuous_configurationMap N n).measurable.aemeasurable
    ((fourfoldContinuous f).continuous.aestronglyMeasurable)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    fourfoldObservation_orbitConfiguration N f x n

theorem configurationMap_succ
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (n : ℕ) :
    configurationMap N (n + 1) =
      progressionStep N ∘ configurationMap N n := by
  funext x j
  simp only [configurationMap, orbitConfiguration_apply,
    progressionStep, Function.comp_apply]
  rw [← Function.iterate_add_apply]
  congr 2
  simp [Nat.mul_succ, Nat.add_comm]

theorem configurationMap_zero
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    configurationMap N 0 = diagonalMap := by
  funext x j
  simp only [configurationMap, orbitConfiguration_apply, diagonalMap,
    Nat.mul_zero, Function.iterate_zero_apply]

theorem configurationMeasure_zero
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    configurationMeasure N 0 = diagonalMeasure μ := by
  unfold configurationMeasure diagonalMeasure
  congr 1
  exact configurationMap_zero N

theorem configurationMeasure_succ
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (n : ℕ) :
    configurationMeasure N (n + 1) =
      measureStep N (configurationMeasure N n) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [configurationMeasure, measureStep,
    ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.coe_mk]
  rw [Measure.map_map
    (continuous_progressionStep N).measurable
    (continuous_configurationMap N n).measurable]
  rw [configurationMap_succ]

/-- The entire progression-measure sequence is a single orbit in the
compact space of probability measures. -/
theorem measureStep_iterate_diagonalMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (n : ℕ) :
    ((measureStep N)^[n]) (diagonalMeasure μ) =
      configurationMeasure N n := by
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, configurationMeasure_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact (configurationMeasure_succ N n).symm

/-- The forward orbit of a pointed dynamical system. -/
def forwardOrbit {P : Type*} (T : P → P) (p : P) : Set P :=
  Set.range fun n : ℕ ↦ (T^[n]) p

/-- Its topological orbit closure. -/
abbrev orbitClosure
    {P : Type*} [TopologicalSpace P] (T : P → P) (p : P) :=
  {q : P // q ∈ closure (forwardOrbit T p)}

/-- A continuous map restricts to its own forward orbit closure. -/
def orbitClosureStep
    {P : Type*} [TopologicalSpace P]
    (T : P → P) (p : P) (hT : Continuous T) :
    orbitClosure T p → orbitClosure T p := by
  intro q
  refine ⟨T q.1, ?_⟩
  have hsubset :
      forwardOrbit T p ⊆ T ⁻¹' closure (forwardOrbit T p) := by
    rintro _ ⟨n, rfl⟩
    change T ((T^[n]) p) ∈ closure (forwardOrbit T p)
    exact subset_closure
      ⟨n + 1, Function.iterate_succ_apply' T n p⟩
  exact
    (closure_minimal hsubset (isClosed_closure.preimage hT)) q.2

theorem continuous_orbitClosureStep
    {P : Type*} [TopologicalSpace P]
    (T : P → P) (p : P) (hT : Continuous T) :
    Continuous (orbitClosureStep T p hT) := by
  exact (hT.comp continuous_subtype_val).subtype_mk _

/-- The distinguished point in its own orbit closure. -/
def orbitClosureBase
    {P : Type*} [TopologicalSpace P] (T : P → P) (p : P) :
    orbitClosure T p :=
  ⟨p, subset_closure ⟨0, by
    simp only [Function.iterate_zero_apply]⟩⟩

theorem orbitClosureStep_iterate_base
    {P : Type*} [TopologicalSpace P]
    (T : P → P) (p : P) (hT : Continuous T) (n : ℕ) :
    ((orbitClosureStep T p hT)^[n]) (orbitClosureBase T p) =
      ⟨(T^[n]) p, subset_closure ⟨n, rfl⟩⟩ := by
  apply Subtype.ext
  induction n with
  | zero =>
      simp only [Function.iterate_zero_apply, orbitClosureBase]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change T
          (((orbitClosureStep T p hT)^[n])
            (orbitClosureBase T p)).1 =
        (T^[n + 1]) p
      rw [ih]
      change T ((T^[n]) p) = (T^[n + 1]) p
      exact (Function.iterate_succ_apply' T n p).symm

/-- The correlation obtained by evolving an arbitrary four-coordinate
probability joining under the progression step.  In the BHK proof the
distinguished joining is the Hall--Petresco measure `μ̃`, not the diagonal
measure. -/
def measureOrbitCorrelation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (ν : ProbabilityMeasure (Vertex → X))
    (f : C(X, ℝ)) (n : ℕ) : ℝ :=
  measureObservation f (((measureStep N)^[n]) ν)

/-- The exact topological assertion needed for a joining-based basic
nilsequence: the joining has a minimal forward orbit closure under the
progression pushforward. -/
def HasMinimalMeasureOrbit
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (ν : ProbabilityMeasure (Vertex → X)) : Prop :=
  Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
    (orbitClosureStep (measureStep N) ν
      (continuous_measureStep N))

/-- A continuous observation of the orbit of a joining with minimal orbit
closure is a compact-minimal orbit sequence.  This is the topological core
of BHK Proposition 7.2 once its special Hall--Petresco joining is supplied. -/
theorem isMinimalOrbitSequence_measureOrbitCorrelation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (ν : ProbabilityMeasure (Vertex → X))
    (hminimal : HasMinimalMeasureOrbit N ν)
    (f : C(X, ℝ)) :
    Chapter02.HostKraStructuredRecurrence.IsMinimalOrbitSequence.{v}
      (measureOrbitCorrelation N ν f) := by
  let P := ProbabilityMeasure (Vertex → X)
  let T : P → P := measureStep N
  let Q := orbitClosure T ν
  let hT : Continuous T := continuous_measureStep N
  letI : TopologicalSpace Q := inferInstance
  letI : CompactSpace Q :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let S : Q → Q := orbitClosureStep T ν hT
  let q₀ : Q := orbitClosureBase T ν
  let ψ : Q → ℝ := fun q ↦ measureObservation f q.1
  refine ⟨Q, inferInstance, inferInstance, S, q₀, ψ,
    continuous_orbitClosureStep T ν hT, hminimal,
    (continuous_measureObservation f).comp continuous_subtype_val,
    fun n ↦ ?_⟩
  change measureObservation f (((measureStep N)^[n]) ν) =
    measureObservation f
      (((orbitClosureStep T ν hT)^[n]) (orbitClosureBase T ν)).1
  rw [orbitClosureStep_iterate_base]

/-- The diagonal-measure assertion is retained only as a named special
case.  It is not assumed in the BHK route: the actual proof uses the
Hall--Petresco joining. -/
def HasMinimalProgressionMeasureOrbit
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) : Prop :=
  HasMinimalMeasureOrbit N (diagonalMeasure μ)

/-- The continuous fourfold correlation sequence of a compact nilsystem. -/
def continuousFourfoldCorrelation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (f : C(X, ℝ)) (n : ℕ) : ℝ :=
  ∫ x, f x * f ((N.nilrotation^[n]) x) *
    f ((N.nilrotation^[2 * n]) x) *
      f ((N.nilrotation^[3 * n]) x) ∂μ

/-- Minimality of the explicit progression-measure orbit closure gives the
required compact-minimal representation of the correlation, with no
additional representation data. -/
theorem isMinimalOrbitSequence_continuousFourfoldCorrelation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (hminimal : HasMinimalProgressionMeasureOrbit N)
    (f : C(X, ℝ)) :
    Chapter02.HostKraStructuredRecurrence.IsMinimalOrbitSequence.{v}
      (continuousFourfoldCorrelation N f) := by
  let P := ProbabilityMeasure (Vertex → X)
  let T : P → P := measureStep N
  let p₀ : P := diagonalMeasure μ
  let Q := orbitClosure T p₀
  let hT : Continuous T := continuous_measureStep N
  letI : TopologicalSpace Q := inferInstance
  letI : CompactSpace Q :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let S : Q → Q := orbitClosureStep T p₀ hT
  let q₀ : Q := orbitClosureBase T p₀
  let ψ : Q → ℝ := fun q ↦ measureObservation f q.1
  refine ⟨Q, inferInstance, inferInstance, S, q₀, ψ,
    continuous_orbitClosureStep T p₀ hT, hminimal,
    (continuous_measureObservation f).comp continuous_subtype_val,
    fun n ↦ ?_⟩
  change continuousFourfoldCorrelation N f n =
    measureObservation f
      (((orbitClosureStep T p₀ hT)^[n]) (orbitClosureBase T p₀)).1
  rw [orbitClosureStep_iterate_base]
  change continuousFourfoldCorrelation N f n =
    measureObservation f (((measureStep N)^[n]) (diagonalMeasure μ))
  rw [measureStep_iterate_diagonalMeasure,
    measureObservation_configurationMeasure]
  rfl

end Chapter02.HallPetrescoMeasureOrbit
