import Chapter02.Dynamics.CompactErgodicOrbitHomogeneity
import Chapter02.HallPetresco.HallPetrescoMeasureOrbit

open Classical MeasureTheory

noncomputable section

namespace Chapter02.CompactConfigurationMeasureOrbit

universe u

/-- The four-speed map associated with a continuous self-map:
`(x₀,x₁,x₂,x₃) ↦ (x₀,T x₁,T² x₂,T³ x₃)`. -/
def progressionStep
    {X : Type u} (T : X → X)
    (y : Chapter02.HallPetrescoTwoStepGroup.Vertex → X) :
    Chapter02.HallPetrescoTwoStepGroup.Vertex → X :=
  fun j ↦ (T^[j.val]) (y j)

theorem continuous_progressionStep
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (hT : Continuous T) :
    Continuous (progressionStep T) := by
  rw [continuous_pi_iff]
  intro j
  exact (hT.iterate j.val).comp (continuous_apply j)

/-- The diagonal map into four configurations. -/
def diagonalMap
    {X : Type u} (x : X) :
    Chapter02.HallPetrescoTwoStepGroup.Vertex → X :=
  fun _ ↦ x

theorem continuous_diagonalMap
    {X : Type u} [TopologicalSpace X] :
    Continuous (diagonalMap : X →
      Chapter02.HallPetrescoTwoStepGroup.Vertex → X) := by
  rw [continuous_pi_iff]
  intro _
  exact continuous_id

/-- The time-`n` four-point progression configuration. -/
def configurationMap
    {X : Type u} (T : X → X) (n : ℕ) (x : X) :
    Chapter02.HallPetrescoTwoStepGroup.Vertex → X :=
  fun j ↦ (T^[j.val * n]) x

theorem continuous_configurationMap
    {X : Type u} [TopologicalSpace X]
    (T : X → X) (hT : Continuous T) (n : ℕ) :
    Continuous (configurationMap T n) := by
  rw [continuous_pi_iff]
  intro j
  exact hT.iterate (j.val * n)

theorem configurationMap_zero
    {X : Type u} (T : X → X) :
    configurationMap T 0 = diagonalMap := by
  funext x j
  simp [configurationMap, diagonalMap]

theorem configurationMap_succ
    {X : Type u} (T : X → X) (n : ℕ) :
    configurationMap T (n + 1) =
      progressionStep T ∘ configurationMap T n := by
  funext x j
  simp only [configurationMap, progressionStep, Function.comp_apply]
  rw [← Function.iterate_add_apply]
  congr 2
  simp [Nat.mul_succ, Nat.add_comm]

/-- The diagonal probability measure on four configurations. -/
def diagonalMeasure
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ProbabilityMeasure
      (Chapter02.HallPetrescoTwoStepGroup.Vertex → X) :=
  ProbabilityMeasure.map
    (⟨μ, inferInstance⟩ : ProbabilityMeasure X)
    continuous_diagonalMap.measurable.aemeasurable

/-- The probability measure carried by the time-`n` configurations. -/
def configurationMeasure
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T) (n : ℕ) :
    ProbabilityMeasure
      (Chapter02.HallPetrescoTwoStepGroup.Vertex → X) :=
  ProbabilityMeasure.map
    (⟨μ, inferInstance⟩ : ProbabilityMeasure X)
    (continuous_configurationMap T hT n).measurable.aemeasurable

/-- Push a configuration measure forward by one four-speed step. -/
def measureStep
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T)
    (ν : ProbabilityMeasure
      (Chapter02.HallPetrescoTwoStepGroup.Vertex → X)) :
    ProbabilityMeasure
      (Chapter02.HallPetrescoTwoStepGroup.Vertex → X) :=
  ν.map (continuous_progressionStep T hT).measurable.aemeasurable

theorem continuous_measureStep
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (T : X → X) (hT : Continuous T) :
    Continuous (measureStep T hT) :=
  ProbabilityMeasure.continuous_map
    (continuous_progressionStep T hT)

theorem configurationMeasure_zero
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T) :
    configurationMeasure μ T hT 0 = diagonalMeasure μ := by
  unfold configurationMeasure diagonalMeasure
  congr 1

theorem configurationMeasure_succ
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T) (n : ℕ) :
    configurationMeasure μ T hT (n + 1) =
      measureStep T hT (configurationMeasure μ T hT n) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [configurationMeasure, measureStep,
    ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]
  rw [Measure.map_map
    (continuous_progressionStep T hT).measurable
    (continuous_configurationMap T hT n).measurable]
  rw [configurationMap_succ]

theorem measureStep_iterate_diagonalMeasure
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T) (n : ℕ) :
    ((measureStep T hT)^[n]) (diagonalMeasure μ) =
      configurationMeasure μ T hT n := by
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, configurationMeasure_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact (configurationMeasure_succ μ T hT n).symm

/-- Integration of an arbitrary continuous four-configuration
observation. -/
def measureObservation
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (F : C(Chapter02.HallPetrescoTwoStepGroup.Vertex → X, ℝ))
    (ν : ProbabilityMeasure
      (Chapter02.HallPetrescoTwoStepGroup.Vertex → X)) : ℝ :=
  ∫ y, F y ∂(ν : Measure
    (Chapter02.HallPetrescoTwoStepGroup.Vertex → X))

theorem continuous_measureObservation
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (F : C(Chapter02.HallPetrescoTwoStepGroup.Vertex → X, ℝ)) :
    Continuous (measureObservation F) :=
  ProbabilityMeasure.continuous_integral_continuousMap F

/-- The scalar correlation obtained by integrating a continuous
observation over the time-`n` four-configuration measure. -/
def configurationCorrelation
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T)
    (F : C(Chapter02.HallPetrescoTwoStepGroup.Vertex → X, ℝ))
    (n : ℕ) : ℝ :=
  measureObservation F (configurationMeasure μ T hT n)

theorem configurationCorrelation_eq_integral
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T)
    (F : C(Chapter02.HallPetrescoTwoStepGroup.Vertex → X, ℝ))
    (n : ℕ) :
    configurationCorrelation μ T hT F n =
      ∫ x, F (configurationMap T n x) ∂μ := by
  rw [configurationCorrelation, measureObservation, configurationMeasure,
    ProbabilityMeasure.toMeasure_map]
  exact MeasureTheory.integral_map
    (continuous_configurationMap T hT n).measurable.aemeasurable
    F.continuous.aestronglyMeasurable

/-- The actual orbit closure of the diagonal configuration measure is
homogeneous when all of its points have the same forward orbit closure. -/
def HasHomogeneousConfigurationMeasureOrbit
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T) : Prop :=
  Chapter02.CompactErgodicOrbitHomogeneity.OrbitClosureHomogeneous
    (Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep
      (measureStep T hT) (diagonalMeasure μ)
      (continuous_measureStep T hT))

/-- The distinguished diagonal measure has dense orbit in its own orbit
closure. -/
theorem denseRange_orbitClosureBase
    {P : Type*} [TopologicalSpace P]
    (T : P → P) (p : P) (hT : Continuous T) :
    DenseRange fun n : ℕ ↦
      ((Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep T p hT)^[n])
        (Chapter02.HallPetrescoMeasureOrbit.orbitClosureBase T p) := by
  let Q := Chapter02.HallPetrescoMeasureOrbit.orbitClosure T p
  let S : Q → Q :=
    Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep T p hT
  let q₀ : Q :=
    Chapter02.HallPetrescoMeasureOrbit.orbitClosureBase T p
  rw [DenseRange, Subtype.dense_iff]
  intro q hq
  have himage :
      ((fun z : Q ↦ (z : P)) '' Set.range (fun n : ℕ ↦ (S^[n]) q₀)) =
        Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T p := by
    ext z
    constructor
    · rintro ⟨q', ⟨n, hn⟩, rfl⟩
      subst q'
      refine ⟨n, ?_⟩
      exact (congrArg Subtype.val
        (Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep_iterate_base
          T p hT n)).symm
    · rintro ⟨n, rfl⟩
      refine ⟨(S^[n]) q₀, ⟨n, rfl⟩, ?_⟩
      exact congrArg Subtype.val
        (Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep_iterate_base
          T p hT n)
  rw [himage]
  exact hq

/-- Homogeneity of the actual diagonal configuration-measure orbit closure
turns every continuous configuration correlation into a compact-minimal
orbit sequence. -/
theorem isMinimalOrbitSequence_configurationCorrelation_of_homogeneous
    {X : Type u} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Continuous T)
    (hhom : HasHomogeneousConfigurationMeasureOrbit μ T hT)
    (F : C(Chapter02.HallPetrescoTwoStepGroup.Vertex → X, ℝ)) :
    Chapter02.HostKraStructuredRecurrence.IsMinimalOrbitSequence.{u}
      (configurationCorrelation μ T hT F) := by
  let P :=
    ProbabilityMeasure
      (Chapter02.HallPetrescoTwoStepGroup.Vertex → X)
  let R : P → P := measureStep T hT
  let p₀ : P := diagonalMeasure μ
  let Q := Chapter02.HallPetrescoMeasureOrbit.orbitClosure R p₀
  let hR : Continuous R := continuous_measureStep T hT
  let S : Q → Q :=
    Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep R p₀ hR
  let q₀ : Q :=
    Chapter02.HallPetrescoMeasureOrbit.orbitClosureBase R p₀
  let ψ : Q → ℝ := fun q ↦ measureObservation F q.1
  letI : TopologicalSpace Q := inferInstance
  letI : CompactSpace Q :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  have hdense : DenseRange fun n : ℕ ↦ (S^[n]) q₀ :=
    denseRange_orbitClosureBase R p₀ hR
  have hminimal :
      Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen S :=
    Chapter02.CompactErgodicOrbitHomogeneity.everyOrbitHitsOpen_of_denseOrbit_of_orbitClosureHomogeneous
      S hhom q₀ hdense
  refine ⟨Q, inferInstance, inferInstance, S, q₀, ψ,
    Chapter02.HallPetrescoMeasureOrbit.continuous_orbitClosureStep R p₀ hR,
    hminimal,
    (continuous_measureObservation F).comp continuous_subtype_val,
    fun n ↦ ?_⟩
  change measureObservation F (configurationMeasure μ T hT n) =
    measureObservation F (((S^[n]) q₀).1)
  rw [← measureStep_iterate_diagonalMeasure μ T hT n]
  congr 1
  exact (congrArg Subtype.val
    (Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep_iterate_base
      R p₀ hR n)).symm

end Chapter02.CompactConfigurationMeasureOrbit
