import Chapter02.HallPetresco.HallPetrescoJoining

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoCentralMeasures

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HostKraCentralChangeVariables

universe u v

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The four-point central Hall configuration whose product observation is
the packed integrand in BHK equation (8.5). -/
def centralConfiguration
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ)
    (q : (G × G) × G) (r : X × G) : Vertex → X :=
  ![C.act q.1.1 r.1,
    C.act (q.1.1 * q.1.2 * r.2) r.1,
    C.act (q.1.1 * q.1.2 ^ 2 * q.2 * r.2 ^ 2) r.1,
    C.act (q.1.1 * q.1.2 ^ 3 * q.2 ^ 3 * r.2 ^ 3) r.1]

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_centralConfiguration
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ) :
    Continuous (fun z : ((G × G) × G) × (X × G) ↦
      centralConfiguration C z.1 z.2) := by
  have hact
      (a : (((G × G) × G) × (X × G)) → G)
      (ha : Continuous a) :
      Continuous (fun z ↦ C.act (a z) z.2.1) := by
    simpa only [Function.comp_apply] using
      C.continuous_act.comp
        (ha.prodMk (continuous_fst.comp continuous_snd))
  rw [continuous_pi_iff]
  intro j
  fin_cases j <;> simp [centralConfiguration] <;>
    apply hact <;> fun_prop

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_centralConfiguration_fixed
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ)
    (q : (G × G) × G) :
    Continuous (centralConfiguration C q) := by
  exact (continuous_centralConfiguration C).comp
    ((continuous_const : Continuous (fun _ : X × G ↦ q)).prodMk
      continuous_id)

omit [CompactSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] in
/-- Multiplying the Haar variable by the linear central parameter removes
that parameter from the Hall configuration.  This is the explicit
change-of-variables underlying the linear `G₂` direction in BHK's reduced
Hall--Petresco quotient. -/
theorem centralConfiguration_linearParameter_changeVariables
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ)
    (q : (G × G) × G) (r : X × G) :
    centralConfiguration C q r =
      centralConfiguration C ((q.1.1, 1), q.2) (r.1, q.1.2 * r.2) := by
  funext j
  fin_cases j <;>
    simp [centralConfiguration, mul_pow, mul_assoc, mul_comm, mul_left_comm]

/-- Push `μ × m` through a fixed central Hall configuration. -/
def centralParameterMeasure
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ)
    (q : (G × G) × G) : ProbabilityMeasure (Vertex → X) :=
  ProbabilityMeasure.map
    (⟨μ.prod m, inferInstance⟩ : ProbabilityMeasure (X × G))
    (continuous_centralConfiguration_fixed C q).measurable.aemeasurable

/-- For a left-invariant probability measure, the central Hall parameter
measure descends through the linear central direction: its middle parameter
can be normalized to the identity. -/
theorem centralParameterMeasure_linearParameter_eq
    (m : Measure G) [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ)
    (q : (G × G) × G) :
    centralParameterMeasure m μ C q =
      centralParameterMeasure m μ C ((q.1.1, 1), q.2) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [centralParameterMeasure, ProbabilityMeasure.toMeasure_map]
  let R : X × G → X × G := fun r ↦ (r.1, q.1.2 * r.2)
  have hR : MeasurePreserving R (μ.prod m) (μ.prod m) := by
    simpa [R, Prod.map] using
      (MeasurePreserving.prod (MeasurePreserving.id μ)
        (measurePreserving_mul_left m q.1.2))
  calc
    Measure.map (centralConfiguration C q) (μ.prod m) =
        Measure.map
          (centralConfiguration C ((q.1.1, 1), q.2) ∘ R)
          (μ.prod m) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun r ↦
        centralConfiguration_linearParameter_changeVariables C q r
    _ = Measure.map (centralConfiguration C ((q.1.1, 1), q.2))
          (Measure.map R (μ.prod m)) := by
      rw [Measure.map_map
        (continuous_centralConfiguration_fixed C
          ((q.1.1, 1), q.2)).measurable
        hR.measurable]
    _ = Measure.map (centralConfiguration C ((q.1.1, 1), q.2))
          (μ.prod m) := by rw [hR.map_eq]

omit [CompactSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] in
theorem fourfoldObservation_centralConfiguration
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ)
    (f : C(X, ℝ)) (q : (G × G) × G) (r : X × G) :
    fourfoldObservation f (centralConfiguration C q r) =
      packedHallIntegrand C f q r := by
  unfold fourfoldObservation centralConfiguration packedHallIntegrand
    hallCentralIntegrand
  simp [Fin.prod_univ_succ]
  ring

/-- Integrating the product observation against the central parameter
measure gives exactly the BHK central Hall value. -/
theorem measureObservation_centralParameterMeasure
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ)
    (f : C(X, ℝ)) (q : (G × G) × G) :
    Chapter02.HallPetrescoMeasureOrbit.measureObservation f
        (centralParameterMeasure m μ C q) =
      centralHallValue m μ C f q.1.1 q.1.2 q.2 := by
  rw [Chapter02.HallPetrescoMeasureOrbit.measureObservation,
    centralParameterMeasure, ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (continuous_centralConfiguration_fixed C q).measurable.aemeasurable
    ((Chapter02.HallPetrescoMeasureOrbit.fourfoldContinuous f).continuous.aestronglyMeasurable)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r ↦
    fourfoldObservation_centralConfiguration C f q r

/-- The Hall central parameter measures vary continuously in the weak
topology on probability measures. -/
theorem continuous_centralParameterMeasure
    (m : Measure G) [IsProbabilityMeasure m]
    {X : Type v} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (C : Chapter02.CentralFiberFourfold.CompactCentralAction G X μ) :
    Continuous (centralParameterMeasure m μ C) := by
  rw [continuous_iff_continuousAt]
  intro q
  change Filter.Tendsto (centralParameterMeasure m μ C)
    (nhds q) (nhds (centralParameterMeasure m μ C q))
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  have hjoint :
      Continuous (fun z : ((G × G) × G) × (X × G) ↦
        F (centralConfiguration C z.1 z.2)) :=
    F.continuous.comp (continuous_centralConfiguration C)
  have hint :
      Continuous (fun p : (G × G) × G ↦
        ∫ r, F (centralConfiguration C p r) ∂(μ.prod m)) := by
    have h :=
      continuous_parametric_integral_of_continuous
        (μ := μ.prod m)
        (f := fun p : (G × G) × G ↦ fun r : X × G ↦
          F (centralConfiguration C p r))
        hjoint isCompact_univ
    simpa only [Measure.restrict_univ] using h
  have hmap (p : (G × G) × G) :
      (∫ y, F y ∂(centralParameterMeasure m μ C p :
          ProbabilityMeasure (Vertex → X))) =
        ∫ r, F (centralConfiguration C p r) ∂(μ.prod m) := by
    rw [centralParameterMeasure, ProbabilityMeasure.toMeasure_map]
    exact integral_map
      (continuous_centralConfiguration_fixed C p).measurable.aemeasurable
      F.continuous.aestronglyMeasurable
  simpa only [hmap] using hint.continuousAt

/-- An observation-independent geometric orbit interface sufficient for the
Hall--Petresco joining argument.  BHK obtains the needed scalar consequence
from the reduced nilmanifold of Lemma 7.1 and the continuous observation
constructed in Proposition 7.2. -/
def HasHallPetrescoGeometricOrbit
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (ν : ProbabilityMeasure (Vertex → X)) : Prop :=
  Chapter02.HallPetrescoMeasureOrbit.HasMinimalMeasureOrbit N ν ∧
    ∀ q,
      centralParameterMeasure m μ
          (Chapter02.toCompactCentralAction N.centralAction) q ∈
        closure
          (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
            (Chapter02.HallPetrescoMeasureOrbit.measureStep N) ν)

/-- The geometric orbit statement, together with the explicit parameter
measure construction above, supplies the complete joining interface for
every continuous observation. -/
theorem hasHallPetrescoJoining_of_geometricOrbit
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (ν : ProbabilityMeasure (Vertex → X))
    (hgeom : HasHallPetrescoGeometricOrbit N m ν)
    (f : C(X, ℝ)) :
    Chapter02.HallPetrescoJoining.HasHallPetrescoJoining N m f ν := by
  refine ⟨hgeom.1,
    centralParameterMeasure m μ
      (Chapter02.toCompactCentralAction N.centralAction),
    continuous_centralParameterMeasure m μ
      (Chapter02.toCompactCentralAction N.centralAction),
    hgeom.2, ?_⟩
  intro q
  exact measureObservation_centralParameterMeasure m μ
    (Chapter02.toCompactCentralAction N.centralAction) f q

/-- The geometric orbit statement gives the complete Hall--Petresco
correlation orbit used by the sharp central-fiber theorem. -/
theorem hasHallPetrescoCorrelationOrbit_of_geometricOrbit
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (ν : ProbabilityMeasure (Vertex → X))
    (hgeom : HasHallPetrescoGeometricOrbit N m ν)
    (f : C(X, ℝ)) :
    Chapter02.HostKraHallPetrescoCorrelation.HasHallPetrescoCorrelationOrbit
      m μ (Chapter02.toCompactCentralAction N.centralAction) f
      (Chapter02.HallPetrescoMeasureOrbit.measureOrbitCorrelation
        N ν f) :=
  Chapter02.HallPetrescoJoining.hasHallPetrescoCorrelationOrbit_of_joining
    N m f ν (hasHallPetrescoJoining_of_geometricOrbit N m ν hgeom f)

end Chapter02.HallPetrescoCentralMeasures
