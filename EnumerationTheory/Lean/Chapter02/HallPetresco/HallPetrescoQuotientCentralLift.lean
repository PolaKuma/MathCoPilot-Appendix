import Chapter02.HallPetresco.HallPetrescoOrbitPresentation
import Mathlib.MeasureTheory.Measure.Prokhorov

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoQuotientCentralLift

open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoMeasureOrbit
open Chapter02.HallPetrescoCentralMeasures

universe u v

/-- The central torus exponent in coordinate `j`. -/
def centralExponent
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)))
    (r : Fin N.torusDim → Circle) (j : Vertex) :
    Fin N.torusDim → Circle :=
  q.1.1 * (q.1.2 * r) ^ j.val * q.2 ^ j.val.choose 2

@[simp]
theorem centralExponent_eq_tuple
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)))
    (r : Fin N.torusDim → Circle) (j : Vertex) :
    centralExponent N q r j =
      ![q.1.1,
        q.1.1 * q.1.2 * r,
        q.1.1 * q.1.2 ^ 2 * q.2 * r ^ 2,
        q.1.1 * q.1.2 ^ 3 * q.2 ^ 3 * r ^ 3] j := by
  fin_cases j <;>
    simp [centralExponent, mul_pow, mul_left_comm, mul_comm]

/-- The Hall--Petresco subgroup element with central coordinates
`q₀ (q₁ r)^j q₂^{choose(j,2)}`. -/
def centralHallElement
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)))
    (r : Fin N.torusDim → Circle) :
    subgroup N :=
  ⟨diagonal (N.centralHom q.1.1) *
      linear (N.centralHom (q.1.2 * r)) *
        quadratic (N.centralHom q.2),
    (subgroup N).mul_mem
      ((subgroup N).mul_mem
        (diagonal_mem_subgroup N (N.centralHom q.1.1))
        (linear_mem_subgroup N (N.centralHom (q.1.2 * r))))
      (quadratic_central_mem_subgroup N q.2)⟩

@[simp]
theorem centralHallElement_apply
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)))
    (r : Fin N.torusDim → Circle) (j : Vertex) :
    ((centralHallElement N q r : subgroup N) : Vertex → H) j =
      N.centralHom (centralExponent N q r j) := by
  simp [centralHallElement, centralExponent, map_mul, map_pow]

theorem continuous_centralHallElement_fixed
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    Continuous (centralHallElement N q) := by
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun r : Fin N.torusDim → Circle ↦
    N.centralHom q.1.1 *
      (N.centralHom (q.1.2 * r)) ^ j.val *
        (N.centralHom q.2) ^ j.val.choose 2)
  have hmiddle :
      Continuous (fun r : Fin N.torusDim → Circle ↦
        N.centralHom (q.1.2 * r)) :=
    N.continuous_centralHom.comp (continuous_const.mul continuous_id)
  exact (continuous_const.mul (hmiddle.pow j.val)).mul continuous_const

/-- A central Hall parameter point in the actual lattice quotient. -/
def centralQuotientPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)))
    (z : X × (Fin N.torusDim → Circle)) :
    Quotient N P.lattice :=
  centralHallElement N q z.2 • quotientDiagonalPoint N P z.1

theorem continuous_centralQuotientPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    Continuous (centralQuotientPoint N P q) := by
  exact continuous_smul.comp
    (((continuous_centralHallElement_fixed N q).comp continuous_snd).prodMk
      ((continuous_quotientDiagonalPoint N P).comp continuous_fst))

/-- The concrete quotient lift has exactly the central configuration used
in the Hall--Petresco integral formula. -/
theorem quotientConfiguration_centralQuotientPoint
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle)))
    (z : X × (Fin N.torusDim → Circle)) :
    quotientConfiguration N P (centralQuotientPoint N P q z) =
      centralConfiguration
        (Chapter02.toCompactCentralAction N.centralAction) q z := by
  letI := configurationAction N
  rw [centralQuotientPoint, quotientConfiguration_smul,
    quotientConfiguration_quotientDiagonalPoint]
  funext j
  change
    N.ambientAction.toMulAction.smul
        (((centralHallElement N q z.2 : subgroup N) : Vertex → H) j) z.1 =
      centralConfiguration
        (Chapter02.toCompactCentralAction N.centralAction) q z j
  rw [centralHallElement_apply, centralExponent_eq_tuple]
  fin_cases j <;> rfl

/-- Push `μ × m` through the concrete quotient lift of a central Hall
parameter. -/
def centralQuotientMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    ProbabilityMeasure (Quotient N P.lattice) :=
  ProbabilityMeasure.map
    (⟨μ.prod m, inferInstance⟩ :
      ProbabilityMeasure (X × (Fin N.torusDim → Circle)))
    (continuous_centralQuotientPoint N P q).measurable.aemeasurable

/-- The central parameter measure is not merely supported on an abstract
configuration orbit: it is the image of an explicit probability measure
on the actual Hall--Petresco lattice quotient. -/
theorem quotientConfigurationMeasure_centralQuotientMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    quotientConfigurationMeasure N P
        (centralQuotientMeasure N P m q) =
      centralParameterMeasure m μ
        (Chapter02.toCompactCentralAction N.centralAction) q := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [quotientConfigurationMeasure, centralQuotientMeasure,
    centralParameterMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (continuous_quotientConfiguration N P).measurable
    (continuous_centralQuotientPoint N P q).measurable]
  congr 1
  funext z
  exact quotientConfiguration_centralQuotientPoint N P q z

theorem centralParameterMeasure_mem_range_quotientConfigurationMeasure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (q : (((Fin N.torusDim → Circle) ×
      (Fin N.torusDim → Circle)) ×
        (Fin N.torusDim → Circle))) :
    centralParameterMeasure m μ
        (Chapter02.toCompactCentralAction N.centralAction) q ∈
      Set.range (quotientConfigurationMeasure N P) := by
  refine ⟨centralQuotientMeasure N P m q, ?_⟩
  exact quotientConfigurationMeasure_centralQuotientMeasure N P m q

/-- Progression translation acting on probability measures on the actual
Hall--Petresco quotient. -/
def quotientMeasureStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)] :
    ProbabilityMeasure (Quotient N P.lattice) →
      ProbabilityMeasure (Quotient N P.lattice) :=
  fun ν ↦
    ν.map (continuous_quotientStep N P.lattice).measurable.aemeasurable

theorem continuous_quotientMeasureStep
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)] :
    Continuous (quotientMeasureStep N P) :=
  ProbabilityMeasure.continuous_map
    (continuous_quotientStep N P.lattice)

/-- The observation-independent geometric statement on the actual quotient:
one quotient probability measure has a minimal progression orbit closure,
and that closure contains every explicit central quotient measure. -/
def HasGeometricQuotientMeasureOrbit
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] : Prop :=
  ∃ ν : ProbabilityMeasure (Quotient N P.lattice),
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
      (Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep
        (quotientMeasureStep N P) ν
        (continuous_quotientMeasureStep N P)) ∧
    ∀ q, centralQuotientMeasure N P m q ∈
      closure
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (quotientMeasureStep N P) ν)

/-- The exact remaining Hall--Petresco dynamical statement on the actual
quotient-measure space.  It no longer asks the full point quotient to be
minimal; instead it asks for a compact minimal measure system containing
all explicit central quotient measures. -/
def HasQuotientMeasurePresentation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] : Prop :=
  ∃ Y : Type, ∃ _top : TopologicalSpace Y, ∃ _compact : CompactSpace Y,
    ∃ _nonempty : Nonempty Y, ∃ S : Y → Y,
    ∃ Ψ : Y → ProbabilityMeasure (Quotient N P.lattice),
      Continuous Ψ ∧
      (∀ y, Ψ (S y) = quotientMeasureStep N P (Ψ y)) ∧
      Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen S ∧
      ∀ q, centralQuotientMeasure N P m q ∈ Set.range Ψ

/-- A single geometric quotient-measure orbit produces the explicit compact
minimal presentation by restricting the progression map to its orbit
closure. -/
theorem hasQuotientMeasurePresentation_of_geometricOrbit
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (hgeom : HasGeometricQuotientMeasureOrbit N P m) :
    HasQuotientMeasurePresentation N P m := by
  letI : T2Space (Quotient N P.lattice) :=
    quotientT2Space N P
  letI : TopologicalSpace.PseudoMetrizableSpace
      (Quotient N P.lattice) :=
    quotientPseudoMetrizableSpace N P
  letI : CompactSpace
      (ProbabilityMeasure (Quotient N P.lattice)) := inferInstance
  obtain ⟨ν, hminimal, hcentral⟩ := hgeom
  let T := quotientMeasureStep N P
  let hT : Continuous T := continuous_quotientMeasureStep N P
  let Y := Chapter02.HallPetrescoMeasureOrbit.orbitClosure T ν
  letI : TopologicalSpace Y := inferInstance
  letI : CompactSpace Y :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let S : Y → Y :=
    Chapter02.HallPetrescoMeasureOrbit.orbitClosureStep T ν hT
  let Ψ : Y → ProbabilityMeasure (Quotient N P.lattice) :=
    fun y ↦ y.1
  refine ⟨Y, inferInstance, inferInstance, ⟨
    Chapter02.HallPetrescoMeasureOrbit.orbitClosureBase T ν⟩,
    S, Ψ, continuous_subtype_val, ?_, hminimal, ?_⟩
  · intro y
    rfl
  · intro q
    exact ⟨⟨centralQuotientMeasure N P m q, hcentral q⟩, rfl⟩

/-- Conversely, any compact minimal presentation already contains a
distinguished quotient measure whose own progression orbit closure is
minimal and contains every central quotient measure. -/
theorem geometricOrbit_of_hasQuotientMeasurePresentation
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (hpresent : HasQuotientMeasurePresentation N P m) :
    HasGeometricQuotientMeasureOrbit N P m := by
  letI : T2Space (Quotient N P.lattice) :=
    quotientT2Space N P
  letI : TopologicalSpace.PseudoMetrizableSpace
      (Quotient N P.lattice) :=
    quotientPseudoMetrizableSpace N P
  letI : T2Space
      (ProbabilityMeasure (Quotient N P.lattice)) := inferInstance
  obtain ⟨Y, topY, compactY, nonemptyY, S, Ψ,
      hΨ, hequiv, hminimal, hcentral⟩ := hpresent
  letI : TopologicalSpace Y := topY
  letI : CompactSpace Y := compactY
  obtain ⟨y₀⟩ := nonemptyY
  refine ⟨Ψ y₀, ?_, ?_⟩
  · exact
      Chapter02.MinimalFactorOrbitClosure.everyOrbitHitsOpen_orbitClosure_of_factor
        S (quotientMeasureStep N P) (continuous_quotientMeasureStep N P)
        Ψ hΨ hequiv hminimal y₀
  · intro q
    obtain ⟨y, hy⟩ := hcentral q
    rw [← hy]
    exact
      Chapter02.MinimalFactorOrbitClosure.factor_mem_orbitClosure_of_minimal
        S (quotientMeasureStep N P) Ψ hΨ hequiv hminimal y₀ y

/-- With the natural compactness of the quotient probability-measure space,
the presentation and the single geometric-orbit formulations are
equivalent. -/
theorem hasQuotientMeasurePresentation_iff_geometricOrbit
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] :
    HasQuotientMeasurePresentation N P m ↔
      HasGeometricQuotientMeasureOrbit N P m := by
  letI : T2Space (Quotient N P.lattice) :=
    quotientT2Space N P
  letI : TopologicalSpace.PseudoMetrizableSpace
      (Quotient N P.lattice) :=
    quotientPseudoMetrizableSpace N P
  letI : T2Space
      (ProbabilityMeasure (Quotient N P.lattice)) := inferInstance
  constructor
  · exact geometricOrbit_of_hasQuotientMeasurePresentation N P m
  · exact hasQuotientMeasurePresentation_of_geometricOrbit N P m

/-- A compact minimal presentation on actual quotient measures supplies
the operational Hall--Petresco presentation used downstream. -/
theorem hasOrbitPresentation_of_quotientMeasurePresentation
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (hpresent : HasQuotientMeasurePresentation N P m) :
    Chapter02.HallPetrescoOrbitPresentation.HasOrbitPresentation N m := by
  obtain ⟨Y, topY, compactY, nonemptyY, S, Ψ,
      hΨ, hequiv, hminimal, hcentral⟩ := hpresent
  letI : TopologicalSpace Y := topY
  letI : CompactSpace Y := compactY
  refine ⟨Y, inferInstance, inferInstance, nonemptyY, S,
    quotientConfigurationMeasure N P ∘ Ψ, ?_, ?_, hminimal, ?_⟩
  · exact (continuous_quotientConfigurationMeasure N P).comp hΨ
  · intro y
    change quotientConfigurationMeasure N P (Ψ (S y)) =
      measureStep N (quotientConfigurationMeasure N P (Ψ y))
    rw [hequiv]
    exact quotientConfigurationMeasure_map_quotientStep N P (Ψ y)
  · intro q
    obtain ⟨y, hy⟩ := hcentral q
    refine ⟨y, ?_⟩
    change quotientConfigurationMeasure N P (Ψ y) =
      centralParameterMeasure m μ
        (Chapter02.toCompactCentralAction N.centralAction) q
    rw [hy]
    exact quotientConfigurationMeasure_centralQuotientMeasure N P m q

/-- The actual quotient-measure presentation therefore produces the
distinguished geometric measure orbit required by the Hall--Petresco
joining argument. -/
theorem exists_geometricOrbit_of_quotientMeasurePresentation
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (hpresent : HasQuotientMeasurePresentation N P m) :
    ∃ ν : ProbabilityMeasure (Vertex → X),
      HasHallPetrescoGeometricOrbit N m ν :=
  Chapter02.HallPetrescoOrbitPresentation.exists_geometricOrbit_of_presentation
    N m (hasOrbitPresentation_of_quotientMeasurePresentation
      N P m hpresent)

/-- For every continuous observation, the same concrete presentation gives
the full correlation orbit consumed by the checked sharp Fourier argument. -/
theorem exists_correlationOrbit_of_quotientMeasurePresentation
    {H X : Type}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ]
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [CompactSpace (Quotient N P.lattice)]
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m]
    (hpresent : HasQuotientMeasurePresentation N P m)
    (f : C(X, ℝ)) :
    ∃ ν : ProbabilityMeasure (Vertex → X),
      Chapter02.HostKraHallPetrescoCorrelation.HasHallPetrescoCorrelationOrbit
        m μ (Chapter02.toCompactCentralAction N.centralAction) f
        (measureOrbitCorrelation N ν f) :=
  Chapter02.HallPetrescoOrbitPresentation.exists_correlationOrbit_of_presentation
    N m (hasOrbitPresentation_of_quotientMeasurePresentation
      N P m hpresent) f

end Chapter02.HallPetrescoQuotientCentralLift
