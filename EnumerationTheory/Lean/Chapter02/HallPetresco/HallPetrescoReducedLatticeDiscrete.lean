import Chapter02.HallPetresco.CountableLocallyCompactGroupDiscrete
import Chapter02.HallPetresco.HallPetrescoReducedHausdorff
import Chapter02.HallPetresco.LocalHomeomorphLatticeLift
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Covering.Quotient

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoReducedLatticeDiscrete

open Chapter02.CountableLocallyCompactGroupDiscrete
open Chapter02.HallPetrescoTwoStepGroup
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedHausdorff

universe u v

/-- In a locally compact second-countable ambient group, the four-coordinate
Hall--Petresco lattice is countable. -/
theorem countable_subgroupLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Countable (subgroupLattice N P.lattice) := by
  letI : DiscreteTopology P.lattice := P.discreteLattice
  letI : Countable P.lattice :=
    countable_of_Lindelof_of_discrete
  let encode :
      subgroupLattice N P.lattice → Vertex → P.lattice :=
    fun l j ↦ ⟨(l.1.1 : Vertex → H) j, l.property j⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congr_fun hab j)
  exact hencode.countable

/-- The image lattice in the reduced Hall--Petresco group is countable. -/
theorem countable_reducedLattice
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    Countable (reducedLattice N P.lattice) := by
  letI : Countable (subgroupLattice N P.lattice) :=
    countable_subgroupLattice N P
  let project :
      subgroupLattice N P.lattice → reducedLattice N P.lattice :=
    fun l ↦
      ⟨QuotientGroup.mk' (averagingNormalSubgroup N) l.1,
        ⟨l.1, l.property, rfl⟩⟩
  have hproject : Function.Surjective project := by
    rintro ⟨r, hr⟩
    rcases hr with ⟨l, hl, rfl⟩
    refine ⟨⟨l, hl⟩, ?_⟩
    rfl
  exact hproject.countable

/-- The actual reduced Hall--Petresco lattice is discrete under the
standard locally compact, second-countable hypotheses of a Lie
nilmanifold.

Closedness was proved geometrically from the compact averaging orbit.
Countability comes from the original discrete four-coordinate lattice.
The conclusion is then the Baire theorem for countable locally compact
Hausdorff groups. -/
noncomputable def reducedLatticeDiscreteTopology
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    DiscreteTopology (reducedLattice N P.lattice) := by
  letI : T2Space H := N.t2Ambient
  letI : LocallyCompactSpace (subgroup N) :=
    (subgroup_isClosed N).locallyCompactSpace
  letI : IsClosed
      (reducedLattice N P.lattice : Set (ReducedGroup N)) :=
    isClosed_reducedLattice N P
  letI : Countable (reducedLattice N P.lattice) :=
    countable_reducedLattice N P
  letI : LocallyCompactSpace (reducedLattice N P.lattice) :=
    (isClosed_reducedLattice N P).locallyCompactSpace
  exact discreteTopology_of_countable_of_baire
    (reducedLattice N P.lattice)

/-- Consequently the canonical projection to the reduced quotient is a
covering map.  This supplies the local lifting device used in the
Parry--Leibman orbit-closure argument. -/
theorem reducedQuotient_isCoveringMap
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsCoveringMap
      (QuotientGroup.mk :
        ReducedGroup N → ReducedQuotient N P.lattice) := by
  letI : T2Space H := N.t2Ambient
  letI : IsClosed
      (reducedLattice N P.lattice : Set (ReducedGroup N)) :=
    isClosed_reducedLattice N P
  letI : DiscreteTopology (reducedLattice N P.lattice) :=
    reducedLatticeDiscreteTopology N P
  exact
    ((reducedLattice N P.lattice).isQuotientCoveringMap
      (isDiscrete_iff_discreteTopology.mpr inferInstance)).isCoveringMap

/-- The reduced quotient projection is therefore locally a homeomorphism.
This is the exact local representative selection needed to lift sufficiently
small returns from the compact reduced quotient back to its nilpotent
translation group. -/
theorem reducedQuotient_isLocalHomeomorph
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    IsLocalHomeomorph
      (QuotientGroup.mk :
        ReducedGroup N → ReducedQuotient N P.lattice) :=
  (reducedQuotient_isCoveringMap N P).isLocalHomeomorph

/-- Convergent returns in the reduced quotient admit representatives
corrected by the actual reduced lattice which converge to the identity
upstairs. -/
theorem exists_reducedLattice_correction_tendsto_one
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    {ι : Type*} {l : Filter ι} (r : ι → ReducedGroup N)
    (hr :
      Filter.Tendsto
        (fun i ↦
          (QuotientGroup.mk (r i) :
            ReducedQuotient N P.lattice))
        l
        (nhds
          (QuotientGroup.mk (1 : ReducedGroup N) :
            ReducedQuotient N P.lattice))) :
    ∃ γ : ι → reducedLattice N P.lattice,
      Filter.Tendsto
        (fun i ↦ r i * (γ i : ReducedGroup N)⁻¹)
        l (nhds 1) := by
  exact
    Chapter02.LocalHomeomorphLatticeLift.exists_lattice_correction_tendsto_one
      (reducedLattice N P.lattice)
      (reducedQuotient_isLocalHomeomorph N P)
      r hr

end Chapter02.HallPetrescoReducedLatticeDiscrete
