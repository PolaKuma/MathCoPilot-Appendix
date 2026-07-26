import Chapter02.HallPetresco.HallPetrescoStabilizerCommutatorDensity

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoStabilizerPairwiseCommutator

open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedRecurrence
open Chapter02.HallPetrescoStabilizerCommutatorDensity
open Chapter02.HallPetrescoVerticalCharacter

universe u v

/-- The commutator of two elements preserving one progression orbit
closure preserves that orbit closure as well.  This records the full
pairwise stabilizer information, rather than only commutators with the
progression generator. -/
theorem commutator_mem_orbitClosureStabilizer
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (g h : ReducedGroup N)
    (hg : g ∈ orbitClosureStabilizer N Γ q)
    (hh : h ∈ orbitClosureStabilizer N Γ q) :
    ⁅g, h⁆ ∈ orbitClosureStabilizer N Γ q := by
  let K := orbitClosureStabilizer N Γ q
  change g * h * g⁻¹ * h⁻¹ ∈ K
  exact K.mul_mem
    (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg))
    (K.inv_mem hh)

/-- Consequently every vertical character annihilating the actual
quadratic return subgroup annihilates each pairwise stabilizer
commutator. -/
theorem verticalCharacter_commutator_eq_one_of_mem_stabilizers
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (hχreturn :
      ∀ z ∈ quadraticReturnSubgroup N Γ q, χ.toFun z = 1)
    (g h : ReducedGroup N)
    (hg : g ∈ orbitClosureStabilizer N Γ q)
    (hh : h ∈ orbitClosureStabilizer N Γ q)
    (z : Fin N.torusDim → Circle)
    (hz : ⁅g, h⁆ = quadraticReducedElement N z) :
    χ.toFun z = 1 := by
  apply hχreturn z
  apply
    (mem_quadraticReturnSubgroup_iff_mem_orbitClosureStabilizer
      N Γ q z).mpr
  rw [← hz]
  exact commutator_mem_orbitClosureStabilizer N Γ q g h hg hh

/-- Every pairwise stabilizer commutator has a unique concrete quadratic
parameter, and every return-annihilating vertical character vanishes on
that parameter. -/
theorem exists_unique_quadraticParameter_commutator_of_mem_stabilizers
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (hχreturn :
      ∀ z ∈ quadraticReturnSubgroup N Γ q, χ.toFun z = 1)
    (g h : ReducedGroup N)
    (hg : g ∈ orbitClosureStabilizer N Γ q)
    (hh : h ∈ orbitClosureStabilizer N Γ q) :
    ∃! z : Fin N.torusDim → Circle,
      ⁅g, h⁆ = quadraticReducedElement N z ∧ χ.toFun z = 1 := by
  have hcomm :
      ⁅g, h⁆ ∈ _root_.commutator (ReducedGroup N) := by
    rw [_root_.commutator_def]
    exact
      (Subgroup.commutator_le.mp
        (show ⁅(⊤ : Subgroup (ReducedGroup N)), ⊤⁆ ≤
            ⁅(⊤ : Subgroup (ReducedGroup N)), ⊤⁆ from le_rfl))
        g (Subgroup.mem_top _) h (Subgroup.mem_top _)
  rw [commutator_reducedGroup_eq_quadratic_range N] at hcomm
  obtain ⟨z, hz⟩ := hcomm
  refine ⟨z, ⟨hz.symm, ?_⟩, ?_⟩
  · exact
      verticalCharacter_commutator_eq_one_of_mem_stabilizers
        N Γ q χ hχreturn g h hg hh z hz.symm
  · rintro w ⟨hw, _⟩
    apply injective_quadraticReducedHom N
    rw [quadraticReducedHom_apply, quadraticReducedHom_apply]
    exact hw.symm.trans hz.symm

/-- Quadratic parameters represented by commutators of arbitrary pairs in
one progression orbit-closure stabilizer. -/
def pairwiseStabilizerCommutatorParameters
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    Set (Fin N.torusDim → Circle) :=
  {z | ∃ g h : ReducedGroup N,
    g ∈ orbitClosureStabilizer N Γ q ∧
    h ∈ orbitClosureStabilizer N Γ q ∧
    ⁅g, h⁆ = quadraticReducedElement N z}

/-- The pairwise Parry density condition.  This is weaker than density of
commutators with one fixed progression generator and is the condition
naturally targeted by the actual lattice-corrected stabilizer lift. -/
def HasDensePairwiseStabilizerCommutatorParameters
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) : Prop :=
  ∀ q : ReducedQuotient N Γ,
    Dense (pairwiseStabilizerCommutatorParameters N Γ q)

/-- The earlier fixed-progression commutator density condition implies the
pairwise condition, since the progression generator itself belongs to every
orbit-closure stabilizer. -/
theorem densePairwiseCommutators_of_denseProgressionCommutators
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hdense :
      HasDenseProgressionCommutatorParameters N P.lattice) :
    HasDensePairwiseStabilizerCommutatorParameters N P.lattice := by
  intro q
  apply (hdense q).mono
  rintro z ⟨g, hg, hz⟩
  exact ⟨reducedProgressionGenerator N, g,
    reducedProgressionGenerator_mem_orbitClosureStabilizer N P q,
    hg, hz⟩

/-- Density of all pairwise stabilizer commutators rules out every proper
quadratic return subgroup.  Unlike the earlier fixed-generator criterion,
the proof uses only the intrinsic return character and subgroup closure. -/
theorem hasFullQuadraticFiberOrbitClosure_of_densePairwiseCommutators
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hdense :
      HasDensePairwiseStabilizerCommutatorParameters N P.lattice) :
    HasFullQuadraticFiberOrbitClosure N P.lattice := by
  rw [hasFullQuadraticFiberOrbitClosure_iff_returnSubgroup_eq_top]
  intro q
  by_contra hne
  obtain ⟨χ, hχreturn, hχnontrivial⟩ :=
    exists_verticalCharacter_of_quadraticReturnSubgroup_ne_top
      N P.lattice q hne
  let S : Set (Fin N.torusDim → Circle) :=
    pairwiseStabilizerCommutatorParameters N P.lattice q
  let E : Set (Fin N.torusDim → Circle) :=
    {z | χ.toFun z = 1}
  have hSE : S ⊆ E := by
    rintro z ⟨g, h, hg, hh, hz⟩
    exact
      verticalCharacter_commutator_eq_one_of_mem_stabilizers
        N P.lattice q χ hχreturn g h hg hh z hz
  have hEclosed : IsClosed E :=
    isClosed_eq χ.continuous continuous_const
  have hclosure : closure S ⊆ E :=
    closure_minimal hSE hEclosed
  have hSdense : Dense S := hdense q
  rw [hSdense.closure_eq] at hclosure
  obtain ⟨z, hz⟩ := hχnontrivial
  exact hz (hclosure (Set.mem_univ z))

/-- Hence pairwise stabilizer-commutator density gives minimality of the
actual reduced Hall--Petresco progression. -/
theorem everyOrbitHitsOpen_reducedStep_of_densePairwiseCommutators
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hdense :
      HasDensePairwiseStabilizerCommutatorParameters N P.lattice) :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
      (reducedStep N P.lattice) :=
  everyOrbitHitsOpen_reducedStep_of_fullQuadraticFiber
    N P
    (hasFullQuadraticFiberOrbitClosure_of_densePairwiseCommutators
      N P hdense)

end Chapter02.HallPetrescoStabilizerPairwiseCommutator
