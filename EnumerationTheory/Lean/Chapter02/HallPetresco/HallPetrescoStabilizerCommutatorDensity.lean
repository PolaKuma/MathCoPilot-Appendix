import Chapter02.HallPetresco.HallPetrescoVerticalPhase

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoStabilizerCommutatorDensity

open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoVerticalCharacter
open Chapter02.HallPetrescoVerticalPhase

universe u v

/-- Quadratic parameters realized by commutators of the progression
generator with actual elements of a given orbit-closure stabilizer. -/
def progressionCommutatorParameters
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ) :
    Set (Fin N.torusDim → Circle) :=
  {z | ∃ g : ReducedGroup N,
    g ∈ orbitClosureStabilizer N Γ q ∧
      ⁅reducedProgressionGenerator N, g⁆ =
        quadraticReducedElement N z}

/-- A concrete sufficient Parry--Leibman density statement: at every point,
commutators of the progression generator with its orbit-closure stabilizer
are dense in the complete quadratic central torus.  The theorem below only
uses this as a sufficient condition; no converse is asserted. -/
def HasDenseProgressionCommutatorParameters
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) : Prop :=
  ∀ q : ReducedQuotient N Γ,
    Dense (progressionCommutatorParameters N Γ q)

/-- Dense stabilizer commutator parameters rule out every nontrivial
vertical phase and therefore force the complete quadratic fiber into every
progression orbit closure. -/
theorem hasFullQuadraticFiberOrbitClosure_of_denseProgressionCommutators
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hdense :
      HasDenseProgressionCommutatorParameters N P.lattice) :
    HasFullQuadraticFiberOrbitClosure N P.lattice := by
  rw [hasFullQuadraticFiberOrbitClosure_iff_returnSubgroup_eq_top]
  intro q
  by_contra hne
  obtain ⟨χ, hχreturn, hχnontrivial⟩ :=
    exists_verticalCharacter_of_quadraticReturnSubgroup_ne_top
      N P.lattice q hne
  obtain ⟨F, hFcontinuous, hFinv, hFvertical, _hFnorm,
      hFq, _hFnonconstant⟩ :=
    exists_continuous_invariant_verticalPhase
      N P q χ hχreturn hχnontrivial
  let S : Set (Fin N.torusDim → Circle) :=
    progressionCommutatorParameters N P.lattice q
  let E : Set (Fin N.torusDim → Circle) :=
    {z | χ.toFun z = 1}
  have hSE : S ⊆ E := by
    rintro z ⟨g, hg, hz⟩
    exact
      verticalCharacter_commutator_eq_one_of_mem_orbitClosureStabilizer
        N P.lattice q χ F hFcontinuous hFinv hFvertical
        (by rw [hFq]; exact one_ne_zero) g hg z hz
  have hEclosed : IsClosed E :=
    isClosed_eq χ.continuous continuous_const
  have hclosure : closure S ⊆ E :=
    closure_minimal hSE hEclosed
  have hSdense : Dense S := hdense q
  rw [hSdense.closure_eq] at hclosure
  obtain ⟨z, hz⟩ := hχnontrivial
  exact hz (hclosure (Set.mem_univ z))

/-- Consequently the same density statement gives minimality of the actual
reduced Hall--Petresco translation on the genuine compact quotient. -/
theorem everyOrbitHitsOpen_reducedStep_of_denseProgressionCommutators
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hdense :
      HasDenseProgressionCommutatorParameters N P.lattice) :
    Chapter02.HostKraStructuredRecurrence.EveryOrbitHitsOpen
      (reducedStep N P.lattice) :=
  everyOrbitHitsOpen_reducedStep_of_fullQuadraticFiber
    N P
    (hasFullQuadraticFiberOrbitClosure_of_denseProgressionCommutators
      N P hdense)

end Chapter02.HallPetrescoStabilizerCommutatorDensity
