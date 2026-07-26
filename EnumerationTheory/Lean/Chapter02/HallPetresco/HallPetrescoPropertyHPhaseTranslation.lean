import Chapter02.HallPetresco.HallPetrescoConnectedPhaseRigidity
import Chapter02.HallPetresco.HallPetrescoInvariantVerticalPhaseUniqueness
import Chapter02.HallPetresco.HallPetrescoLatticePhaseReturn
import Chapter02.HallPetresco.HallPetrescoParryPropertyH

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoPropertyHPhaseTranslation

open Chapter02.HallPetrescoConnectedPhaseRigidity
open Chapter02.HallPetrescoLatticePhaseReturn
open Chapter02.HallPetrescoParryPropertyH
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoVerticalPhase
open Chapter02.NilsystemPropertyHReduction

universe u v

/-- Swapping the inputs of the canonical two-step commutator parameter
inverts that parameter. -/
theorem commutatorParameter_swap
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g h : ReducedGroup N) :
    commutatorParameter N g h =
      (commutatorParameter N h g)⁻¹ := by
  apply injective_quadraticReducedHom N
  rw [map_inv]
  simp only [quadraticReducedHom_apply,
    quadraticReducedElement_commutatorParameter]
  simp only [commutatorElement_def, mul_inv_rev, inv_inv]
  group

/-- The vertical character of every commutator with the progression
generator is trivial under property (H). -/
theorem verticalCharacter_progressionCommutator_eq_one_of_propertyH
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (F : ReducedQuotient N P.lattice → ℂ)
    (hFcontinuous : Continuous F)
    (hFinv : ∀ y, F (reducedStep N P.lattice y) = F y)
    (hFvertical : ∀ z y,
      F (quadraticReducedElement N z • y) =
        χ.toFun z * F y)
    (hFnorm : ∀ y, ‖F y‖ = 1)
    (hproperty :
      identityTranslationSubgroup H N.translation = ⊤)
    (g : ReducedGroup N) :
    χ.toFun
        (commutatorParameter N
          (reducedProgressionGenerator N) g) = 1 := by
  let a : ReducedGroup N := reducedProgressionGenerator N
  let η : ReducedGroup N →* ℂ :=
    { toFun := fun h ↦ χ.toFun (commutatorParameter N h a)
      map_one' := by
        rw [commutatorParameter_one_left, χ.map_one]
      map_mul' := by
        intro x y
        rw [commutatorParameter_mul_left, χ.map_mul] }
  have hχinv (z : Fin N.torusDim → Circle) :
      χ.toFun z⁻¹ = (χ.toFun z)⁻¹ := by
    have hz0 : χ.toFun z ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [χ.unit_norm]
      norm_num
    apply mul_right_cancel₀ hz0
    calc
      χ.toFun z⁻¹ * χ.toFun z =
          χ.toFun (z⁻¹ * z) := (χ.map_mul z⁻¹ z).symm
      _ = χ.toFun 1 := by
        congr 1
        group
      _ = 1 := χ.map_one
      _ = (χ.toFun z)⁻¹ * χ.toFun z :=
        (inv_mul_cancel₀ hz0).symm
  have hgenerated : reducedIdentityTranslationSubgroup N ≤ η.ker := by
    rw [reducedIdentityTranslationSubgroup, identityTranslationSubgroup,
      Subgroup.closure_le]
    intro h hh
    change η h = 1
    rcases hh with hh | rfl
    · change χ.toFun (commutatorParameter N h a) = 1
      have hconnected :
          χ.toFun (commutatorParameter N a h) = 1 :=
        verticalCharacter_commutator_eq_one_of_mem_connectedComponent
          N P q χ F hFcontinuous hFinv hFvertical hFnorm h hh
          (commutatorParameter N a h)
          (quadraticReducedElement_commutatorParameter N a h).symm
      rw [commutatorParameter_swap, hχinv, hconnected, inv_one]
    · change χ.toFun (commutatorParameter N a a) = 1
      have hparam : commutatorParameter N a a = 1 := by
        apply injective_quadraticReducedHom N
        rw [quadraticReducedHom_apply,
          quadraticReducedElement_commutatorParameter]
        simp only [commutatorElement_def]
        rw [map_one]
        group
      rw [hparam, χ.map_one]
  have htop : reducedIdentityTranslationSubgroup N = ⊤ :=
    reducedIdentityTranslationSubgroup_eq_top_of_propertyH N hproperty
  have hgker : g ∈ η.ker := by
    apply hgenerated
    rw [htop]
    exact Subgroup.mem_top g
  change η g = 1 at hgker
  change χ.toFun (commutatorParameter N g a) = 1 at hgker
  rw [commutatorParameter_swap, hχinv]
  change (χ.toFun (commutatorParameter N g a))⁻¹ = 1
  rw [hgker, inv_one]

/-- Under property (H), every left translate of an invariant vertical
phase remains progression-invariant. -/
theorem leftTranslate_verticalPhase_invariant_of_propertyH
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (F : ReducedQuotient N P.lattice → ℂ)
    (hFcontinuous : Continuous F)
    (hFinv : ∀ y, F (reducedStep N P.lattice y) = F y)
    (hFvertical : ∀ z y,
      F (quadraticReducedElement N z • y) =
        χ.toFun z * F y)
    (hFnorm : ∀ y, ‖F y‖ = 1)
    (hproperty :
      identityTranslationSubgroup H N.translation = ⊤)
    (g : ReducedGroup N) :
    ∀ y, F (g • reducedStep N P.lattice y) = F (g • y) := by
  intro y
  let z :=
    commutatorParameter N (reducedProgressionGenerator N) g
  have hz :
      ⁅reducedProgressionGenerator N, g⁆ =
        quadraticReducedElement N z :=
    (quadraticReducedElement_commutatorParameter
      N (reducedProgressionGenerator N) g).symm
  have hχ :
      χ.toFun z = 1 :=
    verticalCharacter_progressionCommutator_eq_one_of_propertyH
      N P q χ F hFcontinuous hFinv hFvertical hFnorm hproperty g
  have heigen :=
    leftTranslate_verticalPhase_eigenrelation
      N P.lattice χ F hFinv hFvertical g z hz y
  rw [hχ, one_mul] at heigen
  exact heigen

end Chapter02.HallPetrescoPropertyHPhaseTranslation
