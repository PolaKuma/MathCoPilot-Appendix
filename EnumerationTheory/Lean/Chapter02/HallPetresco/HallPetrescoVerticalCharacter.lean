import Chapter02.HallPetresco.CompactAbelianSubgroupAnnihilator
import Chapter02.HallPetresco.HallPetrescoCentralExtensionMinimality
import Chapter02.HallPetresco.MultiplicativeTorusCharacter

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoVerticalCharacter

open Chapter02.CompactAbelianSubgroupAnnihilator
open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoReducedQuotient

universe u v

/-- Failure of full quadratic recurrence produces a nontrivial vertical
circle character which is identically one on every quadratic return.
This is the precise spectral obstruction used in the Parry argument. -/
theorem exists_verticalCharacter_of_quadraticReturnSubgroup_ne_top
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (hne : quadraticReturnSubgroup N Γ q ≠ ⊤) :
    ∃ χ : Chapter02.ContinuousMultiplicativeCircleCharacter
        (Fin N.torusDim → Circle),
      (∀ z ∈ quadraticReturnSubgroup N Γ q, χ.toFun z = 1) ∧
        ∃ z, χ.toFun z ≠ 1 := by
  have hnotall :
      ¬ ∀ z : Fin N.torusDim → Circle,
        z ∈ quadraticReturnSubgroup N Γ q := by
    intro hall
    apply hne
    apply top_unique
    intro z _
    exact hall z
  push_neg at hnotall
  obtain ⟨z, hz⟩ := hnotall
  obtain ⟨χ, hχreturn, hχz⟩ :=
    exists_character_trivial_on_closedSubgroup
      (quadraticReturnSubgroup N Γ q)
      (quadraticReturnSubgroup_isClosed N Γ q) hz
  exact ⟨χ, hχreturn, z, hχz⟩

/-- In finite-torus coordinates, a failure of full return is witnessed by
a nonzero integer Fourier frequency whose monomial is one on every return
parameter. -/
theorem exists_nonzero_frequency_of_quadraticReturnSubgroup_ne_top
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (hne : quadraticReturnSubgroup N Γ q ≠ ⊤) :
    ∃ k : Fin N.torusDim → ℤ, k ≠ 0 ∧
      ∀ z ∈ quadraticReturnSubgroup N Γ q,
        UnitAddTorus.mFourier k
          (fun i =>
            (AddCircle.homeomorphCircle one_ne_zero).symm (z i)) = 1 := by
  obtain ⟨χ, hχreturn, hχnontrivial⟩ :=
    exists_verticalCharacter_of_quadraticReturnSubgroup_ne_top
      N Γ q hne
  obtain ⟨k, hk0, hk⟩ :=
    Chapter02.MultiplicativeTorusCharacter.exists_nonzero_frequency
      χ hχnontrivial
  refine ⟨k, hk0, fun z hz ↦ ?_⟩
  rw [← hk z]
  exact hχreturn z hz

/-- Full quadratic recurrence is equivalent to absence, at every base point,
of a nontrivial continuous vertical character annihilating all returns. -/
theorem hasFullQuadraticFiberOrbitClosure_iff_no_verticalCharacter
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) :
    HasFullQuadraticFiberOrbitClosure N Γ ↔
      ∀ q : ReducedQuotient N Γ,
        ¬ ∃ χ : Chapter02.ContinuousMultiplicativeCircleCharacter
            (Fin N.torusDim → Circle),
          (∀ z ∈ quadraticReturnSubgroup N Γ q, χ.toFun z = 1) ∧
            ∃ z, χ.toFun z ≠ 1 := by
  rw [hasFullQuadraticFiberOrbitClosure_iff_returnSubgroup_eq_top]
  constructor
  · intro htop q
    rintro ⟨χ, hχreturn, z, hχz⟩
    apply hχz
    apply hχreturn
    rw [htop q]
    exact Subgroup.mem_top z
  · intro hnone q
    by_contra hne
    exact hnone q
      (exists_verticalCharacter_of_quadraticReturnSubgroup_ne_top
        N Γ q hne)

end Chapter02.HallPetrescoVerticalCharacter
