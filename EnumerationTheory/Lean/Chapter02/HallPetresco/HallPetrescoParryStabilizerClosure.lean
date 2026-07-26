import Chapter02.HallPetresco.HallPetrescoParryPropertyH
import Chapter02.HallPetresco.HallPetrescoReducedRecurrence

open Classical Set
open scoped Pointwise

noncomputable section

namespace Chapter02.HallPetrescoParryStabilizerClosure

open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoParryPropertyH
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedRecurrence
open Chapter02.NilsystemPropertyHReduction

universe u v

/-- Under property `(H)`, stability under the connected component and the
progression generator forces the whole reduced Hall--Petresco group to
stabilize the progression orbit closure.

The progression-generator membership is unconditional; consequently the
only local Parry--Leibman input in this statement is the displayed
connected-component inclusion. -/
theorem orbitClosureStabilizer_eq_top_of_propertyH
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hproperty :
      identityTranslationSubgroup H N.translation = ⊤)
    (q : ReducedQuotient N P.lattice)
    (hidentity :
      Subgroup.connectedComponentOfOne (ReducedGroup N) ≤
        orbitClosureStabilizer N P.lattice q) :
    orbitClosureStabilizer N P.lattice q = ⊤ := by
  let R := ReducedGroup N
  let K : Subgroup R := orbitClosureStabilizer N P.lattice q
  have hgenerated :
      reducedIdentityTranslationSubgroup N ≤ K := by
    rw [reducedIdentityTranslationSubgroup, identityTranslationSubgroup,
      Subgroup.closure_le]
    intro g hg
    rcases hg with hg | rfl
    · exact hidentity hg
    · exact reducedProgressionGenerator_mem_orbitClosureStabilizer N P q
  have htop :
      reducedIdentityTranslationSubgroup N = ⊤ :=
    reducedIdentityTranslationSubgroup_eq_top_of_propertyH N hproperty
  apply top_unique
  simpa only [htop] using hgenerated

/-- Hence the same local connected-component statement makes every
reduced progression orbit dense in the genuine compact quotient. -/
theorem closure_forwardOrbit_eq_univ_of_propertyH
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hproperty :
      identityTranslationSubgroup H N.translation = ⊤)
    (q : ReducedQuotient N P.lattice)
    (hidentity :
      Subgroup.connectedComponentOfOne (ReducedGroup N) ≤
        orbitClosureStabilizer N P.lattice q) :
    closure
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (reducedStep N P.lattice) q) =
      Set.univ := by
  have htop :=
    orbitClosureStabilizer_eq_top_of_propertyH
      N P hproperty q hidentity
  have hq :
      q ∈ closure
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
          (reducedStep N P.lattice) q) :=
    subset_closure ⟨0, by simp⟩
  apply Set.eq_univ_of_forall
  intro r
  obtain ⟨g, rfl⟩ :=
    MulAction.exists_smul_eq (ReducedGroup N) q r
  have hg :
      g ∈ orbitClosureStabilizer N P.lattice q := by
    rw [htop]
    exact Subgroup.mem_top g
  change g ∈ MulAction.stabilizer (ReducedGroup N)
    (closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N P.lattice) q)) at hg
  rw [MulAction.mem_stabilizer_iff] at hg
  rw [← hg]
  exact ⟨q, hq, rfl⟩

end Chapter02.HallPetrescoParryStabilizerClosure
