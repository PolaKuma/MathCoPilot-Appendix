import Chapter02.HallPetresco.HallPetrescoConnectedPhaseRigidity
import Chapter02.HallPetresco.HallPetrescoProgressionReturnLift

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoLatticePhaseReturn

open Chapter02.HallPetrescoConnectedPhaseRigidity
open Chapter02.HallPetrescoProgressionReturnLift
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedQuotient

universe u v

/-- The quadratic torus is homeomorphic to its concrete image in the
reduced Hall--Petresco group. -/
def quadraticRangeHomeomorph
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ) :
    (Fin N.torusDim → Circle) ≃ₜ
      Set.range (quadraticReducedHom N) :=
  (isClosedEmbedding_quadraticReducedHom N).isEmbedding.toHomeomorph

private theorem commutatorElement_mem_reduced_commutator
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g h : ReducedGroup N) :
    ⁅g, h⁆ ∈ _root_.commutator (ReducedGroup N) := by
  rw [_root_.commutator_def]
  exact
    (Subgroup.commutator_le.mp
      (show
        ⁅(⊤ : Subgroup (ReducedGroup N)), ⊤⁆ ≤
          ⁅(⊤ : Subgroup (ReducedGroup N)), ⊤⁆ from le_rfl))
      g (Subgroup.mem_top _) h (Subgroup.mem_top _)

private theorem commutatorElement_mem_quadratic_range
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g h : ReducedGroup N) :
    ⁅g, h⁆ ∈ Set.range (quadraticReducedHom N) := by
  have hc :=
    commutatorElement_mem_reduced_commutator N g h
  rw [commutator_reducedGroup_eq_quadratic_range N] at hc
  obtain ⟨z, hz⟩ := hc
  exact ⟨z, hz⟩

/-- The canonical quadratic-torus parameter of a reduced commutator. -/
def commutatorParameter
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g h : ReducedGroup N) :
    Fin N.torusDim → Circle :=
  (quadraticRangeHomeomorph N).symm
    ⟨⁅g, h⁆, commutatorElement_mem_quadratic_range N g h⟩

theorem quadraticReducedElement_commutatorParameter
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g h : ReducedGroup N) :
    quadraticReducedElement N (commutatorParameter N g h) =
      ⁅g, h⁆ := by
  exact congrArg Subtype.val
    ((quadraticRangeHomeomorph N).apply_symm_apply
      ⟨⁅g, h⁆, commutatorElement_mem_quadratic_range N g h⟩)

/-- For fixed right input, the canonical commutator parameter varies
continuously with the left input. -/
theorem continuous_commutatorParameter_left
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (h : ReducedGroup N) :
    Continuous (fun g ↦ commutatorParameter N g h) := by
  let c : ReducedGroup N → Set.range (quadraticReducedHom N) :=
    fun g ↦
      ⟨⁅g, h⁆, commutatorElement_mem_quadratic_range N g h⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    dsimp only [c, commutatorElement_def]
    fun_prop
  exact (quadraticRangeHomeomorph N).continuous_symm.comp hc

@[simp]
theorem commutatorParameter_one_left
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (g : ReducedGroup N) :
    commutatorParameter N 1 g = 1 := by
  apply injective_quadraticReducedHom N
  rw [quadraticReducedHom_apply,
    quadraticReducedElement_commutatorParameter]
  have hcomm : ⁅(1 : ReducedGroup N), g⁆ = 1 := by
    simp only [commutatorElement_def, one_mul, inv_one, mul_one]
    group
  rw [hcomm]
  exact (map_one (quadraticReducedHom N)).symm

theorem commutatorParameter_mul_left
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (x y g : ReducedGroup N) :
    commutatorParameter N (x * y) g =
      commutatorParameter N x g * commutatorParameter N y g := by
  apply injective_quadraticReducedHom N
  rw [map_mul]
  simp only [quadraticReducedHom_apply,
    quadraticReducedElement_commutatorParameter]
  exact
    commutatorElement_mul_left_of_commutator_le_center
      (reducedGroup_commutator_le_center N) x y g

theorem commutatorParameter_pow_left
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (a g : ReducedGroup N) (n : ℕ) :
    commutatorParameter N (a ^ n) g =
      commutatorParameter N a g ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, commutatorParameter_mul_left, ih, pow_succ]

/-- Connected-phase rigidity removes the pure progression factor from a
lattice-corrected return.  Thus the vertical character of the remaining
genuine lattice commutator converges to one. -/
theorem lattice_commutator_character_tendsto_one
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
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
    {ι : Type*} {l : Filter ι}
    (n : ι → ℕ) (γ : ι → ReducedGroup N)
    (hreturn :
      Tendsto
        (fun i ↦
          (reducedProgressionGenerator N) ^ n i * (γ i)⁻¹)
        l (nhds 1))
    (g : ReducedGroup N)
    (hg : g ∈ Subgroup.connectedComponentOfOne (ReducedGroup N)) :
    Tendsto
      (fun i ↦ χ.toFun (commutatorParameter N (γ i)⁻¹ g))
      l (nhds 1) := by
  let a := reducedProgressionGenerator N
  let p := commutatorParameter N a g
  have hpquad :
      ⁅a, g⁆ = quadraticReducedElement N p :=
    (quadraticReducedElement_commutatorParameter N a g).symm
  have hpχ : χ.toFun p = 1 :=
    verticalCharacter_commutator_eq_one_of_mem_connectedComponent
      N P q χ F hFcontinuous hFinv hFvertical hFnorm
      g hg p hpquad
  have hpχ' :
      χ.toFun (commutatorParameter N a g) = 1 := by
    simpa only [p] using hpχ
  have hparam :
      Tendsto
        (fun i ↦
          commutatorParameter N
            (a ^ n i * (γ i)⁻¹) g)
        l (nhds 1) := by
    have hc := continuous_commutatorParameter_left N g
    simpa only [commutatorParameter_one_left] using
      hc.continuousAt.tendsto.comp hreturn
  have hχparam :
      Tendsto
        (fun i ↦
          χ.toFun
            (commutatorParameter N
              (a ^ n i * (γ i)⁻¹) g))
        l (nhds 1) := by
    simpa only [χ.map_one] using
      χ.continuous.continuousAt.tendsto.comp hparam
  have hχpow (z : Fin N.torusDim → Circle) :
      ∀ m : ℕ, χ.toFun (z ^ m) = χ.toFun z ^ m := by
    intro m
    induction m with
    | zero => simp only [pow_zero, χ.map_one]
    | succ m ih =>
        rw [pow_succ, χ.map_mul, ih, pow_succ]
  simpa only [commutatorParameter_mul_left,
    commutatorParameter_pow_left, χ.map_mul, hχpow,
    hpχ', one_pow, one_mul] using hχparam

/-- For every connected reduced direction, recurrence supplies a concrete
positive return sequence whose genuine lattice-correction commutator phase
converges to one. -/
theorem exists_lattice_return_character_tendsto_one
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
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
    (g : ReducedGroup N)
    (hg : g ∈ Subgroup.connectedComponentOfOne (ReducedGroup N)) :
    ∃ n : ℕ → ℕ, (∀ k, 0 < n k) ∧
      ∃ γ : ℕ → reducedLattice N P.lattice,
        Tendsto
            (fun k ↦
              (reducedProgressionGenerator N) ^ n k *
                (γ k : ReducedGroup N)⁻¹)
            atTop (nhds 1) ∧
          Tendsto
            (fun k ↦
              χ.toFun
                (commutatorParameter N
                  ((γ k : ReducedGroup N)⁻¹) g))
            atTop (nhds 1) := by
  obtain ⟨n, hnpos, γ, hreturn⟩ :=
    exists_corrected_progression_return_sequence N P
  refine ⟨n, hnpos, γ, hreturn, ?_⟩
  exact
    lattice_commutator_character_tendsto_one
      N P q χ F hFcontinuous hFinv hFvertical hFnorm
      n (fun k ↦ (γ k : ReducedGroup N)) hreturn g hg

end Chapter02.HallPetrescoLatticePhaseReturn
