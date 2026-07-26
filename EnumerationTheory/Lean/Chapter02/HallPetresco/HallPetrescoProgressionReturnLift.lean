import Chapter02.HallPetresco.HallPetrescoReducedLatticeDiscrete
import Chapter02.HallPetresco.HallPetrescoReducedRecurrence
import Chapter02.HallPetresco.HallPetrescoReducedSecondCountable

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoProgressionReturnLift

open Chapter02.HallPetrescoReducedLatticeDiscrete
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedRecurrence
open Chapter02.HallPetrescoReducedSecondCountable
open Chapter02.HallPetrescoReducedAbelianFactor

universe u v

/-- Iterating the reduced Hall--Petresco step from the identity coset is
the quotient class of the corresponding power of the progression
generator. -/
theorem reducedStep_iterate_mk_one
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (n : ℕ) :
    ((reducedStep N Γ)^[n])
        (QuotientGroup.mk (1 : ReducedGroup N) :
          ReducedQuotient N Γ) =
      (QuotientGroup.mk ((reducedProgressionGenerator N) ^ n) :
        ReducedQuotient N Γ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      change
        (QuotientGroup.mk
            (reducedProgressionGenerator N *
              (reducedProgressionGenerator N) ^ n) :
            ReducedQuotient N Γ) =
          QuotientGroup.mk ((reducedProgressionGenerator N) ^ (n + 1))
      rw [pow_succ']

/-- A convergent sequence of concrete progression returns in the reduced
quotient admits corrections by the actual reduced lattice which converge
to the identity upstairs.  This is the progression-specialized local lift
needed in the Parry--Leibman argument. -/
theorem exists_reducedLattice_correction_of_progression_returns
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    {ι : Type*} {l : Filter ι} (n : ι → ℕ)
    (hn :
      Tendsto
        (fun i ↦
          ((reducedStep N P.lattice)^[n i])
            (QuotientGroup.mk (1 : ReducedGroup N) :
              ReducedQuotient N P.lattice))
        l
        (nhds
          (QuotientGroup.mk (1 : ReducedGroup N) :
            ReducedQuotient N P.lattice))) :
    ∃ γ : ι → reducedLattice N P.lattice,
      Tendsto
        (fun i ↦
          (reducedProgressionGenerator N) ^ n i *
            (γ i : ReducedGroup N)⁻¹)
        l (nhds 1) := by
  apply exists_reducedLattice_correction_tendsto_one
    N P (fun i ↦ (reducedProgressionGenerator N) ^ n i)
  simpa only [reducedStep_iterate_mk_one] using hn

/-- Recurrence of the identity coset produces an actual sequence of
positive progression powers converging back to that coset. -/
theorem exists_progression_return_sequence
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    letI : CompactSpace (ReducedQuotient N P.lattice) :=
      Chapter02.HallPetrescoCompactReduced.reducedQuotientCompactSpaceOfPresentation
        N P
    letI : T2Space (ReducedQuotient N P.lattice) :=
      Chapter02.HallPetrescoReducedHausdorff.reducedQuotientT2Space N P
    letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
      reducedQuotientSecondCountableTopology N P
    letI : TopologicalSpace.MetrizableSpace
        (ReducedQuotient N P.lattice) := inferInstance
    letI : MetricSpace (ReducedQuotient N P.lattice) :=
      TopologicalSpace.metrizableSpaceMetric _
    ∃ n : ℕ → ℕ,
      (∀ k, 0 < n k) ∧
        Tendsto
          (fun k ↦
            ((reducedStep N P.lattice)^[n k])
              (QuotientGroup.mk (1 : ReducedGroup N) :
                ReducedQuotient N P.lattice))
          atTop
          (nhds
            (QuotientGroup.mk (1 : ReducedGroup N) :
              ReducedQuotient N P.lattice)) := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    Chapter02.HallPetrescoCompactReduced.reducedQuotientCompactSpaceOfPresentation
      N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    Chapter02.HallPetrescoReducedHausdorff.reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  letI : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  let q : ReducedQuotient N P.lattice :=
    QuotientGroup.mk (1 : ReducedGroup N)
  let T := reducedStep N P.lattice
  have hrec :
      q ∈ closure
        (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T (T q)) :=
    reducedStep_recurrent N P q
  have hclose (k : ℕ) :
      ∃ n : ℕ, 0 < n ∧
        dist ((T^[n]) q) q < 1 / ((k : ℝ) + 1) := by
    rw [Metric.mem_closure_iff] at hrec
    obtain ⟨y, ⟨m, rfl⟩, hy⟩ :=
      hrec (1 / ((k : ℝ) + 1)) (by positivity)
    refine ⟨m + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply]
    simpa only [dist_comm] using hy
  choose n hnpos hnclose using hclose
  refine ⟨n, hnpos, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hevent :
      ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat
      (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
  rw [eventually_atTop] at hevent
  obtain ⟨K, hK⟩ := hevent
  exact ⟨K, fun k hk ↦ (hnclose k).trans (hK k hk)⟩

/-- Combining recurrence with the local covering lift yields concrete
lattice-corrected positive powers of the progression generator converging
to the identity in the reduced Hall--Petresco group. -/
theorem exists_corrected_progression_return_sequence
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    ∃ n : ℕ → ℕ, (∀ k, 0 < n k) ∧
      ∃ γ : ℕ → reducedLattice N P.lattice,
        Tendsto
          (fun k ↦
            (reducedProgressionGenerator N) ^ n k *
              (γ k : ReducedGroup N)⁻¹)
          atTop (nhds 1) := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    Chapter02.HallPetrescoCompactReduced.reducedQuotientCompactSpaceOfPresentation
      N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    Chapter02.HallPetrescoReducedHausdorff.reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  letI : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨n, hnpos, hn⟩ := exists_progression_return_sequence N P
  obtain ⟨γ, hγ⟩ :=
    exists_reducedLattice_correction_of_progression_returns N P n hn
  exact ⟨n, hnpos, γ, hγ⟩

private theorem commutatorElement_mem_commutator
    {G : Type*} [Group G] (g h : G) :
    ⁅g, h⁆ ∈ _root_.commutator G := by
  rw [_root_.commutator_def]
  exact
    (Subgroup.commutator_le.mp
      (show ⁅(⊤ : Subgroup G), ⊤⁆ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ from le_rfl))
      g (Subgroup.mem_top _) h (Subgroup.mem_top _)

/-- In a group whose full commutator subgroup is central, a commutator is
multiplicative in its first variable. -/
theorem commutatorElement_mul_left_of_commutator_le_center
    {G : Type*} [Group G]
    (hstep : _root_.commutator G ≤ Subgroup.center G)
    (x y g : G) :
    ⁅x * y, g⁆ = ⁅x, g⁆ * ⁅y, g⁆ := by
  have hxc :
      ⁅x, g⁆ ∈ Subgroup.center G :=
    hstep (commutatorElement_mem_commutator x g)
  have hyc :
      ⁅y, g⁆ ∈ Subgroup.center G :=
    hstep (commutatorElement_mem_commutator y g)
  have hxcomm (z : G) : z * ⁅x, g⁆ = ⁅x, g⁆ * z :=
    Subgroup.mem_center_iff.mp hxc z
  have hycomm (z : G) : z * ⁅y, g⁆ = ⁅y, g⁆ * z :=
    Subgroup.mem_center_iff.mp hyc z
  simp only [commutatorElement_def]
  rw [mul_inv_rev]
  calc
    x * y * g * (y⁻¹ * x⁻¹) * g⁻¹ =
        x * (y * g * y⁻¹ * g⁻¹) * g * x⁻¹ * g⁻¹ := by
          group
    _ = x * ⁅y, g⁆ * g * x⁻¹ * g⁻¹ := by
          simp only [commutatorElement_def]
    _ = ⁅y, g⁆ * (x * g * x⁻¹ * g⁻¹) := by
          rw [hycomm x]
          group
    _ = ⁅x, g⁆ * ⁅y, g⁆ := by
          rw [hycomm ⁅x, g⁆]
          simp only [commutatorElement_def]

/-- In the same two-step situation, commuting a power with a fixed element
raises the basic commutator to that power. -/
theorem commutatorElement_pow_left_of_commutator_le_center
    {G : Type*} [Group G]
    (hstep : _root_.commutator G ≤ Subgroup.center G)
    (a g : G) (n : ℕ) :
    ⁅a ^ n, g⁆ = ⁅a, g⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ,
        commutatorElement_mul_left_of_commutator_le_center
          hstep, ih, pow_succ]

/-- For an actual corrected progression-return sequence, commutation with
any fixed reduced group element converges to the identity.  The displayed
factorization isolates exactly the residual lattice commutator phase. -/
theorem corrected_progression_commutator_tendsto_one
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    {ι : Type*} {l : Filter ι}
    (n : ι → ℕ)
    (γ : ι → ReducedGroup N)
    (hreturn :
      Tendsto
        (fun i ↦
          (reducedProgressionGenerator N) ^ n i * (γ i)⁻¹)
        l (nhds 1))
    (g : ReducedGroup N) :
    Tendsto
      (fun i ↦
        ⁅reducedProgressionGenerator N, g⁆ ^ n i *
          ⁅(γ i)⁻¹, g⁆)
      l (nhds 1) := by
  let r : ι → ReducedGroup N :=
    fun i ↦ (reducedProgressionGenerator N) ^ n i * (γ i)⁻¹
  let c : ReducedGroup N → ReducedGroup N :=
    fun x ↦ ⁅x, g⁆
  have hc : Continuous c := by
    dsimp only [c, commutatorElement_def]
    fun_prop
  have ht : Tendsto (fun i ↦ c (r i)) l (nhds (c 1)) :=
    hc.continuousAt.tendsto.comp hreturn
  have hone : c 1 = 1 := by simp [c]
  rw [hone] at ht
  convert ht using 1
  funext i
  dsimp only [c, r]
  rw [commutatorElement_mul_left_of_commutator_le_center
      (reducedGroup_commutator_le_center N),
    commutatorElement_pow_left_of_commutator_le_center
      (reducedGroup_commutator_le_center N)]

end Chapter02.HallPetrescoProgressionReturnLift
