import Chapter02.HallPetresco.HallPetrescoLatticePhaseReturn

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoLatticeCommutatorNormalForm

open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoLatticePhaseReturn
open Chapter02.HallPetrescoNormalForm
open Chapter02.HallPetrescoParryPropertyH
open Chapter02.HallPetrescoProgressionReturnLift
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoTwoStepGroup

universe u v

/-- Every element of the genuine reduced Hall--Petresco lattice has a
representative whose only noncentral reduced coordinate is a linear element
from the original lattice. -/
theorem exists_linear_quadratic_normalForm
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (γ : reducedLattice N Γ) :
    ∃ a : H, a ∈ Γ ∧
      ∃ z : Fin N.torusDim → Circle,
        (γ : ReducedGroup N) =
          linearReducedElement N a * quadraticReducedElement N z := by
  rcases γ with ⟨_, ⟨s, hs, rfl⟩⟩
  have hsNormal :
      ((s : subgroup N) : Vertex → H) ∈ normalFormSubgroup N := by
    rw [← subgroup_eq_normalFormSubgroup N]
    exact s.property
  rcases hsNormal with ⟨⟨⟨g, a⟩, z⟩, hnormal⟩
  have ha : a ∈ Γ := by
    have hlinear :
        extractedLinear ((s : subgroup N) : Vertex → H) ∈ Γ := by
      exact Γ.mul_mem (Γ.inv_mem (hs 0)) (hs 1)
    have heq :
        a = extractedLinear ((s : subgroup N) : Vertex → H) := by
      calc
        a = extractedLinear (hallTuple N ((g, a), z)) := by simp
        _ = extractedLinear ((s : subgroup N) : Vertex → H) := by
          rw [hnormal]
    rwa [← heq] at hlinear
  refine ⟨a, ha, z, ?_⟩
  have hsdecomp :
      s = diagonalElement N g *
          ⟨linear a, linear_mem_subgroup N a⟩ *
          ⟨quadratic (N.centralHom z),
            quadratic_central_mem_subgroup N z⟩ := by
    apply Subtype.ext
    funext j
    change ((s : subgroup N) : Vertex → H) j =
      g * a ^ j.val * N.centralHom z ^ (j.val.choose 2)
    rw [← hnormal]
    exact hallTuple_apply N ((g, a), z) j
  change
    QuotientGroup.mk' (averagingNormalSubgroup N) s =
      linearReducedElement N a * quadraticReducedElement N z
  rw [hsdecomp, map_mul, map_mul, reduced_mk_diagonalElement, one_mul]
  rfl

/-- The canonical quadratic parameter of the commutator of a genuine
reduced-lattice element with a pure linear direction is the square of the
original ambient commutator parameter.  The unspecified quadratic part of
the lattice element disappears because it is central. -/
theorem commutatorParameter_lattice_linear
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (γ : reducedLattice N Γ)
    (a h : H)
    (w : Fin N.torusDim → Circle)
    (hγ :
      (γ : ReducedGroup N) =
        linearReducedElement N a * quadraticReducedElement N w)
    (z : Fin N.torusDim → Circle)
    (hz : N.centralHom z = ⁅a, h⁆) :
    commutatorParameter N (γ : ReducedGroup N)
        (linearReducedElement N h) =
      z ^ 2 := by
  have hcentral :
      quadraticReducedElement N w ∈
        Subgroup.center (ReducedGroup N) :=
    quadraticReducedElement_mem_center N w
  have hqcomm :
      ⁅quadraticReducedElement N w, linearReducedElement N h⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hcentral _).symm
  apply injective_quadraticReducedHom N
  rw [quadraticReducedHom_apply,
    quadraticReducedElement_commutatorParameter, map_pow,
    quadraticReducedHom_apply]
  rw [hγ,
    commutatorElement_mul_left_of_commutator_le_center
      (reducedGroup_commutator_le_center N),
    hqcomm, mul_one,
    commutatorElement_linearReducedElement N a h z hz]
  exact map_pow (quadraticReducedHom N) z 2

/-- In particular, every genuine reduced-lattice element admits ambient
lattice and torus parameters giving its commutator with a pure linear
direction by the preceding exact square formula. -/
theorem exists_lattice_commutatorParameter_linear
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (γ : reducedLattice N Γ) (h : H) :
    ∃ a : H, a ∈ Γ ∧
      ∃ w z : Fin N.torusDim → Circle,
        (γ : ReducedGroup N) =
            linearReducedElement N a * quadraticReducedElement N w ∧
          N.centralHom z = ⁅a, h⁆ ∧
          commutatorParameter N (γ : ReducedGroup N)
              (linearReducedElement N h) =
            z ^ 2 := by
  obtain ⟨a, ha, w, hγ⟩ :=
    exists_linear_quadratic_normalForm N Γ γ
  have hcomm : ⁅a, h⁆ ∈ N.centralHom.range := by
    rw [N.centralHom_range]
    rw [_root_.commutator_def]
    exact
      (Subgroup.commutator_le.mp
        (show ⁅(⊤ : Subgroup H), ⊤⁆ ≤ ⁅(⊤ : Subgroup H), ⊤⁆
          from le_rfl))
        a (Subgroup.mem_top _) h (Subgroup.mem_top _)
  obtain ⟨z, hz⟩ := hcomm
  refine ⟨a, ha, w, z, hγ, hz, ?_⟩
  exact
    commutatorParameter_lattice_linear
      N Γ γ a h w hγ z hz

/-- The lattice-corrected return sequence can be expressed entirely in
terms of original-lattice linear coefficients.  For every connected
ambient direction, the corresponding squared ambient commutator parameters
are annihilated asymptotically by the vertical character. -/
theorem exists_originalLattice_commutator_phase_return
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
    (h : H) (hh : h ∈ Subgroup.connectedComponentOfOne H) :
    ∃ n : ℕ → ℕ, (∀ k, 0 < n k) ∧
      ∃ γ : ℕ → reducedLattice N P.lattice,
        Filter.Tendsto
            (fun k ↦
              (reducedProgressionGenerator N) ^ n k *
                (γ k : ReducedGroup N)⁻¹)
            Filter.atTop (nhds 1) ∧
          ∃ a : ℕ → H, (∀ k, a k ∈ P.lattice) ∧
            ∃ w z : ℕ → (Fin N.torusDim → Circle),
              (∀ k,
                (((γ k)⁻¹ : reducedLattice N P.lattice) :
                    ReducedGroup N) =
                  linearReducedElement N (a k) *
                    quadraticReducedElement N (w k)) ∧
              (∀ k, N.centralHom (z k) = ⁅a k, h⁆) ∧
              Filter.Tendsto
                (fun k ↦ χ.toFun ((z k) ^ 2))
                Filter.atTop (nhds 1) := by
  have hg :
      linearReducedElement N h ∈
        Subgroup.connectedComponentOfOne (ReducedGroup N) :=
    linearReducedElement_mem_connectedComponentOfOne N h hh
  obtain ⟨n, hn, γ, hreturn, hphase⟩ :=
    exists_lattice_return_character_tendsto_one
      N P q χ F hFcontinuous hFinv hFvertical hFnorm
      (linearReducedElement N h) hg
  have hnormal (k : ℕ) :
      ∃ a : H, a ∈ P.lattice ∧
        ∃ w z : Fin N.torusDim → Circle,
          (((γ k)⁻¹ : reducedLattice N P.lattice) :
              ReducedGroup N) =
              linearReducedElement N a * quadraticReducedElement N w ∧
            N.centralHom z = ⁅a, h⁆ ∧
            commutatorParameter N
                (((γ k)⁻¹ : reducedLattice N P.lattice) :
                  ReducedGroup N)
                (linearReducedElement N h) =
              z ^ 2 :=
    exists_lattice_commutatorParameter_linear
      N P.lattice ((γ k)⁻¹) h
  choose a ha w z hdecomp hcentral hparam using hnormal
  refine ⟨n, hn, γ, hreturn, a, ha, w, z, ?_, hcentral, ?_⟩
  · exact hdecomp
  · apply hphase.congr'
    filter_upwards with k
    rw [← hparam k]
    rfl

end Chapter02.HallPetrescoLatticeCommutatorNormalForm
