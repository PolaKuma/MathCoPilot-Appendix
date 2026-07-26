import Chapter02.HallPetresco.HallPetrescoVerticalPhase
import Chapter02.HallPetresco.HallPetrescoReducedSecondCountable
import Chapter02.HallPetresco.MinimalContinuousEigenfunction

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HallPetrescoConnectedPhaseRigidity

open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedSecondCountable
open Chapter02.HallPetrescoVerticalPhase
open Chapter02.MinimalContinuousEigenfunction

universe u v

/-- A progression-invariant unit vertical phase annihilates every
progression commutator coming from the identity component of the reduced
Hall--Petresco group. -/
theorem verticalCharacter_commutator_eq_one_of_mem_connectedComponent
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
    (g : ReducedGroup N)
    (hg :
      g ∈ Subgroup.connectedComponentOfOne (ReducedGroup N))
    (z : Fin N.torusDim → Circle)
    (hz :
      ⁅reducedProgressionGenerator N, g⁆ =
        quadraticReducedElement N z) :
    χ.toFun z = 1 := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  let R := ReducedGroup N
  let Y := ReducedQuotient N P.lattice
  let T : Y → Y := reducedStep N P.lattice
  let C := Subgroup.connectedComponentOfOne R
  letI : ConnectedSpace C := by
    change ConnectedSpace (connectedComponent (1 : R))
    exact isConnected_iff_connectedSpace.mp
      (isConnected_connectedComponent (x := (1 : R)))
  let e :
      (Fin N.torusDim → Circle) ≃ₜ
        Set.range (quadraticReducedHom N) :=
    (isClosedEmbedding_quadraticReducedHom N).isEmbedding.toHomeomorph
  let commRange : C → Set.range (quadraticReducedHom N) :=
    fun h ↦
      ⟨⁅reducedProgressionGenerator N, (h : R)⁆, by
        have hcomm :
            ⁅reducedProgressionGenerator N, (h : R)⁆ ∈
              _root_.commutator R := by
          rw [_root_.commutator_def]
          exact
            (Subgroup.commutator_le.mp
              (show ⁅(⊤ : Subgroup R), ⊤⁆ ≤
                  ⁅(⊤ : Subgroup R), ⊤⁆ from le_rfl))
              (reducedProgressionGenerator N) (Subgroup.mem_top _)
              h (Subgroup.mem_top _)
        rw [commutator_reducedGroup_eq_quadratic_range N] at hcomm
        exact hcomm⟩
  have hcommRange : Continuous commRange := by
    apply Continuous.subtype_mk
    dsimp only [commRange]
    change Continuous (fun h : C ↦
      reducedProgressionGenerator N * (h : R) *
        (reducedProgressionGenerator N)⁻¹ * (h : R)⁻¹)
    fun_prop
  let param : C → (Fin N.torusDim → Circle) :=
    fun h ↦ e.symm (commRange h)
  have hparamContinuous : Continuous param :=
    e.continuous_symm.comp hcommRange
  have hparam (h : C) :
      quadraticReducedElement N (param h) =
        ⁅reducedProgressionGenerator N, (h : R)⁆ := by
    have heq := e.apply_symm_apply (commRange h)
    exact congrArg Subtype.val heq
  let lam : C → ℂ := fun h ↦ (χ.toFun (param h))⁻¹
  have hχnonzero (h : C) : χ.toFun (param h) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [χ.unit_norm]
    norm_num
  have hlamContinuous : Continuous lam := by
    apply (χ.continuous.comp hparamContinuous).inv₀
    intro h
    simpa only [Function.comp_apply] using hχnonzero h
  have hlamEigen :
      ∀ h, IsNormalizedContinuousEigenvalue T q (lam h) := by
    intro h
    have hFqnonzero : F ((h : R) • q) ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hFnorm]
      norm_num
    let f : C(Y, ℂ) :=
      ⟨fun y ↦ F ((h : R) • y) * (F ((h : R) • q))⁻¹,
        (hFcontinuous.comp
          (continuous_const.smul continuous_id)).mul
            ((hFcontinuous.comp
              (continuous_const.smul continuous_const)).inv₀
                (fun _ ↦ hFqnonzero))⟩
    refine ⟨by simp [lam, norm_inv, χ.unit_norm], f, ?_, ?_⟩
    · intro y
      have heigen :=
        leftTranslate_verticalPhase_eigenrelation
          N P.lattice χ F hFinv hFvertical
          (h : R) (param h) (hparam h).symm y
      have htranslate :
          F ((h : R) • T y) =
            (χ.toFun (param h))⁻¹ * F ((h : R) • y) := by
        calc
          F ((h : R) • T y) =
              1 * F ((h : R) • T y) := by rw [one_mul]
          _ = ((χ.toFun (param h))⁻¹ *
                χ.toFun (param h)) *
              F ((h : R) • T y) := by
                rw [inv_mul_cancel₀ (hχnonzero h)]
          _ = (χ.toFun (param h))⁻¹ *
              (χ.toFun (param h) *
                F ((h : R) • T y)) := by ring
          _ = (χ.toFun (param h))⁻¹ *
              F ((h : R) • y) := by rw [heigen]
      change
        F ((h : R) • T y) * (F ((h : R) • q))⁻¹ =
          lam h *
            (F ((h : R) • y) * (F ((h : R) • q))⁻¹)
      rw [htranslate]
      dsimp only [lam]
      ring
    · change F ((h : R) • q) * (F ((h : R) • q))⁻¹ = 1
      exact mul_inv_cancel₀ hFqnonzero
  have hlamConstant :
      ∀ a b : C, lam a = lam b :=
    continuous_normalizedEigenvalue_family_constant
      T q lam hlamContinuous hlamEigen
  let oneC : C := ⟨1, C.one_mem⟩
  have hparamOne : param oneC = 1 := by
    apply injective_quadraticReducedHom N
    rw [quadraticReducedHom_apply, hparam oneC]
    change ⁅reducedProgressionGenerator N, (1 : R)⁆ =
      quadraticReducedHom N 1
    rw [map_one]
    simp
  have hlamOne : lam oneC = 1 := by
    rw [show lam oneC = (χ.toFun (param oneC))⁻¹ by rfl,
      hparamOne, χ.map_one]
    simp
  let gc : C := ⟨g, hg⟩
  have hparamG : param gc = z := by
    apply injective_quadraticReducedHom N
    rw [quadraticReducedHom_apply, hparam gc, hz]
    rfl
  have hvalue : (χ.toFun z)⁻¹ = 1 := by
    calc
      (χ.toFun z)⁻¹ = lam gc := by simp [lam, hparamG]
      _ = lam oneC := hlamConstant gc oneC
      _ = 1 := hlamOne
  exact inv_eq_one.mp hvalue

end Chapter02.HallPetrescoConnectedPhaseRigidity
