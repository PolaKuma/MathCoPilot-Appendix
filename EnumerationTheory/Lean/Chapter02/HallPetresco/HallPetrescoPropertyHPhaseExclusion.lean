import Chapter02.HallPetresco.HallPetrescoPropertyHPhaseTranslation

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoPropertyHPhaseExclusion

open Chapter02.HallPetrescoInvariantVerticalPhaseUniqueness
open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoPropertyHPhaseTranslation
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoVerticalPhase
open Chapter02.NilsystemPropertyHReduction

universe u v

/-- Property (H) excludes every nontrivial invariant vertical phase.

Each left translate is invariant and therefore, by uniqueness of a
normalized phase with a fixed vertical character, is a scalar multiple of
the original phase.  These scalars multiply under the group action, so
their unit level set contains every commutator.  Since the full quadratic
torus is the commutator subgroup, the vertical character is trivial. -/
theorem hasFullQuadraticFiberOrbitClosure_of_propertyH
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (hproperty :
      identityTranslationSubgroup H N.translation = ⊤) :
    HasFullQuadraticFiberOrbitClosure N P.lattice := by
  rw [hasFullQuadraticFiberOrbitClosure_iff_no_invariant_verticalPhase]
  intro q
  rintro ⟨χ, ⟨z, hz⟩, F, hFcontinuous, hFinv, hFvertical,
    hFnorm, hFq⟩
  have hFnonzero (y : ReducedQuotient N P.lattice) : F y ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hFnorm]
    norm_num
  have htranslateContinuous (g : ReducedGroup N) :
      Continuous (fun y : ReducedQuotient N P.lattice ↦ F (g • y)) :=
    hFcontinuous.comp (continuous_const.smul continuous_id)
  have htranslateVertical (g : ReducedGroup N) :
      ∀ w y,
        F (g • (quadraticReducedElement N w • y)) =
          χ.toFun w * F (g • y) := by
    intro w y
    have hcentral :
        g * quadraticReducedElement N w =
          quadraticReducedElement N w * g :=
      Subgroup.mem_center_iff.mp
        (quadraticReducedElement_mem_center N w) g
    calc
      F (g • (quadraticReducedElement N w • y)) =
          F ((g * quadraticReducedElement N w) • y) := by
            rw [mul_smul]
      _ = F ((quadraticReducedElement N w * g) • y) := by
            rw [hcentral]
      _ = F (quadraticReducedElement N w • (g • y)) := by
            rw [mul_smul]
      _ = χ.toFun w * F (g • y) := hFvertical w (g • y)
  have hscalar (g : ReducedGroup N) :
      ∀ y, F (g • y) = F (g • q) * F y := by
    have hratio :=
      invariant_verticalPhase_ratio_eq
        N P q χ (fun y ↦ F (g • y)) F
        (htranslateContinuous g) hFcontinuous
        (leftTranslate_verticalPhase_invariant_of_propertyH
          N P q χ F hFcontinuous hFinv hFvertical hFnorm
          hproperty g)
        hFinv (htranslateVertical g) hFvertical hFnorm
    intro y
    have hy := hratio y
    rw [hFq, inv_one, mul_one] at hy
    calc
      F (g • y) =
          (F (g • y) * (F y)⁻¹) * F y := by
            rw [mul_assoc, inv_mul_cancel₀ (hFnonzero y), mul_one]
      _ = F (g • q) * F y := by rw [hy]
  have hmul (g h : ReducedGroup N) :
      F ((g * h) • q) = F (g • q) * F (h • q) := by
    rw [mul_smul]
    exact hscalar g (h • q)
  have hinv (g : ReducedGroup N) :
      F (g⁻¹ • q) * F (g • q) = 1 := by
    have h := hscalar g⁻¹ (g • q)
    rw [inv_smul_smul, hFq] at h
    exact h.symm
  let K : Subgroup (ReducedGroup N) :=
    { carrier := {g | F (g • q) = 1}
      one_mem' := by
        change F ((1 : ReducedGroup N) • q) = 1
        simpa only [one_smul] using hFq
      mul_mem' := by
        intro g h hg hh
        change F ((g * h) • q) = 1
        change F (g • q) = 1 at hg
        change F (h • q) = 1 at hh
        rw [hmul, hg, hh, one_mul]
      inv_mem' := by
        intro g hg
        change F (g⁻¹ • q) = 1
        change F (g • q) = 1 at hg
        have hi := hinv g
        rw [hg, mul_one] at hi
        exact hi }
  have hcommutator :
      _root_.commutator (ReducedGroup N) ≤ K := by
    rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    change F (⁅g, h⁆ • q) = 1
    change F ((g * h * g⁻¹ * h⁻¹) • q) = 1
    rw [hmul, hmul, hmul]
    calc
      (F (g • q) * F (h • q) * F (g⁻¹ • q)) *
          F (h⁻¹ • q) =
          (F (g⁻¹ • q) * F (g • q)) *
            (F (h⁻¹ • q) * F (h • q)) := by ring
      _ = 1 := by rw [hinv, hinv, one_mul]
  have hquadratic :
      quadraticReducedElement N z ∈
        _root_.commutator (ReducedGroup N) := by
    rw [commutator_reducedGroup_eq_quadratic_range N]
    exact ⟨z, rfl⟩
  have hK := hcommutator hquadratic
  change F (quadraticReducedElement N z • q) = 1 at hK
  rw [hFvertical, hFq, mul_one] at hK
  exact hz hK

end Chapter02.HallPetrescoPropertyHPhaseExclusion
