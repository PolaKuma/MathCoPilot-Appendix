import Chapter02.HallPetresco.HallPetrescoReducedRecurrence
import Chapter02.HallPetresco.HallPetrescoVerticalCharacter
import Chapter02.HallPetresco.HallPetrescoNormalForm

open Classical Set
open scoped Pointwise

noncomputable section

namespace Chapter02.HallPetrescoVerticalPhase

open Chapter02.CompactGroupExtensionRecurrence
open Chapter02.HallPetrescoCentralExtensionMinimality
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedRecurrence
open Chapter02.HallPetrescoVerticalCharacter
open Chapter02.HallPetrescoNormalForm

universe u v

/-- A character annihilating the vertical return subgroup produces a
continuous phase on the whole reduced quotient.  The phase is invariant
under the progression and transforms by the given character under every
quadratic translation.

This is the precise topological obstruction attached to a proper vertical
return subgroup. -/
theorem exists_continuous_invariant_verticalPhase
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (hχreturn :
      ∀ z ∈ quadraticReturnSubgroup N P.lattice q,
        χ.toFun z = 1)
    (hχnontrivial : ∃ z, χ.toFun z ≠ 1) :
    ∃ F : ReducedQuotient N P.lattice → ℂ,
      Continuous F ∧
      (∀ y, F (reducedStep N P.lattice y) = F y) ∧
      (∀ z y,
        F (quadraticReducedElement N z • y) = χ.toFun z * F y) ∧
      (∀ y, ‖F y‖ = 1) ∧
      F q = 1 ∧
      ∃ y, F y ≠ F q := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  let K := Fin N.torusDim → Circle
  let Y := ReducedQuotient N P.lattice
  let T : Y → Y := reducedStep N P.lattice
  let C : Set Y :=
    closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T q)
  let C₀ := {y : Y // y ∈ C}
  let p : K × C₀ → Y :=
    fun a ↦ quadraticReducedElement N a.1 • a.2.1
  let raw : K × C₀ → ℂ := fun a ↦ χ.toFun a.1
  have hCclosed : IsClosed C := isClosed_closure
  letI : CompactSpace C₀ :=
    isCompact_iff_compactSpace.mp hCclosed.isCompact
  have hpcontinuous : Continuous p := by
    dsimp only [p]
    exact continuous_smul.comp
      ((continuous_quadraticReducedHom N).comp continuous_fst
        |>.prodMk (continuous_subtype_val.comp continuous_snd))
  have hpsurj : Function.Surjective p := by
    intro y
    have hyfactor :
        reducedToAbelianQuotient N P.lattice y ∈
          reducedToAbelianQuotient N P.lattice '' C := by
      rw [image_reduced_orbitClosure_eq_univ N P q]
      exact Set.mem_univ _
    obtain ⟨c, hcC, hcy⟩ := hyfactor
    obtain ⟨z, hyz⟩ :=
      (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
        N P.lattice c y).mp hcy
    exact ⟨⟨z, ⟨c, hcC⟩⟩, hyz.symm⟩
  have hpquot : Topology.IsQuotientMap p :=
    hpcontinuous.isClosedMap.isQuotientMap hpcontinuous hpsurj
  have hrawcontinuous : Continuous raw :=
    χ.continuous.comp continuous_fst
  have hraw_fiber :
      ∀ a b : K × C₀, p a = p b → raw a = raw b := by
    rintro ⟨z, ⟨c, hcC⟩⟩ ⟨w, ⟨d, hdC⟩⟩ hp
    have hfactor_cd :
        reducedToAbelianQuotient N P.lattice c =
          reducedToAbelianQuotient N P.lattice d := by
      have hzc :
          reducedToAbelianQuotient N P.lattice c =
            reducedToAbelianQuotient N P.lattice
              (quadraticReducedElement N z • c) :=
        (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
          N P.lattice c
          (quadraticReducedElement N z • c)).mpr ⟨z, rfl⟩
      have hwd :
          reducedToAbelianQuotient N P.lattice d =
            reducedToAbelianQuotient N P.lattice
              (quadraticReducedElement N w • d) :=
        (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
          N P.lattice d
          (quadraticReducedElement N w • d)).mpr ⟨w, rfl⟩
      exact hzc.trans ((congrArg
        (reducedToAbelianQuotient N P.lattice) hp).trans hwd.symm)
    obtain ⟨u, huQ, hdu⟩ :=
      exists_returnParameter_of_mem_orbitClosure_of_same_abelian
        N P q c d hcC hdC hfactor_cd
    let v : K := (w * u)⁻¹ * z
    have hvfix : quadraticReducedElement N v • c = c := by
      calc
        quadraticReducedElement N v • c =
            quadraticReducedElement N (w * u)⁻¹ •
              (quadraticReducedElement N z • c) := by
              change quadraticReducedHom N v • c =
                quadraticReducedHom N (w * u)⁻¹ •
                  (quadraticReducedHom N z • c)
              rw [← mul_smul]
              congr 1
              dsimp only [v]
              rw [map_mul, map_inv]
        _ = quadraticReducedElement N (w * u)⁻¹ •
              (quadraticReducedElement N w • d) := by
              exact congrArg
                (fun x : Y ↦ quadraticReducedElement N (w * u)⁻¹ • x) hp
        _ = c := by
              rw [hdu]
              change quadraticReducedHom N (w * u)⁻¹ •
                (quadraticReducedHom N w •
                  (quadraticReducedHom N u • c)) = c
              rw [← mul_smul, ← mul_smul]
              rw [← map_mul, ← map_mul]
              have hparam : (w * u)⁻¹ * w * u = 1 := by
                rw [mul_inv_rev]
                calc
                  u⁻¹ * w⁻¹ * w * u =
                      u⁻¹ * (w⁻¹ * w) * u := by
                        simp only [mul_assoc]
                  _ = 1 := by
                    rw [inv_mul_cancel, mul_one, inv_mul_cancel]
              rw [hparam, map_one, one_smul]
    have hvQ : v ∈ quadraticReturnSubgroup N P.lattice q := by
      have hv_at_c :
          v ∈ quadraticReturnSubgroup N P.lattice c := by
        change quadraticReducedElement N v • c ∈
          closure
            (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T c)
        rw [hvfix]
        exact subset_closure ⟨0, rfl⟩
      rw [quadraticReturnSubgroup_eq_of_mem_reduced_orbitClosure
        N P q c hcC] at hv_at_c
      exact hv_at_c
    have hz : w * u * v = z := by
      dsimp only [v]
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    change χ.toFun z = χ.toFun w
    rw [← hz, χ.map_mul, χ.map_mul,
      hχreturn u huQ, hχreturn v hvQ]
    simp
  let liftChoice : Y → K × C₀ :=
    fun y ↦ Classical.choose (hpsurj y)
  have hliftChoice (y : Y) : p (liftChoice y) = y :=
    Classical.choose_spec (hpsurj y)
  let F : Y → ℂ := fun y ↦ raw (liftChoice y)
  have hFp (a : K × C₀) : F (p a) = raw a := by
    exact hraw_fiber (liftChoice (p a)) a (hliftChoice (p a))
  have hFcontinuous : Continuous F := by
    apply hpquot.continuous_iff.mpr
    have heq : F ∘ p = raw := by
      funext a
      exact hFp a
    rw [heq]
    exact hrawcontinuous
  refine ⟨F, hFcontinuous, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨⟨z, c⟩, rfl⟩ := hpsurj y
    have hTc : T c.1 ∈ C := by
      apply image_closure_forwardOrbit_subset
        T (continuous_reducedStep N P.lattice) q
      exact ⟨c.1, c.2, rfl⟩
    have hstep :
        T (p (z, c)) = p (z, ⟨T c.1, hTc⟩) := by
      exact reducedStep_quadratic_smul N P.lattice z c.1
    change F (T (p (z, c))) = F (p (z, c))
    rw [hstep, hFp, hFp]
  · intro z y
    obtain ⟨⟨w, c⟩, rfl⟩ := hpsurj y
    have hsmul :
        quadraticReducedElement N z • p (w, c) =
          p (z * w, c) := by
      change quadraticReducedHom N z •
          (quadraticReducedHom N w • c.1) =
        quadraticReducedHom N (z * w) • c.1
      rw [← mul_smul, map_mul]
    rw [hsmul, hFp, hFp]
    exact χ.map_mul z w
  · intro y
    obtain ⟨a, rfl⟩ := hpsurj y
    rw [hFp]
    exact χ.unit_norm a.1
  · have hqC : q ∈ C := subset_closure ⟨0, rfl⟩
    have hFq : F q = 1 := by
      have hpone : p (1, ⟨q, hqC⟩) = q := by
        change quadraticReducedHom N 1 • q = q
        rw [map_one, one_smul]
      rw [← hpone, hFp]
      exact χ.map_one
    refine ⟨hFq, ?_⟩
    obtain ⟨z, hz⟩ := hχnontrivial
    refine ⟨quadraticReducedElement N z • q, ?_⟩
    have hFz : F (quadraticReducedElement N z • q) = χ.toFun z := by
      rw [show quadraticReducedElement N z • q =
          p (z, ⟨q, hqC⟩) by rfl, hFp]
    rw [hFz, hFq]
    exact hz

/-- Therefore failure of full vertical recurrence is equivalent to a
concrete nonconstant continuous progression-invariant phase carrying a
nontrivial vertical character. -/
theorem exists_nonconstant_invariant_verticalPhase_of_returnSubgroup_ne_top
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (hne : quadraticReturnSubgroup N P.lattice q ≠ ⊤) :
    ∃ χ : Chapter02.ContinuousMultiplicativeCircleCharacter
        (Fin N.torusDim → Circle),
      (∃ z, χ.toFun z ≠ 1) ∧
      ∃ F : ReducedQuotient N P.lattice → ℂ,
        Continuous F ∧
        (∀ y, F (reducedStep N P.lattice y) = F y) ∧
        (∀ z y,
          F (quadraticReducedElement N z • y) =
            χ.toFun z * F y) ∧
        ∃ y, F y ≠ F q := by
  obtain ⟨χ, hχreturn, hχnontrivial⟩ :=
    exists_verticalCharacter_of_quadraticReturnSubgroup_ne_top
      N P.lattice q hne
  obtain ⟨F, hFcontinuous, hFinv, hFvertical, _hFnorm,
      _hFq, hFnonconstant⟩ :=
    exists_continuous_invariant_verticalPhase
      N P q χ hχreturn hχnontrivial
  exact ⟨χ, hχnontrivial, F, hFcontinuous, hFinv, hFvertical,
    hFnonconstant⟩

/-- A continuous progression-invariant function is constant on the
forward orbit closure of the distinguished point.  This elementary
observation is the bridge from the phase construction to the setwise
orbit-closure stabilizer. -/
theorem invariant_eq_on_forwardOrbitClosure
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (F : ReducedQuotient N Γ → ℂ)
    (hFcontinuous : Continuous F)
    (hFinv : ∀ y, F (reducedStep N Γ y) = F y)
    {y : ReducedQuotient N Γ}
    (hy : y ∈ closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
        (reducedStep N Γ) q)) :
    F y = F q := by
  let T : ReducedQuotient N Γ → ReducedQuotient N Γ :=
    reducedStep N Γ
  let E : Set (ReducedQuotient N Γ) := {x | F x = F q}
  have hEclosed : IsClosed E :=
    isClosed_eq hFcontinuous continuous_const
  have horbit :
      Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T q ⊆ E := by
    rintro _ ⟨n, rfl⟩
    change F ((T^[n]) q) = F q
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (hFinv ((T^[n]) q)).trans ih
  exact closure_minimal horbit hEclosed hy

/-- Full quadratic-fiber recurrence is exactly the absence, at every base
point, of a normalized unit-modulus progression-invariant phase carrying a
nontrivial vertical character.

Unlike the sufficient commutator-density criterion, this statement is an
exact reformulation of the remaining vertical obstruction. -/
theorem hasFullQuadraticFiberOrbitClosure_iff_no_invariant_verticalPhase
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N) :
    HasFullQuadraticFiberOrbitClosure N P.lattice ↔
      ∀ q : ReducedQuotient N P.lattice,
        ¬ ∃ χ : Chapter02.ContinuousMultiplicativeCircleCharacter
              (Fin N.torusDim → Circle),
            (∃ z, χ.toFun z ≠ 1) ∧
              ∃ F : ReducedQuotient N P.lattice → ℂ,
                Continuous F ∧
                (∀ y, F (reducedStep N P.lattice y) = F y) ∧
                (∀ z y,
                  F (quadraticReducedElement N z • y) =
                    χ.toFun z * F y) ∧
                (∀ y, ‖F y‖ = 1) ∧
                F q = 1 := by
  constructor
  · intro hfull q
    rintro ⟨χ, ⟨z, hz⟩, F, hFcontinuous, hFinv, hFvertical,
      _hFnorm, hFq⟩
    have hzclosure :
        quadraticReducedElement N z • q ∈
          closure
            (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
              (reducedStep N P.lattice) q) :=
      hfull q z
    have hconstant :
        F (quadraticReducedElement N z • q) = F q :=
      invariant_eq_on_forwardOrbitClosure
        N P.lattice q F hFcontinuous hFinv hzclosure
    apply hz
    calc
      χ.toFun z = χ.toFun z * F q := by rw [hFq, mul_one]
      _ = F (quadraticReducedElement N z • q) :=
        (hFvertical z q).symm
      _ = F q := hconstant
      _ = 1 := hFq
  · intro hnone
    rw [hasFullQuadraticFiberOrbitClosure_iff_returnSubgroup_eq_top]
    intro q
    by_contra hne
    obtain ⟨χ, hχreturn, hχnontrivial⟩ :=
      exists_verticalCharacter_of_quadraticReturnSubgroup_ne_top
        N P.lattice q hne
    obtain ⟨F, hFcontinuous, hFinv, hFvertical, hFnorm,
        hFq, _hFnonconstant⟩ :=
      exists_continuous_invariant_verticalPhase
        N P q χ hχreturn hχnontrivial
    exact hnone q
      ⟨χ, hχnontrivial, F, hFcontinuous, hFinv, hFvertical,
        hFnorm, hFq⟩

/-- Left-translating a progression-invariant vertical phase by an arbitrary
reduced group element produces an eigenrelation.  Its eigenvalue is exactly
the vertical character evaluated on the commutator with the progression
generator. -/
theorem leftTranslate_verticalPhase_eigenrelation
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (F : ReducedQuotient N Γ → ℂ)
    (hFinv : ∀ y, F (reducedStep N Γ y) = F y)
    (hFvertical : ∀ z y,
      F (quadraticReducedElement N z • y) =
        χ.toFun z * F y)
    (g : ReducedGroup N) (z : Fin N.torusDim → Circle)
    (hz :
      ⁅reducedProgressionGenerator N, g⁆ =
        quadraticReducedElement N z)
    (y : ReducedQuotient N Γ) :
    χ.toFun z *
        F (g • reducedStep N Γ y) =
      F (g • y) := by
  have hmul :
      reducedProgressionGenerator N * g =
        quadraticReducedElement N z * g *
          reducedProgressionGenerator N := by
    rw [mul_eq_commutatorElement_mul_swap, hz]
  calc
    χ.toFun z * F (g • reducedStep N Γ y) =
        F (quadraticReducedElement N z •
          (g • reducedStep N Γ y)) := by
            rw [hFvertical]
    _ = F ((quadraticReducedElement N z * g *
          reducedProgressionGenerator N) • y) := by
            change F (quadraticReducedElement N z •
                (g • (reducedProgressionGenerator N • y))) =
              F ((quadraticReducedElement N z * g *
                reducedProgressionGenerator N) • y)
            rw [← mul_smul, ← mul_smul]
    _ = F ((reducedProgressionGenerator N * g) • y) := by
            rw [hmul]
    _ = F (reducedProgressionGenerator N • (g • y)) := by
            rw [mul_smul]
    _ = F (g • y) := hFinv (g • y)

/-- Every commutator of the progression generator with an element of the
setwise orbit-closure stabilizer is annihilated by the vertical character.

Indeed the phase is constant and nonzero on the orbit closure, while the
commutator identity turns its translate into an eigenfunction. -/
theorem verticalCharacter_commutator_eq_one_of_mem_orbitClosureStabilizer
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (Γ : Subgroup H) (q : ReducedQuotient N Γ)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (F : ReducedQuotient N Γ → ℂ)
    (hFcontinuous : Continuous F)
    (hFinv : ∀ y, F (reducedStep N Γ y) = F y)
    (hFvertical : ∀ z y,
      F (quadraticReducedElement N z • y) =
        χ.toFun z * F y)
    (hFq : F q ≠ 0)
    (g : ReducedGroup N)
    (hg : g ∈ orbitClosureStabilizer N Γ q)
    (z : Fin N.torusDim → Circle)
    (hz :
      ⁅reducedProgressionGenerator N, g⁆ =
        quadraticReducedElement N z) :
    χ.toFun z = 1 := by
  let T : ReducedQuotient N Γ → ReducedQuotient N Γ :=
    reducedStep N Γ
  let C : Set (ReducedQuotient N Γ) :=
    closure
      (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit T q)
  have hgC : g • C = C := by
    exact (MulAction.mem_stabilizer_iff.mp hg)
  have hqC : q ∈ C :=
    subset_closure ⟨0, rfl⟩
  have hTqC : T q ∈ C :=
    subset_closure ⟨1, rfl⟩
  have hgqC : g • q ∈ C := by
    rw [← hgC]
    exact ⟨q, hqC, rfl⟩
  have hgTqC : g • T q ∈ C := by
    rw [← hgC]
    exact ⟨T q, hTqC, rfl⟩
  have hphase_gq : F (g • q) = F q :=
    invariant_eq_on_forwardOrbitClosure
      N Γ q F hFcontinuous hFinv hgqC
  have hphase_gTq : F (g • T q) = F q :=
    invariant_eq_on_forwardOrbitClosure
      N Γ q F hFcontinuous hFinv hgTqC
  have heigen :
      χ.toFun z * F (g • T q) = F (g • q) :=
    leftTranslate_verticalPhase_eigenrelation
      N Γ χ F hFinv hFvertical g z hz q
  rw [hphase_gq, hphase_gTq] at heigen
  apply mul_right_cancel₀ hFq
  exact heigen.trans (one_mul (F q)).symm

end Chapter02.HallPetrescoVerticalPhase
