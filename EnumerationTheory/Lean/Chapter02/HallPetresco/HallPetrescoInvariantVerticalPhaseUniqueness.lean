import Chapter02.HallPetresco.HallPetrescoVerticalPhase

open Classical Set

noncomputable section

namespace Chapter02.HallPetrescoInvariantVerticalPhaseUniqueness

open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedRecurrence
open Chapter02.HallPetrescoVerticalPhase

universe u v

/-- Two normalized continuous progression-invariant phases carrying the
same vertical character differ by one global scalar.

The ratio is unchanged both by the progression and by every quadratic
translation.  The progression orbit closure projects onto the whole common
abelian factor, and quadratic translations act transitively on each fiber,
so the ratio is constant on the whole reduced quotient. -/
theorem invariant_verticalPhase_ratio_eq
    {H : Type u} {X : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    (q : ReducedQuotient N P.lattice)
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter
      (Fin N.torusDim → Circle))
    (F G : ReducedQuotient N P.lattice → ℂ)
    (hFcontinuous : Continuous F)
    (hGcontinuous : Continuous G)
    (hFinv : ∀ y, F (reducedStep N P.lattice y) = F y)
    (hGinv : ∀ y, G (reducedStep N P.lattice y) = G y)
    (hFvertical : ∀ z y,
      F (quadraticReducedElement N z • y) = χ.toFun z * F y)
    (hGvertical : ∀ z y,
      G (quadraticReducedElement N z • y) = χ.toFun z * G y)
    (hGnorm : ∀ y, ‖G y‖ = 1) :
    ∀ y, F y * (G y)⁻¹ = F q * (G q)⁻¹ := by
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  let R : ReducedQuotient N P.lattice → ℂ :=
    fun y ↦ F y * (G y)⁻¹
  have hGnonzero (y : ReducedQuotient N P.lattice) : G y ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hGnorm]
    norm_num
  have hχnonzero (z : Fin N.torusDim → Circle) : χ.toFun z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [χ.unit_norm]
    norm_num
  have hRcontinuous : Continuous R := by
    exact hFcontinuous.mul
      (hGcontinuous.inv₀ hGnonzero)
  have hRinv :
      ∀ y, R (reducedStep N P.lattice y) = R y := by
    intro y
    dsimp only [R]
    rw [hFinv, hGinv]
  have hRvertical :
      ∀ z y, R (quadraticReducedElement N z • y) = R y := by
    intro z y
    dsimp only [R]
    rw [hFvertical, hGvertical]
    calc
      χ.toFun z * F y * (χ.toFun z * G y)⁻¹ =
          χ.toFun z * F y * ((G y)⁻¹ * (χ.toFun z)⁻¹) := by
            rw [mul_inv_rev]
      _ = (χ.toFun z * (χ.toFun z)⁻¹) * (F y * (G y)⁻¹) := by
            ring
      _ = F y * (G y)⁻¹ := by
            rw [mul_inv_cancel₀ (hχnonzero z), one_mul]
  intro y
  have hyfactor :
      reducedToAbelianQuotient N P.lattice y ∈
        reducedToAbelianQuotient N P.lattice ''
          closure
            (Chapter02.HallPetrescoMeasureOrbit.forwardOrbit
              (reducedStep N P.lattice) q) := by
    rw [image_reduced_orbitClosure_eq_univ N P q]
    exact Set.mem_univ _
  obtain ⟨c, hc, hcy⟩ := hyfactor
  obtain ⟨z, hyz⟩ :=
    (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
      N P.lattice c y).mp hcy
  calc
    R y = R (quadraticReducedElement N z • c) := by rw [← hyz]
    _ = R c := hRvertical z c
    _ = R q :=
      invariant_eq_on_forwardOrbitClosure
        N P.lattice q R hRcontinuous hRinv hc

end Chapter02.HallPetrescoInvariantVerticalPhaseUniqueness
