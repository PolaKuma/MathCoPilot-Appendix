import Chapter02.Spectral.CompactHaarFourierUniqueness
import Chapter02.HallPetresco.HallPetrescoReducedQuadraticInvariantUniqueness

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoReducedVerticalFourierCriterion

open Chapter02.CompactHaarCharacters
open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedSecondCountable

universe u v

/-- Scalar Fourier form of the remaining vertical Parry theorem. -/
def ReducedInvariantNontrivialFourierVanishing
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsHaarMeasure] : Prop :=
  letI : CompactSpace (Quotient N P.lattice) := quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  letI : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MeasurableSpace (ReducedQuotient N P.lattice) :=
    borel (ReducedQuotient N P.lattice)
  letI : BorelSpace (ReducedQuotient N P.lattice) := ⟨rfl⟩
  ∀ ν : ProbabilityMeasure (ReducedQuotient N P.lattice),
    Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
        (reducedStep N P.lattice) ν →
      ∀ φ : C(ReducedQuotient N P.lattice, ℝ),
      ∀ χ : Character (Fin N.torusDim → Circle),
        (¬ ∀ z, χ.toFun z = 1) →
        (∫ z, star (χ.toFun z) *
            (∫ q, (φ (quadraticReducedElement N z • q) : ℂ)
              ∂(ν : Measure (ReducedQuotient N P.lattice))) ∂m) = 0

/-- Vanishing of every nonzero vertical Fourier mode forces Haar
invariance in the quadratic fibers. -/
theorem quadraticHaarLaw_of_nontrivialFourierVanishing
    {H : Type u} {X : Type v}
    [Group H] [MetricSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H]
    [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] {μ : Measure X}
    (N : Chapter02.ToralTwoStepNilsystem.Model H X μ)
    (P : Chapter02.ToralTwoStepNilsystem.QuotientPresentation N)
    [MeasurableSpace (Quotient N P.lattice)]
    [BorelSpace (Quotient N P.lattice)]
    (m : Measure (Fin N.torusDim → Circle))
    [IsProbabilityMeasure m] [m.IsHaarMeasure]
    (hfourier : ReducedInvariantNontrivialFourierVanishing N P m) :
    Chapter02.HallPetrescoReducedQuadraticInvariantUniqueness.ReducedInvariantQuadraticHaarLaw
      N P m := by
  letI : CompactSpace (Quotient N P.lattice) := quotientCompactSpace N P
  letI : CompactSpace (ReducedQuotient N P.lattice) :=
    reducedQuotientCompactSpaceOfPresentation N P
  letI : T2Space (ReducedQuotient N P.lattice) :=
    reducedQuotientT2Space N P
  letI : SecondCountableTopology (ReducedQuotient N P.lattice) :=
    reducedQuotientSecondCountableTopology N P
  letI : TopologicalSpace.MetrizableSpace
      (ReducedQuotient N P.lattice) := inferInstance
  letI : MetricSpace (ReducedQuotient N P.lattice) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : MeasurableSpace (ReducedQuotient N P.lattice) :=
    borel (ReducedQuotient N P.lattice)
  letI : BorelSpace (ReducedQuotient N P.lattice) := ⟨rfl⟩
  change
    ∀ ν : ProbabilityMeasure (ReducedQuotient N P.lattice),
      Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
          (reducedStep N P.lattice) ν →
        ∀ φ : C(ReducedQuotient N P.lattice, ℝ),
        ∀ χ : Character (Fin N.torusDim → Circle),
          (¬ ∀ z, χ.toFun z = 1) →
          (∫ z, star (χ.toFun z) *
              (∫ q, (φ (quadraticReducedElement N z • q) : ℂ)
                ∂(ν : Measure (ReducedQuotient N P.lattice))) ∂m) = 0
      at hfourier
  intro ν hν φ
  let D : C(Fin N.torusDim → Circle, ℂ) :=
    ⟨fun z ↦ ∫ q, (φ (quadraticReducedElement N z • q) : ℂ)
        ∂(ν : Measure (ReducedQuotient N P.lattice)),
      by
        have h :=
          continuous_parametric_integral_of_continuous
            (μ := (ν : Measure (ReducedQuotient N P.lattice)))
            (f := fun z : Fin N.torusDim → Circle ↦
              fun q : ReducedQuotient N P.lattice ↦
                (φ (quadraticReducedElement N z • q) : ℂ))
            (Complex.continuous_ofReal.comp
              (φ.continuous.comp
                ((continuous_quadraticReducedHom N).comp continuous_fst
                  |>.smul continuous_snd)))
            isCompact_univ
        simpa only [Measure.restrict_univ] using h⟩
  have hD :=
    Chapter02.CompactHaarFourierUniqueness.continuous_eq_haarMean_of_nontrivial_fourier_zero
      m D (fun χ hχ ↦ hfourier ν hν φ χ hχ)
  have htrans (z : Fin N.torusDim → Circle) :
      (∫ q, φ (quadraticReducedElement N z • q)
          ∂(ν : Measure (ReducedQuotient N P.lattice))) =
        ∫ q, φ q ∂(ν : Measure (ReducedQuotient N P.lattice)) := by
    have hz := hD z
    have h1 := hD 1
    have heq : D z = D 1 := hz.trans h1.symm
    have hintz :
        Integrable
          (fun q : ReducedQuotient N P.lattice ↦
            φ (quadraticReducedElement N z • q))
          (ν : Measure (ReducedQuotient N P.lattice)) := by
      have hc : Continuous
          (fun q : ReducedQuotient N P.lattice ↦
            φ (quadraticReducedElement N z • q)) :=
        φ.continuous.comp (continuous_const.smul continuous_id)
      simpa using ContinuousOn.integrableOn_compact
        (μ := (ν : Measure (ReducedQuotient N P.lattice)))
        isCompact_univ hc.continuousOn
    have hint1 :
        Integrable
          (fun q : ReducedQuotient N P.lattice ↦ φ q)
          (ν : Measure (ReducedQuotient N P.lattice)) := by
      have hc : Continuous
          (fun q : ReducedQuotient N P.lattice ↦ φ q) :=
        φ.continuous
      simpa using ContinuousOn.integrableOn_compact
        (μ := (ν : Measure (ReducedQuotient N P.lattice)))
        isCompact_univ hc.continuousOn
    have hqone : quadraticReducedElement N 1 = 1 := by
      change quadraticReducedHom N 1 = 1
      exact map_one _
    simp only [D, ContinuousMap.coe_mk] at heq
    rw [hqone] at heq
    simp only [one_smul] at heq
    have hzC :
        (∫ q, (φ (quadraticReducedElement N z • q) : ℂ)
            ∂(ν : Measure (ReducedQuotient N P.lattice))) =
          Complex.ofReal
            (∫ q, φ (quadraticReducedElement N z • q)
              ∂(ν : Measure (ReducedQuotient N P.lattice))) := by
      exact Complex.ofRealCLM.integral_comp_comm hintz
    have h1C :
        (∫ q, (φ q : ℂ)
            ∂(ν : Measure (ReducedQuotient N P.lattice))) =
          Complex.ofReal
            (∫ q, φ q
              ∂(ν : Measure (ReducedQuotient N P.lattice))) := by
      exact Complex.ofRealCLM.integral_comp_comm hint1
    apply Complex.ofReal_injective
    rw [← hzC, ← h1C]
    exact heq
  have hprod :
      Integrable
        (fun p : (ReducedQuotient N P.lattice) ×
            (Fin N.torusDim → Circle) ↦
          φ (quadraticReducedElement N p.2 • p.1))
        ((ν : Measure (ReducedQuotient N P.lattice)).prod m) := by
    have hc : Continuous
        (fun p : (ReducedQuotient N P.lattice) ×
            (Fin N.torusDim → Circle) ↦
          φ (quadraticReducedElement N p.2 • p.1)) :=
      φ.continuous.comp
        ((continuous_quadraticReducedHom N).comp continuous_snd
          |>.smul continuous_fst)
    simpa using ContinuousOn.integrableOn_compact
      (μ := (ν : Measure (ReducedQuotient N P.lattice)).prod m)
      isCompact_univ hc.continuousOn
  calc
    (∫ q, ∫ z, φ (quadraticReducedElement N z • q) ∂m
        ∂(ν : Measure (ReducedQuotient N P.lattice))) =
        ∫ z, ∫ q, φ (quadraticReducedElement N z • q)
          ∂(ν : Measure (ReducedQuotient N P.lattice)) ∂m :=
      integral_integral_swap hprod
    _ = ∫ z, ∫ q, φ q
          ∂(ν : Measure (ReducedQuotient N P.lattice)) ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall htrans
    _ = ∫ q, φ q ∂(ν : Measure (ReducedQuotient N P.lattice)) := by
      simp

end Chapter02.HallPetrescoReducedVerticalFourierCriterion
