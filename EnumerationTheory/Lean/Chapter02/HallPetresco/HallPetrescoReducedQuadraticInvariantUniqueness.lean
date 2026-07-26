import Chapter02.HallPetresco.HallPetrescoReducedInvariantProjection

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HallPetrescoReducedQuadraticInvariantUniqueness

open Chapter02.HallPetrescoCompactQuotient
open Chapter02.HallPetrescoCompactReduced
open Chapter02.HallPetrescoLattice
open Chapter02.HallPetrescoReducedAbelianFactor
open Chapter02.HallPetrescoReducedHausdorff
open Chapter02.HallPetrescoReducedQuotient
open Chapter02.HallPetrescoReducedSecondCountable
open Chapter02.HallPetrescoAbelianSecondCountable

universe u v

/-- The remaining vertical Parry statement: every reduced-step invariant
probability is unchanged, on continuous integrals, by Haar averaging over
the concrete quadratic central torus. -/
def ReducedInvariantQuadraticHaarLaw
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
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant] : Prop :=
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
        (∫ q, ∫ z, φ (quadraticReducedElement N z • q) ∂m
          ∂(ν : Measure (ReducedQuotient N P.lattice))) =
          ∫ q, φ q ∂(ν : Measure (ReducedQuotient N P.lattice))

/-- Haar invariance in the quadratic fibers, together with the already
proved unique abelian projection, identifies all continuous integrals of
reduced-step invariant probabilities. -/
theorem invariant_integrals_eq_of_quadraticHaar
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
    [IsProbabilityMeasure m] [m.IsMulLeftInvariant]
    (hvertical : ReducedInvariantQuadraticHaarLaw N P m) :
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
    ∀ ρ σ : ProbabilityMeasure (ReducedQuotient N P.lattice),
      Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
          (reducedStep N P.lattice) ρ →
        Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
          (reducedStep N P.lattice) σ →
        ∀ φ : C(ReducedQuotient N P.lattice, ℝ),
          (∫ q, φ q ∂(ρ : Measure (ReducedQuotient N P.lattice))) =
            ∫ q, φ q ∂(σ : Measure (ReducedQuotient N P.lattice)) := by
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
  letI : CompactSpace (AbelianQuotient P.lattice) :=
    abelianQuotientCompactSpace N P
  letI : T2Space (AbelianQuotient P.lattice) :=
    abelianQuotientT2Space N P
  letI : SecondCountableTopology (AbelianQuotient P.lattice) :=
    abelianQuotientSecondCountableTopology N P
  change
    ∀ ν : ProbabilityMeasure (ReducedQuotient N P.lattice),
      Chapter02.CompactUniqueErgodicCesaro.IsIntegralInvariant
          (reducedStep N P.lattice) ν →
        ∀ φ : C(ReducedQuotient N P.lattice, ℝ),
          (∫ q, ∫ z, φ (quadraticReducedElement N z • q) ∂m
            ∂(ν : Measure (ReducedQuotient N P.lattice))) =
            ∫ q, φ q ∂(ν : Measure (ReducedQuotient N P.lattice))
      at hvertical
  intro ρ σ hρ hσ φ
  let A : ReducedQuotient N P.lattice → ℝ :=
    fun q ↦ ∫ z, φ (quadraticReducedElement N z • q) ∂m
  have hA : Continuous A := by
    have h :=
      continuous_parametric_integral_of_continuous
        (μ := m)
        (f := fun q : ReducedQuotient N P.lattice ↦
          fun z : Fin N.torusDim → Circle ↦
            φ (quadraticReducedElement N z • q))
        (φ.continuous.comp
          ((continuous_quadraticReducedHom N).comp continuous_snd
            |>.smul continuous_fst))
        isCompact_univ
    simpa only [A, Measure.restrict_univ] using h
  have hAfiber (q r : ReducedQuotient N P.lattice)
      (hqr : reducedToAbelianQuotient N P.lattice q =
        reducedToAbelianQuotient N P.lattice r) :
      A q = A r := by
    obtain ⟨z, rfl⟩ :=
      (reducedToAbelianQuotient_eq_iff_exists_quadratic_smul
        N P.lattice q r).mp hqr
    dsimp only [A]
    rw [← integral_mul_left_eq_self
      (fun w ↦ φ (quadraticReducedElement N w • q)) z]
    apply integral_congr_ae
    filter_upwards with w
    change φ (quadraticReducedHom N (z * w) • q) =
      φ (quadraticReducedHom N w •
        (quadraticReducedHom N z • q))
    rw [← mul_smul, ← map_mul]
    congr 2
    exact congrArg (quadraticReducedHom N) (mul_comm z w)
  let π := reducedToAbelianQuotient N P.lattice
  have hπsurj : Function.Surjective π :=
    surjective_reducedToAbelianQuotient N P.lattice
  have hπquot : Topology.IsQuotientMap π :=
    (continuous_reducedToAbelianQuotient N P.lattice).isClosedMap.isQuotientMap
      (continuous_reducedToAbelianQuotient N P.lattice) hπsurj
  let lift : AbelianQuotient P.lattice → ReducedQuotient N P.lattice :=
    fun b ↦ Classical.choose (hπsurj b)
  let g : AbelianQuotient P.lattice → ℝ := fun b ↦ A (lift b)
  have hgπ (q : ReducedQuotient N P.lattice) : g (π q) = A q := by
    exact hAfiber _ _ (Classical.choose_spec (hπsurj (π q)))
  have hg : Continuous g := by
    apply hπquot.continuous_iff.mpr
    have : g ∘ π = A := by funext q; exact hgπ q
    rw [this]
    exact hA
  let gc : C(AbelianQuotient P.lattice, ℝ) := ⟨g, hg⟩
  have hbase :=
    Chapter02.HallPetrescoReducedInvariantProjection.reducedInvariantBaseIdentification
      N P ρ σ hρ hσ gc
  change (∫ q, g (π q) ∂(ρ : Measure _)) =
    ∫ q, g (π q) ∂(σ : Measure _) at hbase
  simp_rw [hgπ] at hbase
  rw [← hvertical ρ hρ φ, ← hvertical σ hσ φ]
  exact hbase

end Chapter02.HallPetrescoReducedQuadraticInvariantUniqueness
