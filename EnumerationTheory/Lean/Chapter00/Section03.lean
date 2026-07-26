import Chapter00.Section02
import Chapter00.Probability.Section03Equivariance

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter00
namespace Section03

universe u v

/--
Source: Theorem 0.3.2, Chapter 0, Section 3.
Lebesgue decomposition theorem for two probability measures.
-/
theorem lebesgueDecompositionTheorem {X : Type u} [MeasurableSpace X]
    (μ m : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure m] :
    ∃! parts : MeasureTheory.Measure X × MeasureTheory.Measure X,
      parts.1 + parts.2 = μ ∧
        MeasureTheory.Measure.AbsolutelyContinuous parts.1 m ∧
        MeasureTheory.Measure.MutuallySingular parts.2 m := by
  let ac := m.withDensity (μ.rnDeriv m)
  let sing := μ.singularPart m
  refine ⟨(ac, sing), ?_, ?_⟩
  · refine ⟨?_, MeasureTheory.withDensity_absolutelyContinuous m _,
      MeasureTheory.Measure.mutuallySingular_singularPart μ m⟩
    simpa [ac, sing, add_comm] using (μ.haveLebesgueDecomposition_add m).symm
  · rintro ⟨ac', sing'⟩ ⟨hsum, hac', hsing'⟩
    have hac_le : ac' ≤ μ := by
      calc
        ac' ≤ ac' + sing' := MeasureTheory.Measure.le_add_right le_rfl
        _ = μ := hsum
    letI : MeasureTheory.IsFiniteMeasure ac' :=
      ⟨(hac_le Set.univ).trans_lt (MeasureTheory.measure_lt_top μ _)⟩
    have hsing_le : sing' ≤ μ := by
      calc
        sing' ≤ ac' + sing' := MeasureTheory.Measure.le_add_left le_rfl
        _ = μ := hsum
    letI : MeasureTheory.IsFiniteMeasure sing' :=
      ⟨(hsing_le Set.univ).trans_lt (MeasureTheory.measure_lt_top μ _)⟩
    have hzero : ac'.singularPart m = 0 :=
      (MeasureTheory.Measure.singularPart_eq_zero ac' m).2 hac'
    have hac_eq : ac' = m.withDensity (ac'.rnDeriv m) := by
      simpa [hzero] using ac'.haveLebesgueDecomposition_add m
    have hsing_eq : sing' = μ.singularPart m := by
      apply MeasureTheory.Measure.eq_singularPart
        (μ := μ) (ν := m) (f := ac'.rnDeriv m)
      · exact MeasureTheory.Measure.measurable_rnDeriv ac' m
      · exact hsing'
      · calc
          μ = ac' + sing' := hsum.symm
          _ = m.withDensity (ac'.rnDeriv m) + sing' := by
            conv_lhs => rw [hac_eq]
          _ = sing' + m.withDensity (ac'.rnDeriv m) := add_comm _ _
    apply Prod.ext
    · ext B hB
      have hval := congrArg (fun z : MeasureTheory.Measure X => z B) hsum
      have hcanon_measure : ac + sing = μ := by
        simpa [ac, sing, add_comm] using (μ.haveLebesgueDecomposition_add m).symm
      have hcanon := congrArg (fun z : MeasureTheory.Measure X => z B) hcanon_measure
      simp only [MeasureTheory.Measure.add_apply] at hval hcanon
      change ac' B = ac B
      apply (ENNReal.add_left_inj (MeasureTheory.measure_ne_top sing' B)).mp
      calc
        ac' B + sing' B = μ B := hval
        _ = ac B + sing B := hcanon.symm
        _ = ac B + sing' B := by rw [hsing_eq]
    · simpa [sing] using hsing_eq

/--
Source: Theorem 0.3.3, Chapter 0, Section 3.
Radon-Nikodym theorem and the chain-rule behavior of derivatives.
-/
theorem radonNikodymTheorem {X : Type u} [MeasurableSpace X]
    (μ ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν]
    (hνμ : MeasureTheory.Measure.AbsolutelyContinuous ν μ) :
    ∃ f : X -> ℝ,
      MeasureTheory.AEStronglyMeasurable f μ ∧ (∀ᵐ x ∂μ, 0 ≤ f x) ∧
      MeasureTheory.Integrable f μ ∧
      (∀ A : Set X, MeasurableSet A ->
        ν A = ∫⁻ x in A, ENNReal.ofReal (f x) ∂μ) ∧
      ∀ g : X -> ℝ,
        MeasureTheory.AEStronglyMeasurable g μ -> (∀ᵐ x ∂μ, 0 ≤ g x) ->
        MeasureTheory.Integrable g μ ->
        (∀ A : Set X, MeasurableSet A ->
          ν A = ∫⁻ x in A, ENNReal.ofReal (g x) ∂μ) ->
        f =ᵐ[μ] g := by
  let f : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MeasureTheory.Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg
  · exact MeasureTheory.Measure.integrable_toReal_rnDeriv
  · intro A hA
    have hmeasure : ν = μ.withDensity (ν.rnDeriv μ) :=
      (MeasureTheory.Measure.withDensity_rnDeriv_eq ν μ hνμ).symm
    rw [hmeasure, MeasureTheory.withDensity_apply _ hA]
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.rnDeriv_ne_top ν μ)] with x hx
    exact (ENNReal.ofReal_toReal hx).symm
  · intro g hg hgnonneg _hgint hgrep
    have hgmeas : AEMeasurable (fun x => ENNReal.ofReal (g x)) μ :=
      hg.aemeasurable.ennreal_ofReal
    have hmeasure_g : ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
      ext A hA
      rw [MeasureTheory.withDensity_apply _ hA]
      exact hgrep A hA
    have hmeasure_f : ν = μ.withDensity (ν.rnDeriv μ) :=
      (MeasureTheory.Measure.withDensity_rnDeriv_eq ν μ hνμ).symm
    have hden : ν.rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (g x) :=
      (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
        (MeasureTheory.Measure.measurable_rnDeriv ν μ).aemeasurable hgmeas).1
        (hmeasure_f.symm.trans hmeasure_g)
    filter_upwards [hden, hgnonneg] with x hx hxg
    change (ν.rnDeriv μ x).toReal = g x
    rw [hx, ENNReal.toReal_ofReal hxg]

/--
Source: Theorem 0.3.3, chain rule following the Radon--Nikodym theorem.
-/
theorem radonNikodymChainRule {X : Type u} [MeasurableSpace X]
    (μ ν η : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.IsProbabilityMeasure ν] [MeasureTheory.IsProbabilityMeasure η]
    (hην : MeasureTheory.Measure.AbsolutelyContinuous η ν)
    (hνμ : MeasureTheory.Measure.AbsolutelyContinuous ν μ) :
    η.rnDeriv μ =ᵐ[μ] fun x => η.rnDeriv ν x * ν.rnDeriv μ x := by
  simpa only [Pi.mul_apply] using
    (MeasureTheory.Measure.rnDeriv_mul_rnDeriv (κ := μ) hην).symm

/--
Source: Theorem 0.3.6, Chapter 0, Section 3.
Existence and basic properties of conditional expectation onto a sub
sigma-algebra.
-/
theorem conditionalExpectationExists
    (P : BasicProbabilitySpaceData) (A : SetFamily P.X) :
    IsSigmaAlgebraFamily A -> A ⊆ P.𝓧 ->
      ∃ E : ConditionalExpectationData P A,
        IsConditionalExpectation P A E ∧
        (∀ f g : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          MeasureTheory.Integrable g P.μ -> ∀ a b : ℂ,
          E.op (fun x => a * f x + b * g x) =ᵐ[P.μ]
            fun x => a * E.op f x + b * E.op g x) ∧
        (∀ f : P.X -> ℝ, MeasureTheory.Integrable f P.μ ->
          (∀ᵐ x ∂P.μ, 0 ≤ f x) ->
            ∀ᵐ x ∂P.μ, 0 ≤ (E.op (fun y => (f y : ℂ)) x).re) ∧
        (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          (∫ x, ‖E.op f x‖ ∂P.μ) ≤ ∫ x, ‖f x‖ ∂P.μ) ∧
        (∀ f g : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          IsMeasurableForFamily A g ->
          MeasureTheory.Integrable (fun x => g x * f x) P.μ ->
          MeasureTheory.Integrable (fun x => g x * E.op f x) P.μ ->
          E.op (fun x => g x * f x) =ᵐ[P.μ] fun x => g x * E.op f x) ∧
        (∀ C : SetFamily P.X, C ⊆ A -> IsSigmaAlgebraFamily C ->
          ∀ EC : ConditionalExpectationData P C, IsConditionalExpectation P C EC ->
          ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
            EC.op (E.op f) =ᵐ[P.μ] EC.op f) ∧
        (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          IsMeasurableForFamily A f -> E.op f =ᵐ[P.μ] f) ∧
        (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
          ∀ᵐ x ∂P.μ, ‖E.op f x‖ ≤ (E.op (fun y => ‖f y‖) x).re) ∧
        ∀ E' : ConditionalExpectationData P A,
          IsConditionalExpectation P A E' ->
          ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
            E.op f =ᵐ[P.μ] E'.op f := by
  exact conditionalExpectationExistsAux P A

/--
Source: Theorem 0.3.8, Chapter 0, Section 3.
The conditional expectation operator extends from `L^2` to `L^1` and satisfies
linearity, positivity, module, and tower properties.
-/
theorem conditionalExpectationExtendsToL1
    (P Q : BasicProbabilitySpaceData) (φ : P.X -> Q.X)
    (hφ : Measurable φ) (hpush : MeasureTheory.Measure.map φ P.μ = Q.μ) :
    ∃ E : (P.X -> ℂ) -> Q.X -> ℂ,
      (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
        MeasureTheory.Integrable (E f) Q.μ) ∧
      (∀ f g : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
        MeasureTheory.Integrable g P.μ -> ∀ a b : ℂ,
        E (fun x => a * f x + b * g x) =ᵐ[Q.μ]
          fun y => a * E f y + b * E g y) ∧
      (∀ f : P.X -> ℝ, MeasureTheory.Integrable f P.μ ->
        (∀ᵐ x ∂P.μ, 0 ≤ f x) -> ∀ᵐ y ∂Q.μ, 0 ≤ (E (fun x => f x) y).re) ∧
      (∀ g : Q.X -> ℂ, MeasureTheory.Integrable g Q.μ ->
        E (g ∘ φ) =ᵐ[Q.μ] g) ∧
      (∀ f : P.X -> ℂ, ∀ g : Q.X -> ℂ,
        MeasureTheory.Integrable f P.μ -> MeasureTheory.Integrable g Q.μ ->
        MeasureTheory.Integrable (fun x => g (φ x) * f x) P.μ ->
        MeasureTheory.Integrable (fun y => g y * E f y) Q.μ ->
        E (fun x => g (φ x) * f x) =ᵐ[Q.μ] fun y => g y * E f y) ∧
      ∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
        ∫ x, f x ∂P.μ = ∫ y, E f y ∂Q.μ := by
  exact conditionalExpectationExtendsToL1Aux P Q φ hφ hpush

/--
Source: Theorem 0.3.9, Chapter 0, Section 3.
Existence of conditional measures over a countably generated sub
sigma-algebra on a standard Borel probability space.
-/
theorem conditionalMeasureFamilyExists
    (P : BasicProbabilitySpaceData) [StandardBorelSpace P.X]
    (A : SetFamily P.X) :
    IsSigmaAlgebraFamily A -> A ⊆ P.𝓧 ->
      ∃ E : ConditionalExpectationData P A,
        ∃ D : ConditionalMeasureFamily P A,
          IsConditionalExpectation P A E ∧ IsConditionalMeasureFamily P A E D ∧
          (CountablyGeneratedFamily A ->
            (∀ x ∈ D.fullSet,
              D.measureAt x (⋂₀ {B : Set P.X | B ∈ A ∧ x ∈ B}) = 1) ∧
            ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
              (⋂₀ {B : Set P.X | B ∈ A ∧ x ∈ B}) =
                (⋂₀ {B : Set P.X | B ∈ A ∧ y ∈ B}) ->
              D.measureAt x = D.measureAt y) ∧
          ∀ C : SetFamily P.X, IsSigmaAlgebraFamily C -> C ⊆ P.𝓧 ->
            ∀ EC : ConditionalExpectationData P C,
            ∀ DC : ConditionalMeasureFamily P C,
              IsConditionalExpectation P C EC ->
              IsConditionalMeasureFamily P C EC DC ->
              Section01.completedSigmaAlgebraFamily A P.μ =
                Section01.completedSigmaAlgebraFamily C P.μ ->
              ∀ᵐ x ∂P.μ, D.measureAt x = DC.measureAt x := by
  exact conditionalMeasureFamilyAux P A

/--
Source: Theorem 0.3.11, Chapter 0, Section 3.
Measure disintegration over a Borel map between standard Borel probability
spaces.
-/
theorem measureDisintegrationTheorem
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (φ : X -> Y) (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (hφ : Measurable φ) :
    HasMeasureDisintegration φ μ (MeasureTheory.Measure.map φ μ) := by
  exact measureDisintegrationAux φ μ hφ

/--
Source: Theorem 0.3.12, Chapter 0, Section 3.
A countably generated sub sigma-algebra is represented by a measurable map to a
compact metric factor, with conditional measures as fibers.
-/
theorem countablyGeneratedSubSigmaAlgebraCompactMetricRepresentation
    (P : BasicProbabilitySpaceData) [StandardBorelSpace P.X]
    (A : SetFamily P.X) :
    IsSigmaAlgebraFamily A -> A ⊆ P.𝓧 -> CountablyGeneratedFamily A ->
      ∃ X₀ : Set P.X, X₀ ∈ A ∧ P.μ X₀ = 1 ∧
      ∃ Y : Type u, ∃ _ : MetricSpace Y, ∃ _ : MeasurableSpace Y,
        CompactSpace Y ∧ BorelSpace Y ∧
        ∃ φ : X₀ -> Y, Measurable φ ∧
          (∀ B : Set P.X, B ∈ A ->
            ∃ C : Set Y, MeasurableSet C ∧
              B ∩ X₀ = {x : P.X | ∃ hx : x ∈ X₀, φ ⟨x, hx⟩ ∈ C}) ∧
          (∀ C : Set Y, MeasurableSet C ->
            ∃ B : Set P.X, B ∈ A ∧
              B ∩ X₀ = {x : P.X | ∃ hx : x ∈ X₀, φ ⟨x, hx⟩ ∈ C}) ∧
          ∀ x : X₀,
            (⋂₀ {B : Set P.X | B ∈ A ∧ (x : P.X) ∈ B}) ∩ X₀ =
              {z : P.X | ∃ hz : z ∈ X₀, φ ⟨z, hz⟩ = φ x} := by
  exact countablyGeneratedRepresentationAux P A

/--
Source: Theorem 0.3.13, Chapter 0, Section 3.
Disintegration is equivariant under a factor map of invertible standard Borel
measure-preserving systems.
-/
theorem equivarianceOfDisintegrationUnderDynamics
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (T : X -> X) (S : Y -> Y) (φ : X -> Y)
    (μ : MeasureTheory.Measure X) (ν : MeasureTheory.Measure Y)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] :
    Measurable T -> Measurable S -> Measurable φ ->
    Function.Bijective T -> Function.Bijective S ->
    MeasureTheory.Measure.map T μ = μ -> MeasureTheory.Measure.map S ν = ν ->
    MeasureTheory.Measure.map φ μ = ν -> φ ∘ T = S ∘ φ ->
    HasMeasureDisintegration φ μ ν ->
      ∃ μy : Y -> MeasureTheory.Measure X,
        (∀ᵐ y ∂ν, MeasureTheory.IsProbabilityMeasure (μy y) ∧
          μy y (φ ⁻¹' {y}) = 1) ∧
        (∀ B : Set X, MeasurableSet B -> Measurable fun y => μy y B) ∧
        (∀ B : Set X, MeasurableSet B -> μ B = ∫⁻ y, μy y B ∂ν) ∧
        ∀ᵐ y ∂ν, MeasureTheory.Measure.map T (μy y) = μy (S y) := by
  exact equivarianceOfDisintegrationAux T S φ μ ν

/--
Source: Definition 0.3.1, Chapter 0, Section 3.
Absolute continuity, mutual singularity, and equivalence of probability
measures on a measurable space.
-/
def absoluteContinuitySingularityEquivalenceDefinition {X : Type u}
    [MeasurableSpace X] (μ ν : MeasureTheory.Measure X) : Prop :=
  MeasureTheory.Measure.AbsolutelyContinuous ν μ

/-- Source: Definition 0.3.1(2). Mutual absolute continuity. -/
def equivalentMeasuresDefinition {X : Type u} [MeasurableSpace X]
    (μ ν : MeasureTheory.Measure X) : Prop :=
  MeasureTheory.Measure.AbsolutelyContinuous ν μ ∧
    MeasureTheory.Measure.AbsolutelyContinuous μ ν

/-- Source: Definition 0.3.1(3). Mutual singularity. -/
def mutuallySingularMeasuresDefinition {X : Type u} [MeasurableSpace X]
    (μ ν : MeasureTheory.Measure X) : Prop :=
  MeasureTheory.Measure.MutuallySingular μ ν

/--
Source: Definition 0.3.4, Chapter 0, Section 3.
The normalized restriction of a probability measure to a positive-measure set.
-/
def normalizedRestrictionMeasureDefinition {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (A : Set X) : MeasureTheory.Measure X :=
  (μ A)⁻¹ • μ.restrict A

/--
Source: Remark 0.3.5, Chapter 0, Section 3.
The normalized restriction is absolutely continuous with Radon-Nikodym
derivative given by the normalized characteristic function, and yields a
two-piece decomposition with its complement.
-/
theorem normalizedRestrictionMeasureRemark {X : Type u} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (A : Set X) (hA : MeasurableSet A) (hμA : 0 < μ A) :
    MeasureTheory.IsProbabilityMeasure (normalizedRestrictionMeasureDefinition μ A) ∧
      MeasureTheory.Measure.AbsolutelyContinuous
        (normalizedRestrictionMeasureDefinition μ A) μ ∧
      μ = μ A • normalizedRestrictionMeasureDefinition μ A +
        μ Aᶜ • normalizedRestrictionMeasureDefinition μ Aᶜ := by
  have hA0 : μ A ≠ 0 := ne_of_gt hμA
  have hAtop : μ A ≠ ⊤ := (MeasureTheory.measure_lt_top μ A).ne
  have hprob : MeasureTheory.IsProbabilityMeasure
      (normalizedRestrictionMeasureDefinition μ A) := by
    rw [MeasureTheory.isProbabilityMeasure_iff]
    simp only [normalizedRestrictionMeasureDefinition,
      MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hA0 hAtop
  have hac : MeasureTheory.Measure.AbsolutelyContinuous
      (normalizedRestrictionMeasureDefinition μ A) μ := by
    exact (MeasureTheory.Measure.absolutelyContinuous_of_le
      MeasureTheory.Measure.restrict_le_self).smul_left (μ A)⁻¹
  have hcancel : ∀ B : Set X,
      μ B • normalizedRestrictionMeasureDefinition μ B = μ.restrict B := by
    intro B
    by_cases hB0 : μ B = 0
    · have hr : μ.restrict B = 0 :=
        MeasureTheory.Measure.restrict_eq_zero.mpr hB0
      simp [normalizedRestrictionMeasureDefinition, hB0, hr]
    · have hBtop : μ B ≠ ⊤ := (MeasureTheory.measure_lt_top μ B).ne
      simp [normalizedRestrictionMeasureDefinition, smul_smul,
        ENNReal.mul_inv_cancel hB0 hBtop]
  refine ⟨hprob, hac, ?_⟩
  rw [hcancel A, hcancel Aᶜ]
  exact (MeasureTheory.Measure.restrict_add_restrict_compl hA).symm

/--
Source: Example 0.3.7, Chapter 0, Section 3.
Examples of conditional expectation for the trivial sigma-algebra and finite
partitions.
-/
theorem conditionalExpectationExamples (P : BasicProbabilitySpaceData)
    (A : Set P.X) (hA : MeasurableSet A) (hμA : 0 < P.μ A)
    (hμAc : 0 < P.μ Aᶜ)
    (Etriv : ConditionalExpectationData P {∅, Set.univ})
    (Epart : ConditionalExpectationData P {∅, A, Aᶜ, Set.univ})
    (hEtriv : IsConditionalExpectation P {∅, Set.univ} Etriv)
    (hEpart : IsConditionalExpectation P {∅, A, Aᶜ, Set.univ} Epart) :
    (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
      Etriv.op f =ᵐ[P.μ] fun _ => ∫ x, f x ∂P.μ) ∧
    (∀ f : P.X -> ℂ, MeasureTheory.Integrable f P.μ ->
      Epart.op f =ᵐ[P.μ] fun x =>
        if x ∈ A then (P.μ A).toReal⁻¹ • ∫ y in A, f y ∂P.μ
        else (P.μ Aᶜ).toReal⁻¹ • ∫ y in Aᶜ, f y ∂P.μ) := by
  exact conditionalExpectationExamplesAux P A hA hμA hμAc Etriv Epart hEtriv hEpart

/--
Source: Remark 0.3.10, Chapter 0, Section 3.
Countable generation of a sub-sigma-algebra and the associated conditional
measure notation.
-/
theorem countablyGeneratedSubSigmaAlgebraRemark {X : Type u}
    (A : SetFamily X) (G : ℕ -> Set X)
    (hgen : A = generatedSigmaAlgebra (Set.range G)) (x : X) :
    ⋂₀ {B : Set X | B ∈ A ∧ x ∈ B} =
      ⋂ n : ℕ, if x ∈ G n then G n else (G n)ᶜ := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_iInter]
    intro n
    by_cases hxn : x ∈ G n
    · simp only [hxn, if_pos]
      apply Set.mem_sInter.mp hy (G n)
      constructor
      · rw [hgen]
        exact MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩
      · exact hxn
    · simp only [hxn]
      apply Set.mem_sInter.mp hy (G n)ᶜ
      constructor
      · rw [hgen]
        exact (MeasurableSpace.measurableSet_generateFrom
          (show G n ∈ Set.range G from ⟨n, rfl⟩)).compl
      · simpa using hxn
  · intro hy
    apply Set.mem_sInter.mpr
    intro B hB
    rcases hB with ⟨hBA, hxB⟩
    have hBm : @MeasurableSet X (MeasurableSpace.generateFrom (Set.range G)) B := by
      rw [hgen] at hBA
      exact hBA
    have hpattern : ∀ n : ℕ, x ∈ G n ↔ y ∈ G n := by
      intro n
      have hyn := Set.mem_iInter.mp hy n
      by_cases hxn : x ∈ G n
      · simp only [hxn, if_pos] at hyn
        exact ⟨fun _ => hyn, fun _ => hxn⟩
      · simp only [hxn] at hyn
        exact ⟨fun hx => (hxn hx).elim, fun hyG => (hyn hyG).elim⟩
    have hxy : x ∈ B ↔ y ∈ B := by
      apply MeasurableSpace.generateFrom_induction (Set.range G)
          (fun C _ => x ∈ C ↔ y ∈ C)
      · intro C hC _
        rcases hC with ⟨n, rfl⟩
        exact hpattern n
      · simp
      · intro C _ hC
        simpa only [Set.mem_compl_iff, not_iff_not] using hC
      · intro C _ hC
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨n, hxn⟩
          exact ⟨n, (hC n).mp hxn⟩
        · rintro ⟨n, hyn⟩
          exact ⟨n, (hC n).mpr hyn⟩
      · exact hBm
    exact hxy.mp hxB

/-- Source: Remark 0.3.10. Borel atoms in a compact metric space are singletons. -/
theorem compactMetricBorelAtomIsSingleton {X : Type u} [MetricSpace X]
    [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (x : X) :
    ⋂₀ {B : Set X | MeasurableSet B ∧ x ∈ B} = {x} := by
  apply Set.Subset.antisymm
  · intro y hy
    have hyx : y ∈ ({x} : Set X) :=
      Set.mem_sInter.mp hy {x} ⟨measurableSet_singleton x, Set.mem_singleton x⟩
    simpa using hyx
  · intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact Set.mem_sInter.mpr (fun B hB => hB.2)

end Section03
end Chapter00
