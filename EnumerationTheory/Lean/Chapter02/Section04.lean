import Chapter02.Section03
import Chapter02.Ergodic.ZeroDensity
import Chapter02.Ergodic.StatisticalConvergence
import Chapter02.Spectral.WeakSpectrum
import Chapter02.Ergodic.RotationWeakMixing
import Chapter02.Ergodic.BernoulliMixing
import Chapter02.Ergodic.ProductWeakMixing
import Chapter02.Ergodic.MarkovErgodic
import Chapter02.Spectral.CompactHaarMixing

noncomputable section

open Filter

namespace Chapter02
namespace Section04

universe u v

/-- Source: Definition 2.4.1, Chapter 2, Section 4. -/
def weakStrongHigherOrderAndUniformMixingDefinitions (M : System.{u}) :
    Prop × Prop × (ℕ -> Prop) × Prop :=
  (IsWeakMixing M, IsStrongMixing M, fun k => IsKMixing M k, IsUniformMixing M)

/-- Source: Remark 2.4.2, Chapter 2, Section 4. -/
theorem mixingImplicationsAndRohlinProblem (M : System.{u}) :
    HasMixingImplications M := by
  intro hstrong
  have hM := hstrong.1
  constructor
  · refine ⟨hM, ?_⟩
    intro A B hA hB
    have hcorr := hstrong.2 A B hA hB
    have habs : Tendsto
        (fun n => |correlation M A B n - productMeasureValue M A B|)
        atTop (nhds 0) := by
      convert (hcorr.sub tendsto_const_nhds).abs using 1
      simp
    unfold cesaroTendsTo seqTendsTo cesaroAverage
    exact habs.cesaro.comp (tendsto_add_atTop_nat 1)
  · have hchar := Section03.ergodicIffCesaroCorrelations M hM
    rw [hchar]
    intro A B hA hB
    unfold cesaroTendsTo seqTendsTo cesaroAverage
    exact (hstrong.2 A B hA hB).cesaro.comp (tendsto_add_atTop_nat 1)

/-- Source: Problem 2.4.3, Chapter 2, Section 4. -/
def rohlinMultipleMixingProblem : Prop := RohlinMixingProblem.{u}

/-- Source: Remark 2.4.4, Chapter 2, Section 4. -/
def ledrappierAndRelativeRohlinCounterexamplesRemark : Prop :=
  LedrappierAndRelativeRohlinCounterexamples.{u}

/-- Source: Theorem 2.4.5, Chapter 2, Section 4. -/
theorem mixingCriteriaOnGeneratingSemiAlgebra (M : System.{u})
    (S : SetFamily M.X) :
    MixingCriteriaOnSemiAlgebra M S := by
  intro hM hS hgen
  constructor
  · constructor
    · intro hweak A B hAS hBS
      have hA : MeasurableSet A := by
        change A ∈ M.𝓧
        rw [← hgen]
        exact MeasurableSpace.measurableSet_generateFrom hAS
      have hB : MeasurableSet B := by
        change B ∈ M.𝓧
        rw [← hgen]
        exact MeasurableSpace.measurableSet_generateFrom hBS
      exact hweak.2 A B hA hB
    · intro hcorr
      refine ⟨hM, ?_⟩
      have hAlg := CorrelationSemiAlgebra.absDeviation_on_generatedAlgebra
        M hM S hS hgen hcorr
      exact CorrelationSemiAlgebra.absDeviation_on_all_measurable M hM S hgen hAlg
  · constructor
    · intro hstrong A B hAS hBS
      have hA : MeasurableSet A := by
        change A ∈ M.𝓧
        rw [← hgen]
        exact MeasurableSpace.measurableSet_generateFrom hAS
      have hB : MeasurableSet B := by
        change B ∈ M.𝓧
        rw [← hgen]
        exact MeasurableSpace.measurableSet_generateFrom hBS
      exact hstrong.2 A B hA hB
    · intro hcorr
      refine ⟨hM, ?_⟩
      have hAlg := CorrelationSemiAlgebra.seq_on_generatedAlgebra
        M hM S hS hgen hcorr
      exact CorrelationSemiAlgebra.seq_on_all_measurable M hM S hgen hAlg

/-- Source: Lemma 2.4.6, Chapter 2, Section 4. -/
theorem koopmanVonNeumannZeroDensityLemma :
    KoopmanVonNeumannZeroDensityLemma := by
  exact ZeroDensity.koopmanVonNeumannZeroDensityLemma

/-- Source: Theorem 2.4.7, Chapter 2, Section 4. -/
theorem weakMixingEquivalentDensityCharacterizations (M : System.{u}) :
    WeakMixingEquivalentCharacterizations M := by
  intro hM
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  constructor
  · intro hweak
    constructor
    · intro A B hA hB
      let d : ℕ → ℝ := fun n =>
        correlation M A B n - productMeasureValue M A B
      let a : ℕ → ℂ := fun n => (d n : ℂ)
      have hmeasure_le_one (E : Set M.X) : realMeasure M E ≤ 1 := by
        change M.μ.real E ≤ 1
        calc
          M.μ.real E ≤ M.μ.real Set.univ :=
            MeasureTheory.measureReal_mono (Set.subset_univ E) (by simp)
          _ = 1 := by simp [MeasureTheory.Measure.real]
      have hcorr_bounds (n : ℕ) : 0 ≤ correlation M A B n ∧
          correlation M A B n ≤ 1 := by
        exact ⟨MeasureTheory.measureReal_nonneg,
          hmeasure_le_one (A ∩ preimageIter M n B)⟩
      have hprod_bounds : 0 ≤ productMeasureValue M A B ∧
          productMeasureValue M A B ≤ 1 := by
        constructor
        · exact mul_nonneg MeasureTheory.measureReal_nonneg
            MeasureTheory.measureReal_nonneg
        · exact mul_le_one₀ (hmeasure_le_one A)
            MeasureTheory.measureReal_nonneg (hmeasure_le_one B)
      have ha_bdd : BddAbove (Set.range fun n => ‖a n‖) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨n, rfl⟩
        simp only [a, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_le]
        dsimp [d]
        constructor <;> linarith [hcorr_bounds n, hprod_bounds]
      have hmean : cesaroTendsTo (fun n => ‖a n‖) 0 := by
        change cesaroTendsTo (fun n => ‖(d n : ℂ)‖) 0
        rw [show (fun n => ‖(d n : ℂ)‖) = fun n => |d n| by
          funext n; rw [Complex.norm_real, Real.norm_eq_abs]]
        simpa [d] using hweak.2 A B hA hB
      obtain ⟨⟨J₀, hJ₀low, hJ₀up, haoff⟩, hsquare⟩ :=
        (koopmanVonNeumannZeroDensityLemma a ha_bdd).mp hmean
      refine ⟨J₀ᶜ, ?_, ?_⟩
      · change Chapter00.lowerAsymptoticDensity J₀ᶜ = 1
        have hcompl := Chapter00.upperAsymptoticDensity_compl J₀
        linarith
      · have hd0 : Tendsto d (Filter.principal J₀ᶜ ⊓ atTop) (nhds 0) := by
          have hre := Complex.continuous_re.continuousAt.tendsto.comp haoff
          simpa [a] using hre
        have hadd := hd0.add_const (productMeasureValue M A B)
        simpa [d, add_comm, sub_add_cancel] using hadd
    · intro A B hA hB
      let d : ℕ → ℝ := fun n =>
        correlation M A B n - productMeasureValue M A B
      let a : ℕ → ℂ := fun n => (d n : ℂ)
      have hmeasure_le_one (E : Set M.X) : realMeasure M E ≤ 1 := by
        change M.μ.real E ≤ 1
        calc
          M.μ.real E ≤ M.μ.real Set.univ :=
            MeasureTheory.measureReal_mono (Set.subset_univ E) (by simp)
          _ = 1 := by simp [MeasureTheory.Measure.real]
      have ha_bdd : BddAbove (Set.range fun n => ‖a n‖) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨n, rfl⟩
        simp only [a, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_le]
        have hc0 : 0 ≤ correlation M A B n := MeasureTheory.measureReal_nonneg
        have hc1 : correlation M A B n ≤ 1 :=
          hmeasure_le_one (A ∩ preimageIter M n B)
        have hp0 : 0 ≤ productMeasureValue M A B :=
          mul_nonneg MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
        have hp1 : productMeasureValue M A B ≤ 1 :=
          mul_le_one₀ (hmeasure_le_one A) MeasureTheory.measureReal_nonneg
            (hmeasure_le_one B)
        dsimp [d]
        constructor <;> linarith
      have hmean : cesaroTendsTo (fun n => ‖a n‖) 0 := by
        change cesaroTendsTo (fun n => ‖(d n : ℂ)‖) 0
        rw [show (fun n => ‖(d n : ℂ)‖) = fun n => |d n| by
          funext n; rw [Complex.norm_real, Real.norm_eq_abs]]
        simpa [d] using hweak.2 A B hA hB
      have hsquare := (koopmanVonNeumannZeroDensityLemma a ha_bdd).mp hmean |>.2
      change cesaroTendsTo (fun n => ‖(d n : ℂ)‖ ^ 2) 0 at hsquare
      rw [show (fun n => ‖(d n : ℂ)‖ ^ 2) = fun n => d n ^ 2 by
        funext n; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]] at hsquare
      simpa [d] using hsquare
  · rintro ⟨_, hsquares⟩
    refine ⟨hM, ?_⟩
    intro A B hA hB
    let d : ℕ → ℝ := fun n =>
      correlation M A B n - productMeasureValue M A B
    let a : ℕ → ℂ := fun n => (d n : ℂ)
    have hsquare : cesaroTendsTo (fun n => ‖a n‖ ^ 2) 0 := by
      change cesaroTendsTo (fun n => ‖(d n : ℂ)‖ ^ 2) 0
      rw [show (fun n => ‖(d n : ℂ)‖ ^ 2) = fun n => d n ^ 2 by
        funext n; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]]
      simpa [d] using hsquares A B hA hB
    have hnorm := ZeroDensity.cesaro_norm_of_cesaro_norm_sq a hsquare
    change cesaroTendsTo (fun n => ‖(d n : ℂ)‖) 0 at hnorm
    rw [show (fun n => ‖(d n : ℂ)‖) = fun n => |d n| by
      funext n; rw [Complex.norm_real, Real.norm_eq_abs]] at hnorm
    simpa [d] using hnorm

/-- Source: Theorem 2.4.8, Chapter 2, Section 4. -/
theorem spectralErgodicWeakStrongCharacterizations (M : System.{u}) :
    SpectralErgodicWeakStrongCharacterizations M := by
  intro hM
  exact ⟨CorrelationMean.ergodic_iff_cesaroFunctionCorrelations M hM,
    CorrelationMean.weakMixing_iff_functionCorrelations M hM,
    CorrelationMean.strongMixing_iff_functionCorrelations M hM⟩

/-- Source: Definition 2.4.9, Chapter 2, Section 4. -/
def weakDisjointnessDefinition (M : System.{u}) (N : System.{v}) : Prop :=
  AreWeaklyDisjoint M N

/-- Source: Theorem 2.4.10, Chapter 2, Section 4. -/
theorem weakMixingProductCharacterization (M : System.{u}) :
    ProductWeakMixingCharacterization M := by
  exact ProductWeakMixing.productWeakMixingCharacterization M

/-- Source: Definition 2.4.11, Chapter 2, Section 4. -/
def continuousSpectrumDefinition (M : System.{u}) : Prop :=
  HasContinuousSpectrum M

/-- Source: Remark 2.4.12, Chapter 2, Section 4. -/
theorem continuousSpectrumRemark (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    HasContinuousSpectrum M ↔ IsErgodic M ∧ ∀ lam : ℂ, Eigenvalue M lam -> lam = 1 := by
  have hchar := Section01.ergodicityInvariantFunctionCharacterizations M hM
  constructor
  · intro hcont
    refine ⟨?_, hcont.1⟩
    rw [hchar]
    intro f hf hinv
    by_cases hz : f =ᵐ[M.μ] 0
    · exact ⟨0, hz⟩
    · apply hcont.2 f
      refine ⟨hf, hz, ?_⟩
      simpa using hinv
  · rintro ⟨herg, hlam⟩
    refine ⟨hlam, ?_⟩
    intro f hf
    apply (hchar.mp herg) f hf.1
    simpa using hf.2.2

/-- Source: Theorem 2.4.13, Chapter 2, Section 4. -/
theorem weakMixingIffContinuousSpectrum (M : System.{u}) :
    WeakMixingIffContinuousSpectrum M := by
  exact WeakSpectrum.weakMixing_iff_continuousSpectrum M

/-- Source: Proposition 2.4.14, Chapter 2, Section 4. -/
theorem compactMetricAbelianGroupRotationNotWeakMixing :
    RotationNotWeakMixingStatement := by
  exact RotationWeakMixing.rotationNotWeakMixing

/-- Source: Theorem 2.4.15, Chapter 2, Section 4. -/
theorem compactAbelianGroupEndomorphismMixingEquivalence :
    CompactGroupEndomorphismMixingEquivalence := by
  intro G _ _ _ _ _ _ m hprob hhaar A hAcont hAsurj
  letI : MeasureTheory.IsProbabilityMeasure m := hprob
  letI : m.IsHaarMeasure := hhaar
  let M := compactGroupHaarEndomorphismSystem m A
  have hmp : MeasureTheory.MeasurePreserving A m m :=
    CompactHaarCharacters.haarEndomorphism_measurePreserving
      m A hAcont hAsurj
  have hM : Chapter01.IsMeasurePreservingSystem M := ⟨hprob, hmp⟩
  have hergStrong : IsErgodic M → IsStrongMixing M := by
    intro herg
    have haperiodic :
        ∀ χ : ContinuousMultiplicativeCircleCharacter G,
          (∃ n : ℕ, 0 < n ∧
            (fun x => χ.toFun ((A : G → G)^[n] x)) = χ.toFun) →
          ∀ x, χ.toFun x = 1 := by
      intro χ hperiodic
      exact
        Section01.ergodic_compactGroupEndomorphism_has_no_nontrivial_periodic_character
          G m hprob hhaar A hAcont hAsurj herg χ hperiodic
    exact CompactHaarMixing.strongMixing_of_aperiodic_characters
      m A hAcont hAsurj haperiodic
  have hstrongWeak : IsStrongMixing M → IsWeakMixing M :=
    fun hstrong => (mixingImplicationsAndRohlinProblem M hstrong).1
  have hweakErg : IsWeakMixing M → IsErgodic M :=
    WeakSpectrum.weakMixing_to_ergodic M
  exact
    ⟨⟨fun herg => hstrongWeak (hergStrong herg), hweakErg⟩,
      ⟨fun hweak => hergStrong (hweakErg hweak), hstrongWeak⟩⟩

/-- Source: Theorem 2.4.16, Chapter 2, Section 4. -/
theorem bernoulliShiftIsStrongMixing :
    BernoulliShiftStrongMixingStatement := by
  exact BernoulliMixing.bernoulliShiftStrongMixing

/-- Source: Theorem 2.4.17, Chapter 2, Section 4. -/
theorem markovShiftMixingEquivalentConditions :
    MarkovShiftMixingCharacterization := by
  intro M k p P h hp
  exact ⟨MarkovErgodic.markovShiftWeakMixing_iff_strongMixing k p P h hp,
    MarkovErgodic.markovShiftStrongMixing_iff_primitive k p P h hp,
    MarkovErgodic.markovShiftPrimitive_iff_entrywise_limit k p P h hp⟩

/-- Source: Definition 2.4.18, Chapter 2, Section 4. -/
def familyConvergenceDefinition {α : Type u} [TopologicalSpace α]
    (F : Set (Set ℕ)) (x : ℕ -> α) (a : α) : Prop :=
  FamilyConvergesTo F x a

/-- Source: Theorem 2.4.19, Chapter 2, Section 4. -/
theorem weakAndStrongMixingAsFamilyLimits (M : System.{u}) :
    Chapter01.IsMeasurePreservingSystem M ->
    (IsWeakMixing M ↔ ∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 ->
      FamilyConvergesTo Chapter00.densityOneFamily (fun n => correlation M A B n)
        (productMeasureValue M A B)) ∧
    (IsStrongMixing M ↔ ∀ A B : Set M.X, A ∈ M.𝓧 -> B ∈ M.𝓧 ->
      FamilyConvergesTo {E : Set ℕ | Set.Finite Eᶜ} (fun n => correlation M A B n)
        (productMeasureValue M A B)) := by
  intro hM
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hmeasure_le_one (E : Set M.X) : realMeasure M E ≤ 1 := by
    change M.μ.real E ≤ 1
    calc
      M.μ.real E ≤ M.μ.real Set.univ :=
        MeasureTheory.measureReal_mono (Set.subset_univ E) (by simp)
      _ = 1 := by simp [MeasureTheory.Measure.real]
  have hdeviation_bound (A B : Set M.X) (n : ℕ) :
      |correlation M A B n - productMeasureValue M A B| ≤ 1 := by
    have hc0 : 0 ≤ correlation M A B n := MeasureTheory.measureReal_nonneg
    have hc1 : correlation M A B n ≤ 1 :=
      hmeasure_le_one (A ∩ preimageIter M n B)
    have hp0 : 0 ≤ productMeasureValue M A B :=
      mul_nonneg MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
    have hp1 : productMeasureValue M A B ≤ 1 :=
      mul_le_one₀ (hmeasure_le_one A) MeasureTheory.measureReal_nonneg
        (hmeasure_le_one B)
    rw [abs_le]
    constructor <;> linarith
  constructor
  · constructor
    · intro hweak A B hA hB
      apply (StatisticalConvergence.familyConvergesTo_densityOne_iff_threshold
        (fun n => correlation M A B n) (productMeasureValue M A B)).2
      exact (StatisticalConvergence.cesaroTendsTo_zero_iff_densityOne_lt
        (fun n => |correlation M A B n - productMeasureValue M A B|) 1
        (fun n => abs_nonneg _) (by norm_num)
        (hdeviation_bound A B)).1 (hweak.2 A B hA hB)
    · intro hfamily
      refine ⟨hM, ?_⟩
      intro A B hA hB
      apply (StatisticalConvergence.cesaroTendsTo_zero_iff_densityOne_lt
        (fun n => |correlation M A B n - productMeasureValue M A B|) 1
        (fun n => abs_nonneg _) (by norm_num)
        (hdeviation_bound A B)).2
      exact (StatisticalConvergence.familyConvergesTo_densityOne_iff_threshold
        (fun n => correlation M A B n) (productMeasureValue M A B)).1
        (hfamily A B hA hB)
  · constructor
    · intro hstrong A B hA hB
      exact (StatisticalConvergence.familyConvergesTo_cofinite_iff_tendsto
        (fun n => correlation M A B n) (productMeasureValue M A B)).2
        (hstrong.2 A B hA hB)
    · intro hfamily
      refine ⟨hM, ?_⟩
      intro A B hA hB
      exact (StatisticalConvergence.familyConvergesTo_cofinite_iff_tendsto
        (fun n => correlation M A B n) (productMeasureValue M A B)).1
        (hfamily A B hA hB)

/-- Source: Definition 2.4.20, Chapter 2, Section 4. -/
def ipAndIpStarSetDefinitions (A : Set ℕ) : Prop × Prop :=
  (IsIPSet A, IsIPStarSet A)

/-- Source: Definition 2.4.21, Chapter 2, Section 4. -/
def mildMixingAndRigidFunctionDefinitions (M : System.{u}) :
    Prop × ((M.X -> ℂ) -> Prop) :=
  (IsMildMixing M, IsRigidFunction M)

end Section04
end Chapter02
