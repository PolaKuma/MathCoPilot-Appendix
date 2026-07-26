import Chapter02.Section02
import Chapter02.Ergodic.CorrelationMean
import Chapter02.Ergodic.CorrelationSemiAlgebra
import Chapter02.Ergodic.BorelNormal
import Chapter02.Ergodic.HopfMaximal
import Chapter02.Ergodic.Birkhoff
import Chapter02.Ergodic.StochasticCesaro
import Chapter02.Ergodic.FiniteMarkov
import Mathlib.Probability.StrongLaw

noncomputable section

open Filter

namespace Chapter02
namespace Section03

universe u

/-- Source: Theorem 2.3.1, Chapter 2, Section 3. -/
theorem birkhoffPointwiseErgodicTheorem (M : System.{u}) :
    BirkhoffPointwiseErgodicStatement M := by
  exact Birkhoff.birkhoffPointwiseErgodic M

/-- Source: Remark 2.3.2, Chapter 2, Section 3. -/
theorem timeAverageEqualsSpaceAverageForErgodicSystems (M : System.{u}) :
    ErgodicTimeAverageEqualsSpaceAverage M := by
  intro hM f hf
  obtain ⟨fstar, hfstar, hinv, hlim, hint⟩ :=
    birkhoffPointwiseErgodicTheorem M hM.1 f hf
  obtain ⟨c, hc⟩ :=
    (Section01.isErgodic_to_mathlibErgodic M hM).ae_eq_const_of_ae_eq_comp_ae
      hfstar.aestronglyMeasurable hinv
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  have hci : (∫ x, fstar x ∂M.μ) = c := by
    calc
      (∫ x, fstar x ∂M.μ) = ∫ _x, c ∂M.μ :=
        MeasureTheory.integral_congr_ae hc
      _ = c := by simp
  have hc_eq : c = ∫ x, f x ∂M.μ := hci.symm.trans hint
  filter_upwards [hlim, hc] with x hx hcx
  simpa [hcx, hc_eq] using hx

/-- Source: Theorem 2.3.3, Chapter 2, Section 3. -/
theorem maximalErgodicTheoremPositiveContraction (M : System.{u}) :
    PositiveContractionMaximalStatement M := by
  exact HopfMaximal.positiveContractionMaximal M

/-- Source: Theorem 2.3.4, Chapter 2, Section 3. -/
theorem maximalErgodicInequality (M : System.{u}) :
    MaximalErgodicStatement M := by
  exact HopfMaximal.maximalErgodic M

/-- Source: Remark 2.3.5, Chapter 2, Section 3. -/
theorem weakTypeMaximalInequalityRemark (M : System.{u}) :
    WeakTypeMaximalInequalityStatement M := by
  exact HopfMaximal.weakTypeMaximal M

/-- Source: Remark 2.3.6, Chapter 2, Section 3. -/
theorem lOneMeanErgodicProofOfBirkhoffIntegrability (M : System.{u}) :
    LOneMeanErgodicIdentifiesPointwiseLimitStatement M := by
  intro hM hmean f fstar hf hpoint
  obtain ⟨g, hg, hginv, hnorm, hce, hint, hgerg⟩ := hmean hM f hf
  have havgMeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable (ergodicAverage M f n) M.μ := by
    intro n
    exact (ErgodicAverageLp.ergodicAverage_memLp M hM 1 f hf n).aestronglyMeasurable
  have hinMeasure : MeasureTheory.TendstoInMeasure M.μ
      (fun n => ergodicAverage M f n) atTop g := by
    exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num) havgMeas hg.aestronglyMeasurable hnorm
  obtain ⟨ns, hns, hsub⟩ := hinMeasure.exists_seq_tendsto_ae
  have hfg : fstar =ᵐ[M.μ] g := by
    filter_upwards [hpoint, hsub] with x hx hxs
    have hxsub : Tendsto (fun i => ergodicAverage M f (ns i) x)
        atTop (nhds (fstar x)) := hx.comp hns.tendsto_atTop
    exact tendsto_nhds_unique hxsub hxs
  constructor
  · exact ⟨hg.aestronglyMeasurable.congr hfg.symm,
      (MeasureTheory.eLpNorm_congr_ae hfg).trans_lt hg.eLpNorm_lt_top⟩
  · calc
      ∫ x, fstar x ∂M.μ = ∫ x, g x ∂M.μ :=
        MeasureTheory.integral_congr_ae hfg
      _ = ∫ x, f x ∂M.μ := hint

/-- Source: Theorem 2.3.7, Chapter 2, Section 3. -/
theorem denseCoboundariesInKernelOfInvariantExpectation (M : System.{u}) :
    DenseCoboundariesStatement M := by
  intro hM f hf hcezero ε hε
  let mInv : MeasurableSpace M.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hconv := ErgodicAverageLp.tendsto_ergodicAverage_condExp_one M hM f hf
  have hconv0 : Tendsto (fun n => MeasureTheory.eLpNorm
      (ergodicAverage M f n) 1 M.μ) atTop (nhds 0) := by
    apply hconv.congr'
    filter_upwards [] with n
    apply MeasureTheory.eLpNorm_congr_ae
    filter_upwards [hcezero] with x hx
    simp [hx]
  have hpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hev : ∀ᶠ n in atTop,
      MeasureTheory.eLpNorm (ergodicAverage M f n) 1 M.μ < ENNReal.ofReal ε :=
    hconv0.eventually (Iio_mem_nhds hpos)
  have hevpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  obtain ⟨N, hNavg, hNpos⟩ := (hev.and hevpos).exists
  let g := ErgodicAverageLp.coboundaryApproximant M f N
  refine ⟨g, ErgodicAverageLp.coboundaryApproximant_memLp_one M hM f hf N, ?_⟩
  have hid : (fun x => f x - (g (M.T x) - g x)) = ergodicAverage M f N := by
    funext x
    exact ErgodicAverageLp.coboundaryApproximant_identity M f N
      (Nat.ne_of_gt hNpos) x
  rw [hid]
  exact hNavg

/-- Source: Theorem 2.3.8, Chapter 2, Section 3. -/
theorem vonNeumannLpErgodicTheorem (M : System.{u}) (p : ENNReal)
    (hp : 1 ≤ p) (hp_top : p < ⊤) :
    MeanErgodicSystemStatement M p := by
  exact Section02.lpMeanErgodicTheorem M p hp hp_top

/-- Source: Corollary 2.3.9, Chapter 2, Section 3. -/
theorem orbitVisitSetHasDensityMeasure (M : System.{u}) :
    OrbitVisitDensityStatement M := by
  intro hM A hA
  classical
  let f : M.X → ℂ := A.indicator fun _ => 1
  have hf : M.lpMember 1 f := by
    letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
    exact MeasureTheory.memLp_indicator_const 1 hA 1 (Or.inr (by simp))
  have htime := timeAverageEqualsSpaceAverageForErgodicSystems M hM f hf
  filter_upwards [htime] with x hx
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hx
  have hseq : (fun n : ℕ => (ergodicAverage M f n x).re) =
      (fun n : ℕ => if n = 0 then 0 else
        ((n : ℝ)⁻¹) * ((Finset.range n).filter
          (fun i => (M.T^[i]) x ∈ A)).card) := by
    funext n
    by_cases hn : n = 0
    · simp [ergodicAverage, hn]
    · have hsum : ∑ i ∈ Finset.range n, f ((M.T^[i]) x) =
          (((Finset.range n).filter
            (fun i => (M.T^[i]) x ∈ A)).card : ℂ) := by
        calc
          ∑ i ∈ Finset.range n, f ((M.T^[i]) x) =
              ∑ i ∈ Finset.range n,
                if (M.T^[i]) x ∈ A then (1 : ℂ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  simp [f, Set.indicator]
          _ = (((Finset.range n).filter
              (fun i => (M.T^[i]) x ∈ A)).card : ℂ) := by simp
      simp only [ergodicAverage, hn, if_false]
      rw [hsum]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      rw [Complex.mul_re, Complex.inv_re, Complex.inv_im]
      rw [Complex.natCast_re, Complex.natCast_im, Complex.normSq_natCast]
      change (n : ℝ) / ((n : ℝ) * n) *
          (((Finset.range n).filter (fun i => (M.T^[i]) x ∈ A)).card : ℝ) -
        -0 / ((n : ℝ) * n) * 0 =
          (n : ℝ)⁻¹ *
            (((Finset.range n).filter (fun i => (M.T^[i]) x ∈ A)).card : ℝ)
      field_simp
      ring
  have hlim : (∫ y, f y ∂M.μ).re = realMeasure M A := by
    simp [f, realMeasure, MeasureTheory.integral_indicator hA,
      MeasureTheory.Measure.real]
  change Tendsto (fun n => (ergodicAverage M f n x).re) atTop
    (nhds (∫ y, f y ∂M.μ).re) at hre
  rw [hseq] at hre
  simpa only [Function.comp_apply, hlim] using hre

/-- Source: Theorem 2.3.10, Chapter 2, Section 3. -/
theorem borelNormalNumberTheorem : BorelNormalNumberTheoremStatement := by
  exact BorelNormal.borel_normal_of_orbit_visit
    (orbitVisitSetHasDensityMeasure (circleEndomorphismSystem 2))
    (Section01.circleEndomorphismIsErgodic 2 (by norm_num))

/-- Source: Theorem 2.3.11, Chapter 2, Section 3. -/
theorem ergodicIffCesaroCorrelations (M : System.{u}) :
    ErgodicIffCesaroCorrelations M := by
  intro hM
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  constructor
  · intro hErg A B hA hB
    exact CorrelationMean.ergodic_cesaroCorrelations M hM hErg A B hA hB
  · intro hcorr
    refine ⟨hM, ?_⟩
    intro A hA hnull
    have hself := CorrelationMean.cesaroCorrelation_self_of_invariant M hM A hnull
    have hprod := hcorr A A hA hA
    have heq : realMeasure M A = productMeasureValue M A A :=
      tendsto_nhds_unique hself hprod
    have hidem : realMeasure M A * (realMeasure M A - 1) = 0 := by
      unfold productMeasureValue at heq
      nlinarith
    rcases mul_eq_zero.mp hidem with hzero | hone
    · left
      have hrealzero : realMeasure M A = 0 := hzero
      apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
        (by simp : (0 : ENNReal) ≠ ⊤)).mp
      simpa [realMeasure] using hrealzero
    · right
      have hrealone : realMeasure M A = 1 := by nlinarith
      apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
        (by simp : (1 : ENNReal) ≠ ⊤)).mp
      simpa [realMeasure] using hrealone

/-- Source: Theorem 2.3.12, Chapter 2, Section 3. -/
theorem ergodicIffCesaroCorrelationsOnSemiAlgebra (M : System.{u})
    (S : SetFamily M.X) :
    ErgodicIffOnGeneratingSemiAlgebra M S := by
  intro hM hS hgen
  constructor
  · intro hErg A B hAS hBS
    have hA : MeasurableSet A := by
      change A ∈ M.𝓧
      rw [← hgen]
      exact MeasurableSpace.measurableSet_generateFrom hAS
    have hB : MeasurableSet B := by
      change B ∈ M.𝓧
      rw [← hgen]
      exact MeasurableSpace.measurableSet_generateFrom hBS
    exact CorrelationMean.ergodic_cesaroCorrelations M hM hErg A B hA hB
  · intro hcorr
    have hAlg := CorrelationSemiAlgebra.cesaro_on_generatedAlgebra
      M hM S hS hgen hcorr
    have hAll := CorrelationSemiAlgebra.cesaro_on_all_measurable
      M hM S hgen hAlg
    exact (ergodicIffCesaroCorrelations M hM).2 hAll

/-- Source: Theorem 2.3.13, Chapter 2, Section 3. -/
theorem kolmogorovStrongLawOfLargeNumbers : StrongLawStatement := by
  intro P X hprob hint hmap hind
  letI : MeasureTheory.IsProbabilityMeasure P.μ := hprob
  have hi : ProbabilityTheory.iIndepFun X P.μ := by
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro I B hB
    have h := hind I B hB
    have hs : (⋂ i ∈ I, X i ⁻¹' B i) =
        {ω | ∀ i ∈ I, X i ω ∈ B i} := by
      ext ω
      simp
    rw [hs]
    exact h
  have hpw : Pairwise (fun i j =>
      ProbabilityTheory.IndepFun (X i) (X j) P.μ) := by
    intro i j hij
    exact hi.indepFun hij
  have hid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P.μ P.μ := by
    intro i
    exact
      { aemeasurable_fst := (hint i).aestronglyMeasurable.aemeasurable
        aemeasurable_snd := (hint 0).aestronglyMeasurable.aemeasurable
        map_eq := hmap i }
  have hstrong := ProbabilityTheory.strong_law_ae X (hint 0) hpw hid
  filter_upwards [hstrong] with ω hω
  convert hω using 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, smul_eq_mul]

/-- Source: Lemma 2.3.14, Chapter 2, Section 3. -/
theorem stochasticMatrixCesaroLimit : StochasticMatrixLimitStatement := by
  exact StochasticCesaro.stochasticMatrixCesaroLimit

/-- Source: Theorem 2.3.15, Chapter 2, Section 3. -/
theorem markovShiftErgodicityEquivalentConditions :
    MarkovShiftErgodicEquivalentConditionsStatement := by
  intro M k p P Q hshift hp hQ
  have hshift' := hshift
  have hparams :
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      (∀ i j, 0 ≤ P i j) ∧ (∀ i, (∑ j, P i j) = 1) ∧
      (∀ j, (∑ i, p i * P i j) = p j) := by
    rcases hshift' with hone | htwo
    · rcases hone with ⟨_hM, e, he, heinv, hcomm, hp0, hpsum,
          hP0, hPsum, hstationary, hcyl⟩
      exact ⟨hp0, hpsum, hP0, hPsum, hstationary⟩
    · rcases htwo with ⟨_hM, e, he, heinv, hcomm, hp0, hpsum,
          hP0, hPsum, hstationary, hcyl⟩
      exact ⟨hp0, hpsum, hP0, hPsum, hstationary⟩
  rcases hparams with ⟨_hp0, hpsum, hP0, hPsum, hstationary⟩
  have heq := FiniteMarkov.rowsEqual_iff_strictlyPositive_iff_irreducible
    p P Q hp hpsum hP0 hPsum hstationary hQ
  have hrows_irred : StochasticMatrixRowsEqual Q ↔
      IsIrreducibleStochasticMatrix P := heq.1.trans heq.2
  have herg_irred : IsErgodic M ↔ IsIrreducibleStochasticMatrix P :=
    Section01.markovShiftErgodicIffIrreducible M k p P hshift hp
  have hirred_simple := FiniteMarkov.irreducible_iff_hasSimpleEigenvalueOne
    p P Q hp hpsum hP0 hPsum hstationary hQ
  exact ⟨herg_irred.trans hrows_irred.symm, heq.1, heq.2, hirred_simple⟩

end Section03
end Chapter02
