import Chapter03.ContinuedFractions.DigitFrequency
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter03

noncomputable def logDigitObservable (y : GaussSpace) : ℝ :=
  Real.log (gaussDigit y.1 0 : ℝ)

theorem logDigitObservable_measurable : Measurable logDigitObservable := by
  have hval : Measurable fun y : GaussSpace => y.1 := measurable_subtype_coe
  have hinv : Measurable fun y : GaussSpace => y.1⁻¹ := measurable_inv.comp hval
  have hfloor : Measurable fun y : GaussSpace => Int.floor y.1⁻¹ :=
    Int.measurable_floor.comp hinv
  have htoNat : Measurable fun z : ℤ => z.toNat := measurable_of_countable _
  have hcast : Measurable fun n : ℕ => (n : ℝ) := measurable_of_countable _
  exact (hcast.comp (htoNat.comp hfloor)).log

theorem logDigitObservable_nonneg (y : GaussSpace) :
    0 ≤ logDigitObservable y := by
  exact Real.log_natCast_nonneg _

noncomputable def negLogVal (y : GaussSpace) : ℝ := -Real.log y.1

theorem negLogVal_integrable : Integrable negLogVal gaussMeasure := by
  have hproj : Measurable unitIntervalProjection := by
    apply Measurable.subtype_mk
    fun_prop
  rw [gaussMeasure]
  apply (integrable_map_measure
    (show AEStronglyMeasurable negLogVal
        (Measure.map unitIntervalProjection gaussMeasureOnReal) from
      (show Measurable negLogVal by
        change Measurable fun y : GaussSpace => -Real.log y.1
        fun_prop).aestronglyMeasurable)
    hproj.aemeasurable).2
  rw [gaussMeasureOnReal]
  have hdmeas : Measurable fun x : ℝ => ENNReal.ofReal (gaussDensityReal x) := by
    apply Measurable.ennreal_ofReal
    change Measurable fun x : ℝ => (Real.log 2 * (1 + x))⁻¹
    fun_prop
  apply (integrable_withDensity_iff hdmeas (by simp)).2
  have hlogInterval : IntervalIntegrable Real.log volume (0 : ℝ) 1 := by
    apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
    rw [integral_log]
    norm_num
  have hlogIoc : IntegrableOn Real.log (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 hlogInterval
  have hlogIcc : IntegrableOn Real.log (Set.Icc (0 : ℝ) 1) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo, ← integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hlogIoc
  have hdensMeas : AEStronglyMeasurable gaussDensityReal
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply AEMeasurable.aestronglyMeasurable
    exact (show Measurable gaussDensityReal by
      change Measurable fun x : ℝ => (Real.log 2 * (1 + x))⁻¹
      fun_prop).aemeasurable
  have hdensBound : ∀ᵐ x ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      ‖gaussDensityReal x‖ ≤ (Real.log 2)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hx1 : 1 ≤ 1 + x := by linarith [hx.1]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · dsimp [gaussDensityReal]
      exact (inv_le_inv₀ (mul_pos hlog (by linarith [hx.1])) hlog).2
        (by nlinarith)
    · dsimp [gaussDensityReal]
      positivity
  have hweighted : Integrable
      (fun x : ℝ => (-Real.log x) * gaussDensityReal x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hlogIcc.neg.mul_bdd hdensMeas hdensBound
  apply hweighted.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hprojx : (unitIntervalProjection x).1 = x := by
    simp [unitIntervalProjection, min_eq_right hx.2, max_eq_right hx.1]
  simp only [Function.comp_apply, negLogVal, hprojx]
  rw [ENNReal.toReal_ofReal]
  change 0 ≤ (Real.log 2 * (1 + x))⁻¹
  exact inv_nonneg.mpr (mul_nonneg (Real.log_pos (by norm_num)).le (by linarith [hx.1]))

theorem negLogVal_nonneg (y : GaussSpace) : 0 ≤ negLogVal y := by
  change 0 ≤ -Real.log y.1
  exact neg_nonneg.mpr (Real.log_nonpos y.2.1 y.2.2)

theorem logDigitObservable_le_negLogVal (y : GaussSpace) (hy : 0 < y.1) :
    logDigitObservable y ≤ negLogVal y := by
  have hinv : (1 : ℝ) ≤ y.1⁻¹ := (one_le_inv₀ hy).2 y.2.2
  have hfloorNonneg : 0 ≤ Int.floor y.1⁻¹ :=
    Int.floor_nonneg.mpr (le_trans (by norm_num) hinv)
  have hdigitCast : (gaussDigit y.1 0 : ℝ) = (Int.floor y.1⁻¹ : ℝ) := by
    simp only [gaussDigit, Function.iterate_zero_apply]
    exact_mod_cast Int.toNat_of_nonneg hfloorNonneg
  have hfloorPos : (0 : ℝ) < (Int.floor y.1⁻¹ : ℝ) := by
    have : (1 : ℤ) ≤ Int.floor y.1⁻¹ := Int.le_floor.mpr (by exact_mod_cast hinv)
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1) this)
  have hfloorLe : (Int.floor y.1⁻¹ : ℝ) ≤ y.1⁻¹ := Int.floor_le _
  change Real.log (gaussDigit y.1 0 : ℝ) ≤ -Real.log y.1
  rw [hdigitCast, ← Real.log_inv]
  exact Real.strictMonoOn_log.monotoneOn
    (show (Int.floor y.1⁻¹ : ℝ) ∈ Set.Ioi 0 from hfloorPos)
    (show y.1⁻¹ ∈ Set.Ioi 0 from inv_pos.mpr hy) hfloorLe

theorem logDigitObservable_integrable :
    Integrable logDigitObservable gaussMeasure := by
  apply negLogVal_integrable.mono logDigitObservable_measurable.aestronglyMeasurable
  filter_upwards [ae_gaussMeasure_irrational] with y hyirr
  have hy : 0 < y.1 := lt_of_le_of_ne y.2.1 (by
    intro h
    apply hyirr
    exact ⟨0, by norm_num; exact h⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (logDigitObservable_nonneg y),
    Real.norm_eq_abs, abs_of_nonneg (negLogVal_nonneg y)]
  exact logDigitObservable_le_negLogVal y hy

theorem digitCylinder_succ_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint fun n : ℕ => testCylinder (n + 1)) := by
  intro n m hnm
  change Disjoint (testCylinder (n + 1)) (testCylinder (m + 1))
  rw [Set.disjoint_left]
  intro y hyn hym
  have hn : gaussDigit y.1 0 = n + 1 :=
    (test_digit_mem (n + 1) (by omega) y).2 hyn
  have hm : gaussDigit y.1 0 = m + 1 :=
    (test_digit_mem (m + 1) (by omega) y).2 hym
  omega

theorem ae_mem_iUnion_digitCylinder :
    ∀ᵐ y ∂gaussMeasure, y ∈ ⋃ n : ℕ, testCylinder (n + 1) := by
  filter_upwards [ae_gaussMeasure_irrational] with y hyirr
  have hy : 0 < y.1 := lt_of_le_of_ne y.2.1 (by
    intro h
    apply hyirr
    exact ⟨0, by norm_num; exact h⟩)
  have hdigitPos : 0 < gaussDigit y.1 0 := by
    simp only [gaussDigit, Function.iterate_zero_apply]
    have hinv : (1 : ℝ) ≤ y.1⁻¹ := (one_le_inv₀ hy).2 y.2.2
    have hfloor : (1 : ℤ) ≤ Int.floor y.1⁻¹ :=
      Int.le_floor.mpr (by exact_mod_cast hinv)
    have hnonneg : 0 ≤ Int.floor y.1⁻¹ := le_trans (by norm_num) hfloor
    rw [show Int.toNat (Int.floor y.1⁻¹) = (Int.floor y.1⁻¹).toNat from rfl]
    omega
  rw [Set.mem_iUnion]
  refine ⟨gaussDigit y.1 0 - 1, ?_⟩
  apply (test_digit_mem (gaussDigit y.1 0 - 1 + 1) (by omega) y).1
  omega

theorem integral_logDigit_eq_tsum_cylinders :
    (∫ y, logDigitObservable y ∂gaussMeasure) =
      ∑' n : ℕ, Real.log (n + 1 : ℝ) *
        gaussMeasure.real (testCylinder (n + 1)) := by
  have hpartition := integral_iUnion
    (fun n : ℕ => testCylinder_measurable (n + 1))
    digitCylinder_succ_pairwiseDisjoint
    (logDigitObservable_integrable.integrableOn :
      IntegrableOn logDigitObservable (⋃ n : ℕ, testCylinder (n + 1)) gaussMeasure)
  calc
    (∫ y, logDigitObservable y ∂gaussMeasure) =
        ∫ y in ⋃ n : ℕ, testCylinder (n + 1), logDigitObservable y ∂gaussMeasure := by
      rw [← integral_indicator (MeasurableSet.iUnion fun n => testCylinder_measurable (n + 1))]
      apply integral_congr_ae
      filter_upwards [ae_mem_iUnion_digitCylinder] with y hy
      simp only [Set.indicator_of_mem hy]
    _ = ∑' n : ℕ, ∫ y in testCylinder (n + 1),
        logDigitObservable y ∂gaussMeasure := hpartition
    _ = _ := by
      congr 1
      funext n
      calc
        (∫ y in testCylinder (n + 1), logDigitObservable y ∂gaussMeasure) =
            ∫ _y in testCylinder (n + 1), Real.log (n + 1 : ℝ) ∂gaussMeasure := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (testCylinder_measurable (n + 1))] with y hy
          change Real.log (gaussDigit y.1 0 : ℝ) = _
          rw [(test_digit_mem (n + 1) (by omega) y).2 hy]
          norm_num only [Nat.cast_add, Nat.cast_one]
        _ = _ := by
          rw [setIntegral_const]
          simp [mul_comm]

noncomputable def logDigitCylinderTerm (n : ℕ) : ℝ :=
  Real.log (n + 1 : ℝ) * gaussMeasure.real (testCylinder (n + 1))

theorem logDigitCylinderTerm_nonneg (n : ℕ) : 0 ≤ logDigitCylinderTerm n := by
  apply mul_nonneg
  · simpa only [Nat.cast_add, Nat.cast_one] using Real.log_natCast_nonneg (n + 1)
  · rw [Measure.real_def]
    exact ENNReal.toReal_nonneg

theorem summable_logDigitCylinderTerm : Summable logDigitCylinderTerm := by
  apply summable_of_sum_le logDigitCylinderTerm_nonneg
    (c := ∫ y, logDigitObservable y ∂gaussMeasure)
  intro u
  have hsum : ∑ n ∈ u, logDigitCylinderTerm n =
      ∑ n ∈ u, ∫ y in testCylinder (n + 1),
        logDigitObservable y ∂gaussMeasure := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [logDigitCylinderTerm]
    symm
    calc
      (∫ y in testCylinder (n + 1), logDigitObservable y ∂gaussMeasure) =
          ∫ _y in testCylinder (n + 1), Real.log (n + 1 : ℝ) ∂gaussMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (testCylinder_measurable (n + 1))] with y hy
        change Real.log (gaussDigit y.1 0 : ℝ) = _
        rw [(test_digit_mem (n + 1) (by omega) y).2 hy]
        norm_num only [Nat.cast_add, Nat.cast_one]
      _ = _ := by
        rw [setIntegral_const]
        simp [mul_comm]
  rw [hsum, ← integral_biUnion_finset]
  · rw [show (∫ y, logDigitObservable y ∂gaussMeasure) =
        ∫ y in Set.univ, logDigitObservable y ∂gaussMeasure by simp]
    apply setIntegral_mono_set logDigitObservable_integrable.integrableOn
      (Filter.Eventually.of_forall logDigitObservable_nonneg)
    filter_upwards [] with y
    exact fun _ => Set.mem_univ y
  · intro n hn
    exact testCylinder_measurable (n + 1)
  · intro n hn m hm hnm
    exact digitCylinder_succ_pairwiseDisjoint hnm
  · intro n hn
    exact logDigitObservable_integrable.integrableOn

noncomputable def khinchinLogTerm (n : ℕ) : ℝ :=
  Real.log (n + 1 : ℝ) *
    ((2 * Real.log (n + 2 : ℝ) - Real.log (n + 1 : ℝ) -
      Real.log (n + 3 : ℝ)) / Real.log 2)

theorem logDigitCylinderTerm_eq_khinchinLogTerm (n : ℕ) :
    logDigitCylinderTerm n = khinchinLogTerm n := by
  dsimp [logDigitCylinderTerm, khinchinLogTerm]
  rw [Measure.real_def, testCylinder_measure (n + 1) (by omega),
    ENNReal.toReal_ofReal (testConstant_nonneg (n + 1) (by omega))]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 3 <;> ring_nf

theorem summable_khinchinLogTerm : Summable khinchinLogTerm := by
  exact summable_logDigitCylinderTerm.congr logDigitCylinderTerm_eq_khinchinLogTerm

theorem integral_logDigit_eq_tsum_khinchinLogTerm :
    (∫ y, logDigitObservable y ∂gaussMeasure) = ∑' n, khinchinLogTerm n := by
  rw [integral_logDigit_eq_tsum_cylinders]
  apply tsum_congr
  intro n
  exact logDigitCylinderTerm_eq_khinchinLogTerm n

theorem khinchin_factor_eq_exp (n : ℕ) :
    Real.rpow (((n + 2 : ℝ) ^ 2) / ((n + 1 : ℝ) * (n + 3 : ℝ)))
        (Real.log (n + 1 : ℝ) / Real.log 2) =
      Real.exp (khinchinLogTerm n) := by
  have hbase : 0 < (((n + 2 : ℝ) ^ 2) / ((n + 1 : ℝ) * (n + 3 : ℝ))) := by
    positivity
  change (((n + 2 : ℝ) ^ 2) / ((n + 1 : ℝ) * (n + 3 : ℝ))) ^
      (Real.log (n + 1 : ℝ) / Real.log 2) = _
  rw [Real.rpow_def_of_pos hbase]
  congr 1
  dsimp [khinchinLogTerm]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) (by positivity)]
  ring

theorem exp_integral_logDigit_eq_khinchinConstant :
    Real.exp (∫ y, logDigitObservable y ∂gaussMeasure) = khinchinConstant := by
  rw [integral_logDigit_eq_tsum_khinchinLogTerm, khinchinConstant]
  symm
  calc
    (∏' n : ℕ, Real.rpow (((n + 2 : ℝ) ^ 2) /
        ((n + 1 : ℝ) * (n + 3 : ℝ)))
        (Real.log (n + 1 : ℝ) / Real.log 2)) =
        ∏' n : ℕ, Real.exp (khinchinLogTerm n) := by
      apply tprod_congr
      intro n
      exact khinchin_factor_eq_exp n
    _ = Real.exp (∑' n : ℕ, khinchinLogTerm n) := by
      simpa only [Function.comp_apply] using
        summable_khinchinLogTerm.hasSum.rexp.tprod_eq

noncomputable def complexLogDigitObservable (y : GaussSpace) : ℂ :=
  (logDigitObservable y : ℂ)

theorem complexLogDigitObservable_integrable :
    Integrable complexLogDigitObservable gaussMeasure := by
  apply logDigitObservable_integrable.mono
  · exact (Complex.continuous_ofReal.measurable.comp
      logDigitObservable_measurable).aestronglyMeasurable
  · filter_upwards [] with y
    simp [complexLogDigitObservable, Real.norm_eq_abs,
      abs_of_nonneg (logDigitObservable_nonneg y)]

theorem ergodicAverage_complexLogDigit_eq (x : GaussSpace) (n : ℕ) :
    Chapter02.ergodicAverage gaussSystem complexLogDigitObservable (n + 1) x =
      Complex.ofReal ((((n + 1 : ℕ) : ℝ)⁻¹ *
        (Finset.range (n + 1)).sum
          (fun k => Real.log ((gaussPartialQuotients x.1).tail k : ℝ)))) := by
  rw [Chapter02.ergodicAverage, if_neg (by omega : n + 1 ≠ 0)]
  simp only [gaussSystem, complexLogDigitObservable, logDigitObservable,
    gaussPartialQuotients]
  have hsum : ∑ i ∈ Finset.range (n + 1),
      (Real.log (gaussDigit ((gaussMap^[i]) x).1 0 : ℝ) : ℂ) =
      ((∑ i ∈ Finset.range (n + 1),
        Real.log (gaussDigit x.1 i : ℝ) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [← test_orbit_digit x i]
  rw [hsum]
  push_cast
  rfl

theorem geometricMean_formula_ae :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => geometricMeanPartialQuotients
          (gaussPartialQuotients x) (n + 1)) atTop
        (nhds khinchinConstant) := by
  letI : IsProbabilityMeasure gaussMeasure := gaussMeasure_isProbability
  have hmem : MemLp complexLogDigitObservable 1 gaussMeasure :=
    memLp_one_iff_integrable.mpr complexLogDigitObservable_integrable
  have hlim := gauss_ergodicAverage_ae_tendsto complexLogDigitObservable hmem
  filter_upwards [hlim] with x hx
  change Tendsto
      (fun n => Chapter02.ergodicAverage gaussSystem complexLogDigitObservable n x)
      atTop (nhds (∫ y, complexLogDigitObservable y ∂gaussMeasure)) at hx
  have hx' := hx.comp (Filter.tendsto_add_atTop_nat 1)
  have hre := (Complex.continuous_re.tendsto
    (∫ y, complexLogDigitObservable y ∂gaussMeasure)).comp hx'
  have hintRe : (∫ y, complexLogDigitObservable y ∂gaussMeasure).re =
      ∫ y, logDigitObservable y ∂gaussMeasure := by
    change Complex.reCLM (∫ y, complexLogDigitObservable y ∂gaussMeasure) = _
    rw [← Complex.reCLM.integral_comp_comm]
    · apply integral_congr_ae
      filter_upwards [] with y
      rfl
    · exact complexLogDigitObservable_integrable
  have havg : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
        (Finset.range (n + 1)).sum
          (fun k => Real.log ((gaussPartialQuotients x.1).tail k : ℝ)))
      atTop (nhds (∫ y, logDigitObservable y ∂gaussMeasure)) := by
    rw [← hintRe]
    convert hre using 1
    funext n
    simpa only [Function.comp_apply, Complex.ofReal_re] using
      (congrArg Complex.re (ergodicAverage_complexLogDigit_eq x n)).symm
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp havg
  rw [exp_integral_logDigit_eq_khinchinConstant] at hexp
  simpa only [geometricMeanPartialQuotients] using hexp

noncomputable def digitProbability (j : ℕ) : ℝ :=
  (2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
    Real.log (2 + (j : ℝ))) / Real.log 2

noncomputable def weightedDigitProbabilityPartial (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) * digitProbability (i + 1)

theorem weightedLogNumeratorPartial_formula (M : ℕ) :
    (∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
      (2 * Real.log (i + 2 : ℝ) - Real.log (i + 1 : ℝ) -
        Real.log (i + 3 : ℝ))) =
      ((M + 1 : ℕ) : ℝ) * Real.log (M + 1 : ℝ) -
        (M : ℝ) * Real.log (M + 2 : ℝ) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring_nf

theorem weightedDigitProbabilityPartial_formula (M : ℕ) :
    weightedDigitProbabilityPartial M =
      (((M + 1 : ℕ) : ℝ) * Real.log (M + 1 : ℝ) -
        (M : ℝ) * Real.log (M + 2 : ℝ)) / Real.log 2 := by
  dsimp [weightedDigitProbabilityPartial, digitProbability]
  calc
    (∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
        ((2 * Real.log (1 + ((i + 1 : ℕ) : ℝ)) -
          Real.log ((i + 1 : ℕ) : ℝ) -
          Real.log (2 + ((i + 1 : ℕ) : ℝ))) / Real.log 2)) =
        (∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
          (2 * Real.log (1 + ((i + 1 : ℕ) : ℝ)) -
            Real.log ((i + 1 : ℕ) : ℝ) -
            Real.log (2 + ((i + 1 : ℕ) : ℝ)))) / Real.log 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [show (∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
          (2 * Real.log (1 + ((i + 1 : ℕ) : ℝ)) -
            Real.log ((i + 1 : ℕ) : ℝ) -
            Real.log (2 + ((i + 1 : ℕ) : ℝ)))) =
          ((M + 1 : ℕ) : ℝ) * Real.log (M + 1 : ℝ) -
            (M : ℝ) * Real.log (M + 2 : ℝ) by
        convert weightedLogNumeratorPartial_formula M using 1
        all_goals norm_num only [Nat.cast_add, Nat.cast_one]
        all_goals ring_nf]

theorem weightedLogNumeratorPartial_lower (M : ℕ) :
    Real.log (M + 1 : ℝ) - 1 ≤
      ((M + 1 : ℕ) : ℝ) * Real.log (M + 1 : ℝ) -
        (M : ℝ) * Real.log (M + 2 : ℝ) := by
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hM2 : (0 : ℝ) < M + 2 := by positivity
  have hratio : (M + 2 : ℝ) / (M + 1 : ℝ) =
      1 + 1 / (M + 1 : ℝ) := by field_simp; ring
  have hlogratio : Real.log ((M + 2 : ℝ) / (M + 1 : ℝ)) ≤
      1 / (M + 1 : ℝ) := by
    rw [hratio]
    have := Real.log_le_sub_one_of_pos
      (show 0 < 1 + 1 / (M + 1 : ℝ) by positivity)
    linarith
  have hlogdiff : Real.log (M + 2 : ℝ) - Real.log (M + 1 : ℝ) ≤
      1 / (M + 1 : ℝ) := by
    rw [← Real.log_div hM2.ne' hM1.ne']
    exact hlogratio
  have hMfrac : (M : ℝ) / (M + 1 : ℝ) ≤ 1 := by
    exact (div_le_one₀ hM1).2 (by
      exact_mod_cast Nat.le_add_right M 1)
  have hmul : (M : ℝ) *
      (Real.log (M + 2 : ℝ) - Real.log (M + 1 : ℝ)) ≤ 1 := by
    calc
      _ ≤ (M : ℝ) * (1 / (M + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogdiff (by positivity)
      _ = (M : ℝ) / (M + 1 : ℝ) := by ring
      _ ≤ 1 := hMfrac
  norm_num only [Nat.cast_add, Nat.cast_one] at ⊢
  linarith

theorem weightedDigitProbabilityPartial_tendsto_atTop :
    Tendsto weightedDigitProbabilityPartial atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hlog := Real.tendsto_log_atTop.comp hcast
  filter_upwards [(tendsto_atTop.1 hlog (b * Real.log 2 + 1))] with M hM
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hM
  rw [weightedDigitProbabilityPartial_formula]
  apply (le_div_iff₀ hlog2).2
  exact le_trans (by linarith) (weightedLogNumeratorPartial_lower M)

theorem weighted_indicator_sum_le (M d : ℕ) :
    (∑ i ∈ Finset.range M,
      if d = i + 1 then ((i + 1 : ℕ) : ℝ) else 0) ≤ (d : ℝ) := by
  by_cases hd : d = 0
  · subst d
    simp
  by_cases hm : d - 1 ∈ Finset.range M
  · rw [Finset.sum_eq_single (d - 1)]
    · simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]
    · intro b hb hne
      split_ifs with h
      · omega
      · rfl
    · exact fun h => (h hm).elim
  · have hzero : ∀ i ∈ Finset.range M,
        (if d = i + 1 then ((i + 1 : ℕ) : ℝ) else 0) = 0 := by
      intro i hi
      split_ifs with h
      · exfalso
        apply hm
        have : d - 1 = i := by omega
        simpa [this] using hi
      · rfl
    rw [Finset.sum_eq_zero hzero]
    positivity

theorem weightedDigitFrequencies_le_arithmeticMean
    (a : PartialQuotients) (M n : ℕ) :
    (∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
      digitFrequency a (i + 1) (n + 1)) ≤
      (((n + 1 : ℕ) : ℝ)⁻¹ *
        (Finset.range (n + 1)).sum (fun k => (a.tail k : ℝ))) := by
  have hN : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
  calc
    (∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
        digitFrequency a (i + 1) (n + 1)) =
        (((n + 1 : ℕ) : ℝ)⁻¹ *
          ∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
            (((Finset.range (n + 1)).filter
              fun k => a.tail k = i + 1).card : ℝ)) := by
      dsimp [digitFrequency]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    _ ≤ (((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), (a.tail k : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hN
      calc
        (∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
            (((Finset.range (n + 1)).filter
              fun k => a.tail k = i + 1).card : ℝ)) =
            ∑ i ∈ Finset.range M, ∑ k ∈ Finset.range (n + 1),
              if a.tail k = i + 1 then ((i + 1 : ℕ) : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_boole]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs <;> simp
        _ = ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range M,
              if a.tail k = i + 1 then ((i + 1 : ℕ) : ℝ) else 0 := by
          rw [Finset.sum_comm]
        _ ≤ ∑ k ∈ Finset.range (n + 1), (a.tail k : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact weighted_indicator_sum_le M (a.tail k)
    _ = _ := rfl

theorem arithmeticMeanPartialQuotients_diverges_ae :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
          (Finset.range (n + 1)).sum
            (fun k => ((gaussPartialQuotients x).tail k : ℝ)))
        atTop atTop := by
  have hall : ∀ᵐ x ∂gaussMeasure, ∀ i : ℕ,
      Tendsto
        (fun n : ℕ => digitFrequency (gaussPartialQuotients x.1)
          (i + 1) (n + 1)) atTop
        (nhds (digitProbability (i + 1))) := by
    rw [ae_all_iff]
    intro i
    simpa only [digitProbability] using digitFrequency_formula_ae (i + 1) (by omega)
  filter_upwards [hall] with x hx
  rw [tendsto_atTop]
  intro b
  have hlarge := (tendsto_atTop.1 weightedDigitProbabilityPartial_tendsto_atTop)
    (b + 1)
  obtain ⟨M, hM⟩ := hlarge.exists
  have hsum : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
        digitFrequency (gaussPartialQuotients x.1) (i + 1) (n + 1))
      atTop (nhds (weightedDigitProbabilityPartial M)) := by
    dsimp [weightedDigitProbabilityPartial]
    apply tendsto_finset_sum
    intro i hi
    exact tendsto_const_nhds.mul (hx i)
  have hevent : ∀ᶠ n : ℕ in atTop,
      b ≤ ∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) *
        digitFrequency (gaussPartialQuotients x.1) (i + 1) (n + 1) := by
    have hb : b < weightedDigitProbabilityPartial M := by linarith
    exact (tendsto_order.1 hsum).1 b hb |>.mono (fun n hn => hn.le)
  filter_upwards [hevent] with n hn
  exact hn.trans (weightedDigitFrequencies_le_arithmeticMean
    (gaussPartialQuotients x.1) M n)

noncomputable def metricGaussOrbit (x : ℝ) (n : ℕ) : ℝ := (gaussMapReal^[n]) x

theorem metricGaussOrbit_mem (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    metricGaussOrbit x n ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simpa [metricGaussOrbit] using hx
  | succ n ih =>
      simpa [metricGaussOrbit, Function.iterate_succ_apply'] using
        gaussMapReal_mem_gaussSpace (metricGaussOrbit x n)

theorem metricGaussOrbit_irrational (x : ℝ) (hx : Irrational x) (n : ℕ) :
    Irrational (metricGaussOrbit x n) := by
  induction n with
  | zero => simpa [metricGaussOrbit] using hx
  | succ n ih =>
      rw [metricGaussOrbit, Function.iterate_succ_apply']
      exact (ih.inv).sub_intCast _

theorem metricGaussOrbit_pos_lt_one (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) : metricGaussOrbit x n ∈ Set.Ioo (0 : ℝ) 1 := by
  have h := metricGaussOrbit_mem x hx n
  have hi := metricGaussOrbit_irrational x hirr n
  exact ⟨lt_of_le_of_ne h.1 (by
      intro hz
      exact hi ⟨0, by
        convert hz using 1
        norm_num only⟩),
    lt_of_le_of_ne h.2 (by
      intro ho
      exact hi ⟨1, by
        convert ho.symm using 1
        norm_num only⟩)⟩

theorem metricGaussOrbit_inv_recurrence (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) :
    (metricGaussOrbit x n)⁻¹ =
      (gaussDigit x n : ℝ) + metricGaussOrbit x (n + 1) := by
  have hpos := (metricGaussOrbit_pos_lt_one x hx hirr n).1
  have hfloorNonneg : 0 ≤ Int.floor (metricGaussOrbit x n)⁻¹ :=
    Int.floor_nonneg.mpr (inv_nonneg.mpr hpos.le)
  have hdigit : (gaussDigit x n : ℝ) =
      (Int.floor (metricGaussOrbit x n)⁻¹ : ℝ) := by
    dsimp [gaussDigit, metricGaussOrbit]
    exact_mod_cast Int.toNat_of_nonneg hfloorNonneg
  have hs : metricGaussOrbit x (n + 1) = gaussMapReal (metricGaussOrbit x n) := by
    simp [metricGaussOrbit, Function.iterate_succ_apply']
  rw [hs, gaussMapReal, hdigit]
  ring

theorem gaussConvergentDenominator_product_identity
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational x) (n : ℕ) :
    ((∏ k ∈ Finset.range (n + 1), metricGaussOrbit x k)⁻¹) =
      (convergentDenominator (gaussPartialQuotients x) (n + 1) : ℝ) +
        (convergentDenominator (gaussPartialQuotients x) n : ℝ) *
          metricGaussOrbit x (n + 1) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_succ, Finset.prod_range_zero]
      norm_num
      rw [Section01.denominator_succ, Section01.denominator_zero,
        Section01.previousDenominator_zero]
      simp only [partialQuotient, gaussPartialQuotients]
      push_cast
      simpa [metricGaussOrbit] using metricGaussOrbit_inv_recurrence x hx hirr 0
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have horbitNe : metricGaussOrbit x (n + 1) ≠ 0 :=
        (metricGaussOrbit_pos_lt_one x hx hirr (n + 1)).1.ne'
      have hcancel : metricGaussOrbit x (n + 1) *
          ((gaussDigit x (n + 1) : ℝ) + metricGaussOrbit x (n + 2)) = 1 := by
        rw [← metricGaussOrbit_inv_recurrence x hx hirr (n + 1)]
        exact mul_inv_cancel₀ horbitNe
      rw [show ((∏ k ∈ Finset.range (n + 1), metricGaussOrbit x k) *
          metricGaussOrbit x (n + 1))⁻¹ =
          (∏ k ∈ Finset.range (n + 1), metricGaussOrbit x k)⁻¹ *
            (metricGaussOrbit x (n + 1))⁻¹ by
        rw [mul_inv]]
      rw [ih, metricGaussOrbit_inv_recurrence x hx hirr (n + 1)]
      rw [Section01.denominator_succ (gaussPartialQuotients x) (n + 1),
        Section01.previousDenominator_succ (gaussPartialQuotients x) n]
      simp only [partialQuotient, gaussPartialQuotients]
      push_cast
      rw [show n + 1 + 1 = n + 2 by omega]
      linear_combination
        (convergentDenominator
          ({ a₀ := 0, tail := gaussDigit x } : PartialQuotients) n : ℝ) * hcancel

end Chapter03
