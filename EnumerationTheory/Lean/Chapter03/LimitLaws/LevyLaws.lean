import Chapter03.LimitLaws.MetricLaws
import Chapter03.LimitLaws.LevyIntegral

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter03

noncomputable def complexNegLogVal (y : GaussSpace) : ℂ :=
  (negLogVal y : ℂ)

theorem complexNegLogVal_integrable :
    Integrable complexNegLogVal gaussMeasure := by
  apply negLogVal_integrable.mono
  · exact (Complex.continuous_ofReal.measurable.comp
      (show Measurable negLogVal by
        change Measurable fun y : GaussSpace => -Real.log y.1
        fun_prop)).aestronglyMeasurable
  · filter_upwards [] with y
    simp [complexNegLogVal, Real.norm_eq_abs,
      abs_of_nonneg (negLogVal_nonneg y)]

theorem ergodicAverage_complexNegLog_eq (x : GaussSpace) (n : ℕ) :
    Chapter02.ergodicAverage gaussSystem complexNegLogVal (n + 1) x =
      Complex.ofReal ((((n + 1 : ℕ) : ℝ)⁻¹ *
        (Finset.range (n + 1)).sum
          (fun k => -Real.log (metricGaussOrbit x.1 k)))) := by
  rw [Chapter02.ergodicAverage, if_neg (by omega : n + 1 ≠ 0)]
  simp only [gaussSystem, complexNegLogVal, negLogVal]
  have hsum : ∑ i ∈ Finset.range (n + 1),
      ((-Real.log ((gaussMap^[i]) x).1 : ℝ) : ℂ) =
      (((∑ i ∈ Finset.range (n + 1),
        -Real.log (metricGaussOrbit x.1 i) : ℝ)) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [test_orbit_val]
    rfl
  rw [hsum]
  push_cast
  rfl

theorem negLogOrbit_average_ae :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
          (Finset.range (n + 1)).sum
            (fun k => -Real.log (metricGaussOrbit x k)))
        atTop (nhds levyConstant) := by
  letI : IsProbabilityMeasure gaussMeasure := gaussMeasure_isProbability
  have hmem : MemLp complexNegLogVal 1 gaussMeasure :=
    memLp_one_iff_integrable.mpr complexNegLogVal_integrable
  have hlim := gauss_ergodicAverage_ae_tendsto complexNegLogVal hmem
  filter_upwards [hlim] with x hx
  change Tendsto
      (fun n => Chapter02.ergodicAverage gaussSystem complexNegLogVal n x)
      atTop (nhds (∫ y, complexNegLogVal y ∂gaussMeasure)) at hx
  have hx' := hx.comp (Filter.tendsto_add_atTop_nat 1)
  have hre := (Complex.continuous_re.tendsto
    (∫ y, complexNegLogVal y ∂gaussMeasure)).comp hx'
  have hintRe : (∫ y, complexNegLogVal y ∂gaussMeasure).re =
      ∫ y, -Real.log y.1 ∂gaussMeasure := by
    change Complex.reCLM (∫ y, complexNegLogVal y ∂gaussMeasure) = _
    rw [← Complex.reCLM.integral_comp_comm]
    · apply integral_congr_ae
      filter_upwards [] with y
      rfl
    · exact complexNegLogVal_integrable
  rw [hintRe, integral_negLogVal_gauss] at hre
  convert hre using 1
  funext n
  simpa only [Function.comp_apply, Complex.ofReal_re] using
    (congrArg Complex.re (ergodicAverage_complexNegLog_eq x n)).symm

theorem gaussDenominator_monotone (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hirr : Irrational x) (n : ℕ) :
    convergentDenominator (gaussPartialQuotients x) n ≤
      convergentDenominator (gaussPartialQuotients x) (n + 1) := by
  have hreg := (Section01.gaussPartialQuotients_expansion x hx hirr).1
  cases n with
  | zero =>
      rw [Section01.denominator_succ, Section01.denominator_zero,
        Section01.previousDenominator_zero]
      simp only [partialQuotient, gaussPartialQuotients]
      norm_num only [zero_add, mul_one, Nat.cast_one]
      exact_mod_cast hreg 0
  | succ n =>
      exact (Section01.adjacent_denominator_strict
        (gaussPartialQuotients x) hreg (n + 1) (by omega)).le

theorem negLogOrbit_sum_eq_log_product (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational x) (n : ℕ) :
    (Finset.range (n + 1)).sum
        (fun k => -Real.log (metricGaussOrbit x k)) =
      Real.log ((∏ k ∈ Finset.range (n + 1), metricGaussOrbit x k)⁻¹) := by
  rw [Real.log_inv, Real.log_prod]
  · simp only [Finset.sum_neg_distrib]
  · intro k hk
    exact (metricGaussOrbit_pos_lt_one x hx hirr k).1.ne'

theorem denominator_log_gap_bounds (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational x) (n : ℕ) :
    0 ≤ (Finset.range (n + 1)).sum
          (fun k => -Real.log (metricGaussOrbit x k)) -
        Real.log (convergentDenominator
          (gaussPartialQuotients x) (n + 1) : ℝ) ∧
      (Finset.range (n + 1)).sum
          (fun k => -Real.log (metricGaussOrbit x k)) -
        Real.log (convergentDenominator
          (gaussPartialQuotients x) (n + 1) : ℝ) ≤ Real.log 2 := by
  let q : ℝ := convergentDenominator
    (gaussPartialQuotients x) (n + 1)
  let p : ℝ := convergentDenominator (gaussPartialQuotients x) n
  let z : ℝ := metricGaussOrbit x (n + 1)
  have hreg := (Section01.gaussPartialQuotients_expansion x hx hirr).1
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Section01.denominator_pos_and_previous_nonneg
      (gaussPartialQuotients x) hreg (n + 1)).1
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast (Section01.denominator_pos_and_previous_nonneg
      (gaussPartialQuotients x) hreg n).1
  have hpq : p ≤ q := by
    dsimp [p, q]
    exact_mod_cast gaussDenominator_monotone x hx hirr n
  have hz := metricGaussOrbit_pos_lt_one x hx hirr (n + 1)
  change z ∈ Set.Ioo (0 : ℝ) 1 at hz
  have hid : ((∏ k ∈ Finset.range (n + 1), metricGaussOrbit x k)⁻¹) =
      q + p * z := by
    simpa [q, p, z] using gaussConvergentDenominator_product_identity x hx hirr n
  rw [negLogOrbit_sum_eq_log_product x hx hirr n, hid]
  have hlower : q ≤ q + p * z := by nlinarith [mul_pos hp hz.1]
  have hpz : p * z ≤ p := mul_le_of_le_one_right hp.le hz.2.le
  have hupper : q + p * z ≤ 2 * q := by linarith
  have hq2 : 0 < 2 * q := by positivity
  have hsumpos : 0 < q + p * z := lt_of_lt_of_le hq hlower
  have hlogLower := Real.log_le_log hq hlower
  have hlogUpper := Real.log_le_log hsumpos hupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq.ne'] at hlogUpper
  constructor <;> linarith

theorem convergentDenominator_growth_ae :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
          Real.log
            (convergentDenominator (gaussPartialQuotients x) (n + 1) : ℝ))
        atTop (nhds levyConstant) := by
  filter_upwards [negLogOrbit_average_ae, ae_gaussMeasure_irrational] with x havg hirr
  have hdenTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hbound : Tendsto (fun n : ℕ => Real.log 2 / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hdenTop
  have hgap : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
        ((Finset.range (n + 1)).sum
            (fun k => -Real.log (metricGaussOrbit x.1 k)) -
          Real.log (convergentDenominator
            (gaussPartialQuotients x.1) (n + 1) : ℝ)))
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (denominator_log_gap_bounds x.1 x.2 hirr n).1
    · intro n
      have hb := (denominator_log_gap_bounds x.1 x.2 hirr n).2
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      calc
        ((n + 1 : ℕ) : ℝ)⁻¹ *
            ((Finset.range (n + 1)).sum
                (fun k => -Real.log (metricGaussOrbit x.1 k)) -
              Real.log (convergentDenominator
                (gaussPartialQuotients x.1) (n + 1) : ℝ))
            ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * Real.log 2 :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hn.le)
        _ = Real.log 2 / ((n + 1 : ℕ) : ℝ) := by
          rw [div_eq_mul_inv]
          ring
    · exact hbound
  have hsub := havg.sub hgap
  convert hsub using 1
  · funext n
    ring
  · simp

end Chapter03
