import Chapter03.ContinuedFractions.DigitFrequency
import Mathlib.NumberTheory.ZetaValues

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter03

theorem intervalIntegral_negLog_mul_pow (m : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, (-Real.log x) * x ^ m) =
      1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
  let F : ℝ → ℝ := fun x =>
    -(x ^ (m + 1) * Real.log x) / (m + 1 : ℝ) +
      x ^ (m + 1) / (m + 1 : ℝ) ^ 2
  have hcontMul : Continuous fun x : ℝ => x ^ (m + 1) * Real.log x := by
    simpa [pow_succ, mul_assoc] using
      (continuous_pow m).mul Real.continuous_mul_log
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivWithinAt F ((-Real.log x) * x ^ m) (Set.Ioi x) x := by
    intro x hx
    norm_num only [min_eq_left, max_eq_right] at hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hp := (hasDerivAt_pow (m + 1) x).mul (Real.hasDerivAt_log hx0)
    have hq := hasDerivAt_pow (m + 1) x
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hp hq
    apply HasDerivAt.hasDerivWithinAt
    dsimp [F]
    convert hp.neg.div_const (m + 1 : ℝ) |>.add
      (hq.div_const ((m + 1 : ℝ) ^ 2)) using 1
    all_goals field_simp
    all_goals ring
  have hlogInterval : IntervalIntegrable Real.log volume (0 : ℝ) 1 := by
    apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
    rw [integral_log]
    norm_num only [Real.log_one, Real.log_zero, one_mul, zero_mul, sub_zero,
      zero_sub, add_zero, neg_ne_zero, one_ne_zero]
  have hint : IntervalIntegrable (fun x : ℝ => (-Real.log x) * x ^ m)
      volume (0 : ℝ) 1 :=
    hlogInterval.neg.mul_continuousOn (continuous_pow m).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont.continuousOn hderiv hint]
  dsimp [F]
  simp [Real.log_zero, Nat.cast_add, Nat.cast_one]

theorem hasSum_alternating_zeta_pairs :
    HasSum (fun k : ℕ =>
      1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 -
        1 / ((2 * k + 2 : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 12) := by
  let f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hall : HasSum f (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have heven : HasSum (fun k => f (2 * k)) (Real.pi ^ 2 / 24) := by
    convert hasSum_zeta_two.mul_left (1 / 4 : ℝ) using 1
    · ext k
      dsimp [f]
      push_cast
      simp only [div_eq_mul_inv, one_mul, mul_pow, mul_inv_rev]
      norm_num only
      ring
    · ring
  have hoddSummable : Summable fun k => f (2 * k + 1) := by
    have hshift : Summable fun k => f (k + 1) :=
      (summable_nat_add_iff 1).2 hall.summable
    apply Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => ?_) hshift
    dsimp [f]
    gcongr
    omega
  have hsplit := tsum_even_add_odd heven.summable hoddSummable
  have hodd : HasSum (fun k => f (2 * k + 1)) (Real.pi ^ 2 / 8) := by
    convert hoddSummable.hasSum using 1
    rw [hall.tsum_eq] at hsplit
    rw [heven.tsum_eq] at hsplit
    linarith
  have hevenShift : HasSum (fun k => f (2 * k + 2)) (Real.pi ^ 2 / 24) := by
    let feven : ℕ → ℝ := fun k => f (2 * k)
    have hshift : HasSum (fun k => feven (k + 1)) (Real.pi ^ 2 / 24) := by
      simpa [feven, f] using
        ((hasSum_nat_add_iff' (f := feven) 1).2 heven)
    convert hshift using 1
  convert hodd.sub hevenShift using 1
  ring

noncomputable def levySeriesTerm (k : ℕ) (x : ℝ) : ℝ :=
  (-Real.log x) * (x ^ (2 * k) - x ^ (2 * k + 1))

theorem intervalIntegral_levySeriesTerm (k : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, levySeriesTerm k x) =
      1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 -
        1 / ((2 * k + 2 : ℕ) : ℝ) ^ 2 := by
  have hlogInterval : IntervalIntegrable Real.log volume (0 : ℝ) 1 := by
    apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
    rw [integral_log]
    norm_num only [Real.log_one, Real.log_zero, one_mul, zero_mul, sub_zero,
      zero_sub, add_zero, neg_ne_zero, one_ne_zero]
  have hint (m : ℕ) : IntervalIntegrable
      (fun x : ℝ => (-Real.log x) * x ^ m) volume (0 : ℝ) 1 :=
    hlogInterval.neg.mul_continuousOn (continuous_pow m).continuousOn
  rw [show levySeriesTerm k = fun x : ℝ =>
      (-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1) by
    funext x
    dsimp [levySeriesTerm]
    ring]
  rw [intervalIntegral.integral_sub (hint (2 * k)) (hint (2 * k + 1)),
    intervalIntegral_negLog_mul_pow, intervalIntegral_negLog_mul_pow]

theorem tsum_levySeriesTerm (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑' k : ℕ, levySeriesTerm k x = (-Real.log x) / (1 + x) := by
  rcases eq_or_lt_of_le hx1 with rfl | hx1
  · simp [levySeriesTerm]
  have habs : ‖x ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    nlinarith
  have hgeom := hasSum_geometric_of_norm_lt_one habs
  have hmul := hgeom.mul_left ((-Real.log x) * (1 - x))
  have hseries : HasSum (fun k : ℕ => levySeriesTerm k x)
      ((-Real.log x) * (1 - x) * (1 - x ^ 2)⁻¹) := by
    convert hmul using 1
    funext k
    dsimp [levySeriesTerm]
    rw [pow_mul]
    ring
  rw [hseries.tsum_eq]
  have hne : 1 + x ≠ 0 := by linarith
  have hne' : 1 - x ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

theorem intervalIntegral_negLog_div_one_add :
    (∫ x : ℝ in (0 : ℝ)..1, (-Real.log x) / (1 + x)) =
      Real.pi ^ 2 / 12 := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hlogInterval : IntervalIntegrable Real.log volume (0 : ℝ) 1 := by
    apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
    rw [integral_log]
    norm_num only [Real.log_one, Real.log_zero, one_mul, zero_mul, sub_zero,
      zero_sub, add_zero, neg_ne_zero, one_ne_zero]
  have htermInt (k : ℕ) : Integrable (levySeriesTerm k) μ := by
    rw [show levySeriesTerm k = fun x : ℝ =>
        (-Real.log x) * x ^ (2 * k) - (-Real.log x) * x ^ (2 * k + 1) by
      funext x
      dsimp [levySeriesTerm]
      ring]
    apply Integrable.sub
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        (hlogInterval.neg.mul_continuousOn (continuous_pow (2 * k)).continuousOn)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
        (hlogInterval.neg.mul_continuousOn
          (continuous_pow (2 * k + 1)).continuousOn)
  have htermNonneg (k : ℕ) : ∀ᵐ x ∂μ, 0 ≤ levySeriesTerm k x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hlog : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)
    have hpow : x ^ (2 * k + 1) ≤ x ^ (2 * k) := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hx.1.le _) hx.2
    exact mul_nonneg hlog (sub_nonneg.mpr hpow)
  have hnormIntegral (k : ℕ) :
      ∫ x, ‖levySeriesTerm k x‖ ∂μ =
        1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 -
          1 / ((2 * k + 2 : ℕ) : ℝ) ^ 2 := by
    calc
      ∫ x, ‖levySeriesTerm k x‖ ∂μ = ∫ x, levySeriesTerm k x ∂μ := by
        apply integral_congr_ae
        filter_upwards [htermNonneg k] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx]
      _ = ∫ x : ℝ in (0 : ℝ)..1, levySeriesTerm k x := by
        rw [intervalIntegral.integral_of_le (by norm_num)]
      _ = _ := intervalIntegral_levySeriesTerm k
  have hsumNorm : Summable fun k : ℕ => ∫ x, ‖levySeriesTerm k x‖ ∂μ := by
    simpa only [hnormIntegral] using hasSum_alternating_zeta_pairs.summable
  have hinterchange := MeasureTheory.integral_tsum_of_summable_integral_norm
    htermInt hsumNorm
  have hpoint : ∀ᵐ x ∂μ,
      ∑' k : ℕ, levySeriesTerm k x = (-Real.log x) / (1 + x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact tsum_levySeriesTerm x hx.1.le hx.2
  have hintegralPoint :
      (∫ x, ∑' k : ℕ, levySeriesTerm k x ∂μ) =
        ∫ x, (-Real.log x) / (1 + x) ∂μ := integral_congr_ae hpoint
  rw [hintegralPoint] at hinterchange
  have hleft :
      ∑' k : ℕ, ∫ x, levySeriesTerm k x ∂μ = Real.pi ^ 2 / 12 := by
    rw [show (fun k : ℕ => ∫ x, levySeriesTerm k x ∂μ) = fun k =>
        1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 -
          1 / ((2 * k + 2 : ℕ) : ℝ) ^ 2 by
      funext k
      rw [← intervalIntegral.integral_of_le (by norm_num)]
      exact intervalIntegral_levySeriesTerm k]
    exact hasSum_alternating_zeta_pairs.tsum_eq
  rw [hleft] at hinterchange
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact hinterchange.symm

theorem integral_negLogVal_gauss :
    (∫ y : GaussSpace, -Real.log y.1 ∂gaussMeasure) = levyConstant := by
  have hproj : Measurable unitIntervalProjection := by
    apply Measurable.subtype_mk
    fun_prop
  rw [gaussMeasure]
  rw [MeasureTheory.integral_map hproj.aemeasurable
    (show AEStronglyMeasurable (fun y : GaussSpace => -Real.log y.1)
        (Measure.map unitIntervalProjection gaussMeasureOnReal) by
      exact (show Measurable fun y : GaussSpace => -Real.log y.1 by
        fun_prop).aestronglyMeasurable)]
  rw [gaussMeasureOnReal]
  have hdmeas : Measurable fun x : ℝ => ENNReal.ofReal (gaussDensityReal x) := by
    apply Measurable.ennreal_ofReal
    change Measurable fun x : ℝ => (Real.log 2 * (1 + x))⁻¹
    fun_prop
  change (∫ x : ℝ, -Real.log (unitIntervalProjection x).1
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (gaussDensityReal x))) = levyConstant
  rw [integral_withDensity_eq_integral_toReal_smul hdmeas (by simp)]
  have hrewrite : ∀ᵐ x ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      (ENNReal.ofReal (gaussDensityReal x)).toReal •
          (-Real.log (unitIntervalProjection x).1) =
        (Real.log 2)⁻¹ * ((-Real.log x) / (1 + x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hprojx : (unitIntervalProjection x).1 = x := by
      simp [unitIntervalProjection, min_eq_right hx.2, max_eq_right hx.1]
    rw [hprojx, ENNReal.toReal_ofReal]
    · change gaussDensityReal x * (-Real.log x) = _
      dsimp [gaussDensityReal]
      have hlogNe : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      have hxNe : 1 + x ≠ 0 := by linarith [hx.1]
      field_simp [hlogNe, hxNe]
    · dsimp [gaussDensityReal]
      exact inv_nonneg.mpr
        (mul_nonneg (Real.log_pos (by norm_num)).le (by linarith [hx.1]))
  rw [integral_congr_ae hrewrite]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral_negLog_div_one_add]
  dsimp [levyConstant]
  ring

end Chapter03
