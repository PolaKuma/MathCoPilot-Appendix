import Chapter03.ContinuedFractions.GaussMeasure
import Chapter03.ContinuedFractions.GaussErgodic

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter03

theorem test_orbit_val (x : GaussSpace) (n : ℕ) :
    ((gaussMap^[n]) x).1 = (gaussMapReal^[n]) x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (gaussMap x)

theorem test_orbit_digit (x : GaussSpace) (n : ℕ) :
    gaussDigit x.1 n = gaussDigit ((gaussMap^[n]) x).1 0 := by
  simp only [gaussDigit, Function.iterate_zero_apply]
  rw [show ((gaussMap^[n]) x).1 = (gaussMapReal^[n]) x.1 by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        exact ih (gaussMap x)]

def testCylinder (j : ℕ) : Set GaussSpace :=
  Subtype.val ⁻¹' Set.Ioc (((j : ℝ) + 1)⁻¹) ((j : ℝ)⁻¹)

theorem testCylinder_measurable (j : ℕ) : MeasurableSet (testCylinder j) := by
  exact measurable_subtype_coe measurableSet_Ioc

theorem test_digit_mem (j : ℕ) (hj : 0 < j) (y : GaussSpace) :
    gaussDigit y.1 0 = j ↔ y ∈ testCylinder j := by
  simp only [gaussDigit, Function.iterate_zero_apply, testCylinder,
    Set.mem_preimage, Set.mem_Ioc]
  have hnonneg : 0 ≤ Int.floor y.1⁻¹ :=
    Int.floor_nonneg.mpr (inv_nonneg.mpr y.2.1)
  rw [show Int.toNat (Int.floor y.1⁻¹) = j ↔ Int.floor y.1⁻¹ = (j : ℤ) by
    constructor
    · intro h
      have hc := Int.toNat_of_nonneg hnonneg
      rw [h] at hc
      exact hc.symm
    · intro h
      rw [h]
      simp]
  rw [Int.floor_eq_iff]
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  constructor
  · intro h
    have hypos : 0 < y.1 := by
      by_contra hn
      have hyzero : y.1 = 0 := le_antisymm (le_of_not_gt hn) y.2.1
      rw [hyzero, inv_zero] at h
      exact (not_le_of_gt hjR) (by exact_mod_cast h.1)
    constructor
    · exact (inv_lt_comm₀ (by positivity : (0 : ℝ) < j + 1) hypos).2 h.2
    · simpa only [inv_inv] using
        (inv_le_inv₀ (inv_pos.mpr hypos) hjR).2 h.1
  · intro h
    have hypos : 0 < y.1 := lt_of_le_of_lt (inv_nonneg.mpr (by positivity)) h.1
    constructor
    · have hr := (inv_le_inv₀ (inv_pos.mpr hypos) hjR).1
          (show (y.1⁻¹)⁻¹ ≤ (j : ℝ)⁻¹ by simpa only [inv_inv] using h.2)
      simpa only [inv_inv] using hr
    · exact (inv_lt_comm₀ (by positivity : (0 : ℝ) < j + 1) hypos).1 h.1

theorem testCylinder_image (j : ℕ) (hj : 0 < j) :
    Subtype.val '' testCylinder j =
      Set.Ioc (((j : ℝ) + 1)⁻¹) ((j : ℝ)⁻¹) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨⟨x, ?_⟩, ?_, rfl⟩
    · constructor
      · exact le_of_lt (lt_of_le_of_lt (inv_nonneg.mpr (by positivity)) hx.1)
      · have hjR : (0 : ℝ) < j := by exact_mod_cast hj
        have hjone : (1 : ℝ) ≤ j := by exact_mod_cast hj
        exact le_trans hx.2 ((inv_le_one₀ hjR).2 hjone)
    · simpa [testCylinder] using hx

theorem testCylinder_measure (j : ℕ) (hj : 0 < j) :
    gaussMeasure (testCylinder j) = ENNReal.ofReal
      ((2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
        Real.log (2 + (j : ℝ))) / Real.log 2) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  let a : ℝ := ((j : ℝ) + 1)⁻¹
  let b : ℝ := (j : ℝ)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact (inv_le_inv₀ (by positivity : (0 : ℝ) < j + 1) hjR).2 (by linarith)
  have hcont : ContinuousOn gaussDensityReal (Set.Icc a b) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx hzero
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hxpos : 0 < 1 + x := by linarith [ha, hx.1]
      nlinarith
  have hint : Integrable gaussDensityReal (volume.restrict (Set.Ioc a b)) := by
    exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] gaussDensityReal := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    dsimp [gaussDensityReal]
    exact inv_nonneg.mpr (mul_nonneg (Real.log_pos (by norm_num)).le
      (by linarith [ha, hx.1]))
  rw [gaussMeasure_apply (show MeasurableSet (testCylinder j) by
    exact measurable_subtype_coe measurableSet_Ioc)]
  rw [show Subtype.val '' testCylinder j = Set.Ioc a b by
    simpa [a, b] using (show Subtype.val '' testCylinder j =
      Set.Ioc (((j : ℝ) + 1)⁻¹) ((j : ℝ)⁻¹) by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          refine ⟨⟨x, ?_⟩, ?_, rfl⟩
          · constructor
            · exact le_of_lt (lt_of_le_of_lt (inv_nonneg.mpr (by positivity)) hx.1)
            · have hjone : (1 : ℝ) ≤ j := by exact_mod_cast hj
              exact le_trans hx.2 ((inv_le_one₀ hjR).2 hjone)
          · simpa [testCylinder] using hx)]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  rw [← intervalIntegral.integral_of_le hab]
  calc
    ∫ x : ℝ in a..b, gaussDensityReal x =
        (Real.log 2)⁻¹ * ∫ x : ℝ in a..b, (1 + x)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp [gaussDensityReal]
      field_simp
    _ = (Real.log 2)⁻¹ * ∫ x : ℝ in (1 + a)..(1 + b), x⁻¹ := by
      rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) 1]
    _ = (Real.log 2)⁻¹ * Real.log ((1 + b) / (1 + a)) := by
      rw [integral_inv_of_pos (by linarith) (by linarith)]
    _ = (2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
        Real.log (2 + (j : ℝ))) / Real.log 2 := by
      dsimp [a, b]
      rw [Real.log_div (by positivity) (by positivity)]
      rw [show 1 + (j : ℝ)⁻¹ = (j + 1) / j by field_simp,
        show 1 + ((j : ℝ) + 1)⁻¹ = (j + 2) / (j + 1) by
          field_simp
          ring]
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (by positivity)]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      ring

theorem testConstant_nonneg (j : ℕ) (hj : 0 < j) :
    0 ≤ (2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
      Real.log (2 + (j : ℝ))) / Real.log 2 := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hden : (0 : ℝ) < j * (j + 2) := by positivity
  have hratio : (1 : ℝ) ≤ ((j + 1) ^ 2) / (j * (j + 2)) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hlog : 0 ≤ Real.log (((j + 1) ^ 2) / (j * (j + 2))) :=
    Real.log_nonneg hratio
  have hform :
      Real.log (((j + 1) ^ 2) / (j * (j + 2))) =
        2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
          Real.log (2 + (j : ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_mul (by positivity) (by positivity)]
    ring
  rw [← hform]
  exact div_nonneg hlog (Real.log_pos (by norm_num)).le

noncomputable def testObservable (j : ℕ) : GaussSpace → ℂ :=
  (testCylinder j).indicator (fun _ => 1)

theorem test_average_eq_frequency (j : ℕ) (hj : 0 < j)
    (x : GaussSpace) (n : ℕ) :
    Chapter02.ergodicAverage gaussSystem (testObservable j) (n + 1) x =
      (digitFrequency (gaussPartialQuotients x.1) j (n + 1) : ℂ) := by
  rw [Chapter02.ergodicAverage, if_neg (by omega : n + 1 ≠ 0)]
  simp only [gaussSystem, digitFrequency, gaussPartialQuotients]
  have hsum :
      ∑ i ∈ Finset.range (n + 1), testObservable j ((gaussMap^[i]) x) =
        (((Finset.range (n + 1)).filter fun k => gaussDigit x.1 k = j).card : ℂ) := by
    calc
      _ = ∑ i ∈ Finset.range (n + 1),
          if gaussDigit x.1 i = j then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hd : gaussDigit x.1 i = j
        · rw [if_pos hd]
          have horbit : gaussDigit ((gaussMap^[i]) x).1 0 = j := by
            rw [← test_orbit_digit x i]
            exact hd
          have hmem := (test_digit_mem j hj ((gaussMap^[i]) x)).1 horbit
          simp [testObservable, Set.indicator_of_mem hmem]
        · rw [if_neg hd]
          have hnotmem : (gaussMap^[i]) x ∉ testCylinder j := by
            intro hm
            apply hd
            rw [test_orbit_digit x i]
            exact (test_digit_mem j hj ((gaussMap^[i]) x)).2 hm
          simp [testObservable, hnotmem]
      _ = _ := Finset.sum_boole (fun k => gaussDigit x.1 k = j) (Finset.range (n + 1))
  rw [hsum]
  push_cast
  rw [div_eq_mul_inv]
  ring

theorem digitFrequency_formula_ae (j : ℕ) (hj : 0 < j) :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => digitFrequency (gaussPartialQuotients x) j (n + 1)) atTop
        (nhds ((2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
          Real.log (2 + (j : ℝ))) / Real.log 2)) := by
  let c : ℝ := (2 * Real.log (1 + (j : ℝ)) - Real.log (j : ℝ) -
    Real.log (2 + (j : ℝ))) / Real.log 2
  let f : GaussSpace → ℂ := testObservable j
  letI : IsProbabilityMeasure gaussMeasure := gaussMeasure_isProbability
  have hf : MemLp f 1 gaussMeasure := by
    apply memLp_indicator_const 1 (testCylinder_measurable j) 1
    right
    exact (lt_of_le_of_lt (measure_mono (Set.subset_univ _))
      (show gaussMeasure Set.univ < ∞ by
        rw [measure_univ]
        norm_num)).ne
  have hlim := gauss_ergodicAverage_ae_tendsto f hf
  filter_upwards [hlim] with x hx
  change Tendsto (fun n => Chapter02.ergodicAverage gaussSystem f n x) atTop
    (nhds (∫ y, f y ∂gaussMeasure)) at hx
  have hmeasure : gaussMeasure.real (testCylinder j) = c := by
    rw [Measure.real_def, testCylinder_measure j hj,
      ENNReal.toReal_ofReal (testConstant_nonneg j hj)]
  have hintegral : (∫ y, f y ∂gaussMeasure) = (c : ℂ) := by
    change (∫ y, (testCylinder j).indicator (fun _ => (1 : ℂ)) y ∂gaussMeasure) = _
    rw [integral_indicator_const (1 : ℂ) (testCylinder_measurable j), hmeasure]
    simp
  have hc : Tendsto
      (fun n : ℕ => (digitFrequency (gaussPartialQuotients x.1) j (n + 1) : ℂ))
      atTop (nhds (c : ℂ)) := by
    have hx' := hx.comp (Filter.tendsto_add_atTop_nat 1)
    rw [hintegral] at hx'
    convert hx' using 1
    funext n
    symm
    simpa [f] using test_average_eq_frequency j hj x n
  have hre := (Complex.continuous_re.tendsto (c : ℂ)).comp hc
  change Tendsto
    (fun n : ℕ => digitFrequency (gaussPartialQuotients x.1) j (n + 1))
    atTop (nhds c)
  simpa only [Function.comp_apply, Complex.ofReal_re] using hre

end Chapter03
