import Chapter01.Common

noncomputable section

open Classical
open scoped BigOperators

namespace Chapter01

noncomputable def circleIcoRepresentative (y : AddCircle (1 : ℝ)) : ℝ :=
  AddCircle.measurableEquivIoc 1 0 y

noncomputable def circleBinaryDigits (y : AddCircle (1 : ℝ)) :
    OneSidedSymbolicSpace 2 := fun n =>
  if 1 / 2 < circleIcoRepresentative (circleTimes (2 ^ n) y) then 1 else 0

theorem circleIcoRepresentative_mem (y : AddCircle (1 : ℝ)) :
    circleIcoRepresentative y ∈ Set.Ioc (0 : ℝ) 1 := by
  simpa [circleIcoRepresentative] using
    (AddCircle.measurableEquivIoc 1 0 y).property

theorem circleIcoRepresentative_measurable :
    Measurable circleIcoRepresentative := by
  exact (AddCircle.measurableEquivIoc 1 0).measurable.subtype_val

theorem circleBinaryDigits_measurable : Measurable circleBinaryDigits := by
  apply measurable_pi_lambda
  intro n
  unfold circleBinaryDigits
  have hc : Measurable (circleTimes (2 ^ n)) := by
    unfold circleTimes
    fun_prop
  have hf : Measurable (fun y : AddCircle (1 : ℝ) =>
      circleIcoRepresentative (circleTimes (2 ^ n) y)) := by
    exact circleIcoRepresentative_measurable.comp hc
  apply Measurable.ite
  · exact hf measurableSet_Ioi
  · exact measurable_const
  · exact measurable_const

theorem circleBinaryDigits_dynamics (y : AddCircle (1 : ℝ)) (n : ℕ) :
    circleBinaryDigits (circleTimes 2 y) n = circleBinaryDigits y (n + 1) := by
  unfold circleBinaryDigits circleTimes
  congr 1
  rw [pow_succ, mul_comm (2 ^ n) 2]
  simp [mul_nsmul]

theorem circleIcoRepresentative_coe (y : AddCircle (1 : ℝ)) :
    ((circleIcoRepresentative y : ℝ) : AddCircle (1 : ℝ)) = y := by
  let q := AddCircle.measurableEquivIoc 1 0
  change q.symm (q y) = y
  exact q.symm_apply_apply y

theorem circleIcoRepresentative_double (y : AddCircle (1 : ℝ)) :
    circleIcoRepresentative (circleTimes 2 y) =
      if circleIcoRepresentative y ≤ 1 / 2 then
        2 * circleIcoRepresentative y
      else 2 * circleIcoRepresentative y - 1 := by
  let r := circleIcoRepresentative y
  have hr := circleIcoRepresentative_mem y
  rcases hr with ⟨hr0, hr1⟩
  by_cases h : r ≤ 1 / 2
  · rw [if_pos h]
    let z : Set.Ioc (0 : ℝ) (0 + 1) := ⟨2 * r, by
      constructor <;> dsimp [r] at * <;> linarith⟩
    have hz : AddCircle.measurableEquivIoc 1 0 (circleTimes 2 y) = z := by
      apply (AddCircle.measurableEquivIoc 1 0).symm.injective
      rw [(AddCircle.measurableEquivIoc 1 0).symm_apply_apply]
      change circleTimes 2 y = (((2 * r : ℝ) : AddCircle (1 : ℝ)))
      symm
      rw [show (2 * r : ℝ) = r + r by ring]
      change ((r : AddCircle (1 : ℝ)) + (r : AddCircle (1 : ℝ))) = _
      rw [← two_nsmul]
      dsimp [r]
      rw [circleIcoRepresentative_coe]
      rfl
    exact congrArg Subtype.val hz
  · rw [if_neg h]
    let z : Set.Ioc (0 : ℝ) (0 + 1) := ⟨2 * r - 1, by
      constructor <;> dsimp [r] at * <;> linarith⟩
    have hz : AddCircle.measurableEquivIoc 1 0 (circleTimes 2 y) = z := by
      apply (AddCircle.measurableEquivIoc 1 0).symm.injective
      rw [(AddCircle.measurableEquivIoc 1 0).symm_apply_apply]
      change circleTimes 2 y = (((2 * r - 1 : ℝ) : AddCircle (1 : ℝ)))
      symm
      change (((2 * r : ℝ) : AddCircle (1 : ℝ)) -
        (((1 : ℝ) : AddCircle (1 : ℝ)))) = _
      rw [show (((1 : ℝ) : AddCircle (1 : ℝ))) = 0 by simp, sub_zero]
      rw [show (2 * r : ℝ) = r + r by ring]
      change ((r : AddCircle (1 : ℝ)) + (r : AddCircle (1 : ℝ))) = _
      rw [← two_nsmul]
      dsimp [r]
      rw [circleIcoRepresentative_coe]
      rfl
    exact congrArg Subtype.val hz

theorem circleOrbit_succ (y : AddCircle (1 : ℝ)) (n : ℕ) :
    circleTimes 2 (circleTimes (2 ^ n) y) = circleTimes (2 ^ (n + 1)) y := by
  unfold circleTimes
  rw [← mul_nsmul, pow_succ, mul_comm (2 ^ n) 2]

theorem circleBinaryDigits_recurrence (y : AddCircle (1 : ℝ)) (n : ℕ) :
    circleIcoRepresentative (circleTimes (2 ^ n) y) =
      ((circleBinaryDigits y n).val : ℝ) / 2 +
        circleIcoRepresentative (circleTimes (2 ^ (n + 1)) y) / 2 := by
  let z := circleTimes (2 ^ n) y
  have hdouble := circleIcoRepresentative_double z
  rw [← circleOrbit_succ y n]
  change circleIcoRepresentative z =
    ((if 1 / 2 < circleIcoRepresentative z then (1 : Fin 2) else 0).val : ℝ) / 2 +
      circleIcoRepresentative (circleTimes 2 z) / 2
  by_cases h : circleIcoRepresentative z ≤ 1 / 2
  · rw [if_pos h] at hdouble
    have hnlt : ¬1 / 2 < circleIcoRepresentative z := not_lt.mpr h
    rw [if_neg hnlt]
    norm_num
    linarith
  · rw [if_neg h] at hdouble
    have hlt : 1 / 2 < circleIcoRepresentative z := lt_of_not_ge h
    rw [if_pos hlt]
    norm_num
    linarith

theorem circleBinaryDigits_partial_sum (y : AddCircle (1 : ℝ)) (n : ℕ) :
    circleIcoRepresentative y =
      (∑ i ∈ Finset.range n,
        ((circleBinaryDigits y i).val : ℝ) / (2 : ℝ) ^ (i + 1)) +
      circleIcoRepresentative (circleTimes (2 ^ n) y) / (2 : ℝ) ^ n := by
  induction n with
  | zero => simp [circleTimes]
  | succ n ih =>
      rw [ih, Finset.sum_range_succ, circleBinaryDigits_recurrence y n]
      field_simp
      ring

theorem circleBinaryDigits_hasSum (y : AddCircle (1 : ℝ)) :
    HasSum (fun i : ℕ =>
      ((circleBinaryDigits y i).val : ℝ) / (2 : ℝ) ^ (i + 1))
      (circleIcoRepresentative y) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun i => by positivity) _).2
  let rem : ℕ → ℝ := fun n =>
    circleIcoRepresentative (circleTimes (2 ^ n) y) / (2 : ℝ) ^ n
  have hrem : Filter.Tendsto rem Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards with n
      exact div_nonneg (le_of_lt (circleIcoRepresentative_mem _).1) (by positivity)
    · filter_upwards with n
      have hrle : circleIcoRepresentative (circleTimes (2 ^ n) y) ≤ 1 :=
        (circleIcoRepresentative_mem _).2
      calc
        rem n ≤ 1 / (2 : ℝ) ^ n :=
          div_le_div_of_nonneg_right hrle (by positivity)
        _ = (1 / 2 : ℝ) ^ n := by rw [one_div_pow]
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq : (fun n : ℕ => ∑ i ∈ Finset.range n,
      ((circleBinaryDigits y i).val : ℝ) / (2 : ℝ) ^ (i + 1)) =
      fun n => circleIcoRepresentative y - rem n := by
    funext n
    dsimp [rem]
    linarith [circleBinaryDigits_partial_sum y n]
  rw [heq]
  convert tendsto_const_nhds.sub hrem using 1 <;> simp

theorem binaryCoding_circleBinaryDigits (y : AddCircle (1 : ℝ)) :
    binaryCoding (circleBinaryDigits y) = y := by
  let q : ℝ →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples 1)
  have hmap := (circleBinaryDigits_hasSum y).map q (AddCircle.continuous_mk' 1)
  unfold binaryCoding
  change (∑' n : ℕ, q
    (((circleBinaryDigits y n).val : ℝ) / (2 : ℝ) ^ (n + 1))) = y
  calc
    _ = q (circleIcoRepresentative y) := by
      simpa [Function.comp_def] using hmap.tsum_eq
    _ = y := circleIcoRepresentative_coe y

theorem binarySeries_summable_probe (x : OneSidedSymbolicSpace 2) :
    Summable (fun n : ℕ => ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  apply (summable_geometric_two.comp_injective Nat.succ_injective).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hx : ((x n).val : ℝ) ≤ 1 := by
    exact_mod_cast (Nat.le_of_lt_succ (x n).isLt)
  have hden : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  calc
    ((x n).val : ℝ) / 2 ^ (n + 1) ≤ 1 / 2 ^ (n + 1) :=
      (div_le_div_iff_of_pos_right hden).2 hx
    _ = (1 / 2 : ℝ) ^ (n + 1) := by norm_num [div_pow]

theorem binaryCoding_eq_real_tsum_probe (x : OneSidedSymbolicSpace 2) :
    binaryCoding x =
      (((∑' n : ℕ, ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)) : ℝ) :
        AddCircle (1 : ℝ)) := by
  let q : ℝ →+ AddCircle (1 : ℝ) :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples 1)
  have hmap := (binarySeries_summable_probe x).hasSum.map q
    (AddCircle.continuous_mk' 1)
  unfold binaryCoding
  change (∑' n : ℕ, q (((x n).val : ℝ) / (2 : ℝ) ^ (n + 1))) = _
  simpa [Function.comp_def] using hmap.tsum_eq

theorem binaryRealTsum_continuous :
    Continuous (fun x : OneSidedSymbolicSpace 2 =>
      ∑' n : ℕ, ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  apply continuous_tsum
  · intro n
    fun_prop
  · exact summable_geometric_two.comp_injective Nat.succ_injective
  · intro n x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hx : ((x n).val : ℝ) ≤ 1 := by
      exact_mod_cast (Nat.le_of_lt_succ (x n).isLt)
    have hden : 0 < (2 : ℝ) ^ (n + 1) := by positivity
    calc
      ((x n).val : ℝ) / 2 ^ (n + 1) ≤ 1 / 2 ^ (n + 1) :=
        (div_le_div_iff_of_pos_right hden).2 hx
      _ = ((fun m : ℕ => (1 / 2 : ℝ) ^ m) ∘ Nat.succ) n := by
        simp [Function.comp_def, div_pow]

theorem binaryCoding_continuous : Continuous binaryCoding := by
  rw [show binaryCoding = fun x =>
      (((∑' n : ℕ, ((x n).val : ℝ) / (2 : ℝ) ^ (n + 1)) : ℝ) :
        AddCircle (1 : ℝ)) by
    funext x
    exact binaryCoding_eq_real_tsum_probe x]
  exact (AddCircle.continuous_mk' 1).comp binaryRealTsum_continuous

def binaryPrefixNat (x : OneSidedSymbolicSpace 2) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * binaryPrefixNat x n + (x n).val

theorem binaryPrefixNat_lt_pow_two (x : OneSidedSymbolicSpace 2) (n : ℕ) :
    binaryPrefixNat x n < 2 ^ n := by
  induction n with
  | zero => simp [binaryPrefixNat]
  | succ n ih =>
      have hd := (x n).isLt
      simp only [binaryPrefixNat, pow_succ]
      omega

theorem binaryPrefixNat_real (x : OneSidedSymbolicSpace 2) (n : ℕ) :
    (binaryPrefixNat x n : ℝ) / (2 : ℝ) ^ n =
      ∑ i ∈ Finset.range n, ((x i).val : ℝ) / (2 : ℝ) ^ (i + 1) := by
  induction n with
  | zero => simp [binaryPrefixNat]
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [binaryPrefixNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      field_simp

theorem binaryPrefixNat_congr {x z : OneSidedSymbolicSpace 2} {n : ℕ}
    (h : ∀ i < n, x i = z i) : binaryPrefixNat x n = binaryPrefixNat z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [binaryPrefixNat]
      rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem binaryPrefixNat_injective {x z : OneSidedSymbolicSpace 2} {n : ℕ}
    (h : binaryPrefixNat x n = binaryPrefixNat z n) :
    ∀ i < n, x i = z i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have heq : 2 * binaryPrefixNat x n + (x n).val =
          2 * binaryPrefixNat z n + (z n).val := by
        simpa only [binaryPrefixNat] using h
      have hxlt := (x n).isLt
      have hzlt := (z n).isLt
      have hd : (x n).val = (z n).val := by omega
      have hp : binaryPrefixNat x n = binaryPrefixNat z n := by omega
      intro i hi
      by_cases hin : i = n
      · subst i
        exact Fin.ext hd
      · exact ih hp i (by omega)

theorem circleBinaryDigits_interval (y : AddCircle (1 : ℝ)) (n : ℕ) :
    circleIcoRepresentative y ∈ Set.Ioc
      ((binaryPrefixNat (circleBinaryDigits y) n : ℝ) / (2 : ℝ) ^ n)
      (((binaryPrefixNat (circleBinaryDigits y) n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
  have hp := binaryPrefixNat_real (circleBinaryDigits y) n
  have hsum := circleBinaryDigits_partial_sum y n
  have hr := circleIcoRepresentative_mem (circleTimes (2 ^ n) y)
  constructor
  · rw [hp, hsum]
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    exact lt_add_of_pos_right _ (div_pos hr.1 hpow)
  · rw [hsum, ← hp]
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    have hle := div_le_div_of_nonneg_right hr.2 (le_of_lt hpow)
    rw [show (((binaryPrefixNat (circleBinaryDigits y) n + 1 : ℕ) : ℝ) /
          (2 : ℝ) ^ n) =
        (binaryPrefixNat (circleBinaryDigits y) n : ℝ) / (2 : ℝ) ^ n +
          1 / (2 : ℝ) ^ n by
      push_cast
      ring]
    simpa [add_comm] using
      add_le_add_left hle
        ((binaryPrefixNat (circleBinaryDigits y) n : ℝ) / (2 : ℝ) ^ n)

theorem circleBinaryCylinder_preimage (x : OneSidedSymbolicSpace 2) (n : ℕ) :
    circleBinaryDigits ⁻¹' PiNat.cylinder x n =
      circleIcoRepresentative ⁻¹' Set.Ioc
        ((binaryPrefixNat x n : ℝ) / (2 : ℝ) ^ n)
        (((binaryPrefixNat x n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
  ext y
  simp only [Set.mem_preimage, PiNat.cylinder]
  constructor
  · intro h
    have hp := binaryPrefixNat_congr h
    simpa [hp] using circleBinaryDigits_interval y n
  · intro hy
    have hz := circleBinaryDigits_interval y n
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    have hp : binaryPrefixNat (circleBinaryDigits y) n = binaryPrefixNat x n := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hint : binaryPrefixNat (circleBinaryDigits y) n + 1 ≤ binaryPrefixNat x n := by
          omega
        have hint' :
            (((binaryPrefixNat (circleBinaryDigits y) n + 1 : ℕ) : ℝ) /
                (2 : ℝ) ^ n) ≤
              (binaryPrefixNat x n : ℝ) / (2 : ℝ) ^ n := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hint) (le_of_lt hpow)
        linarith [hz.2, hy.1]
      · have hint : binaryPrefixNat x n + 1 ≤ binaryPrefixNat (circleBinaryDigits y) n := by
          omega
        have hint' :
            (((binaryPrefixNat x n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) ≤
              (binaryPrefixNat (circleBinaryDigits y) n : ℝ) / (2 : ℝ) ^ n := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hint) (le_of_lt hpow)
        linarith [hy.2, hz.1]
    exact binaryPrefixNat_injective hp

theorem circleBinaryCylinder_measure (x : OneSidedSymbolicSpace 2) (n : ℕ) :
    AddCircle.haarAddCircle (circleBinaryDigits ⁻¹' PiNat.cylinder x n) =
      (2 : ENNReal)⁻¹ ^ n := by
  rw [circleBinaryCylinder_preimage]
  let a : ℝ := (binaryPrefixNat x n : ℝ) / (2 : ℝ) ^ n
  let b : ℝ := ((binaryPrefixNat x n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
  let q : AddCircle (1 : ℝ) ≃ᵐ Set.Ioc (0 : ℝ) (0 + 1) :=
    AddCircle.measurableEquivIoc 1 0
  let s : Set (Set.Ioc (0 : ℝ) (0 + 1)) :=
    Subtype.val ⁻¹' Set.Ioc a b
  have hs : MeasurableSet s := by
    exact measurableSet_Ioc.preimage measurable_subtype_coe
  have hvol :
      (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
        AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hq : MeasureTheory.MeasurePreserving q AddCircle.haarAddCircle
      (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) := by
    rw [← hvol]
    simpa [q] using (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
  have hpre : circleIcoRepresentative ⁻¹' Set.Ioc a b = q ⁻¹' s := by
    rfl
  rw [show circleIcoRepresentative ⁻¹' Set.Ioc
      ((binaryPrefixNat x n : ℝ) / (2 : ℝ) ^ n)
      (((binaryPrefixNat x n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) =
      circleIcoRepresentative ⁻¹' Set.Ioc a b by rfl, hpre,
    hq.measure_preimage hs.nullMeasurableSet]
  rw [MeasureTheory.Measure.comap_apply Subtype.val Subtype.val_injective
    (fun t ht => measurableSet_Ioc.subtype_image ht) MeasureTheory.volume hs]
  have ha : 0 ≤ a := by
    exact div_nonneg (by positivity) (by positivity)
  have hb : b ≤ 1 := by
    have hp := binaryPrefixNat_lt_pow_two x n
    have hnat : binaryPrefixNat x n + 1 ≤ 2 ^ n := by
      omega
    have hreal : ((binaryPrefixNat x n + 1 : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hnat
    dsimp [b]
    calc
      ((binaryPrefixNat x n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n ≤
          ((2 ^ n : ℕ) : ℝ) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_right hreal (by positivity)
      _ = 1 := by norm_num
  have himage : Subtype.val '' s = Set.Ioc a b := by
    ext r
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hr
      refine ⟨⟨r, ?_⟩, hr, rfl⟩
      exact ⟨lt_of_le_of_lt ha hr.1, by simpa using le_trans hr.2 hb⟩
  rw [himage, Real.volume_Ioc]
  have hdiff : b - a = 1 / (2 : ℝ) ^ n := by
    dsimp [a, b]
    push_cast
    ring
  rw [hdiff, ← one_div_pow]
  calc
    ENNReal.ofReal ((1 / 2 : ℝ) ^ n) =
        ENNReal.ofReal (1 / 2 : ℝ) ^ n := by
      exact ENNReal.ofReal_pow (p := (1 / 2 : ℝ)) (by norm_num) n
    _ = (2 : ENNReal)⁻¹ ^ n := by
      congr 1
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num [div_eq_mul_inv]

end Chapter01
