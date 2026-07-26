import Chapter03.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter03
namespace Section01

private def rationalGCF (a : PartialQuotients) : GenContFract ℚ where
  h := a.a₀
  s := Stream'.Seq.ofStream (fun n => ⟨1, a.tail n⟩)

private def rationalSCF (a : PartialQuotients) : SimpContFract ℚ :=
  ⟨rationalGCF a, by
    intro n q hq
    simp [rationalGCF, GenContFract.partNums, Stream'.Seq.map,
      Stream'.Seq.get?, Stream'.Seq.ofStream, Stream'.map, Stream'.get] at hq
    exact hq.symm⟩

private def rationalCF (a : PartialQuotients) (hregular : IsRegularPartialQuotients a) :
    ContFract ℚ :=
  ⟨rationalSCF a, by
    intro n q hq
    simp [rationalSCF, rationalGCF, GenContFract.partDens, Stream'.Seq.map,
      Stream'.Seq.get?, Stream'.Seq.ofStream, Stream'.map, Stream'.get] at hq
    rw [← hq]
    exact_mod_cast hregular n⟩

private theorem matrix_eq_rational_contsAux (a : PartialQuotients) (n : ℕ) :
    (convergentMatrixProduct a n).map (Int.castRingHom ℚ) =
      !![(rationalGCF a).contsAux (n + 1) |>.a,
          (rationalGCF a).contsAux n |>.a;
        (rationalGCF a).contsAux (n + 1) |>.b,
          (rationalGCF a).contsAux n |>.b] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [convergentMatrixProduct, partialQuotientMatrix, rationalGCF,
          GenContFract.contsAux, partialQuotient]
  | succ n ih =>
      rw [convergentMatrixProduct, Matrix.map_mul, ih]
      have hq : partialQuotient a (n + 1) = (a.tail n : ℤ) := rfl
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, partialQuotientMatrix,
          rationalGCF, GenContFract.contsAux, GenContFract.nextConts,
          GenContFract.nextNum, GenContFract.nextDen, Stream'.Seq.get?,
          Stream'.Seq.ofStream, Stream'.map, Stream'.get, hq, mul_comm]

private theorem partialQuotient_shift (a : PartialQuotients) (i : ℕ) :
    partialQuotient (shiftPartials a) i = partialQuotient a (i + 1) := by
  cases i <;> rfl

private theorem finiteContinuedFractionFrom_shift (a : PartialQuotients)
    (n i : ℕ) :
    finiteContinuedFractionFrom (shiftPartials a) n i =
      finiteContinuedFractionFrom a n (i + 1) := by
  induction n generalizing i with
  | zero => simp [finiteContinuedFractionFrom, partialQuotient_shift]
  | succ n ih =>
      simp only [finiteContinuedFractionFrom, partialQuotient_shift]
      rw [ih]

private theorem finiteContinuedFraction_succ (a : PartialQuotients) (n : ℕ) :
    finiteContinuedFraction a (n + 1) =
      (a.a₀ : ℚ) + (finiteContinuedFraction (shiftPartials a) n)⁻¹ := by
  simp only [finiteContinuedFraction, finiteContinuedFractionFrom, partialQuotient]
  rw [finiteContinuedFractionFrom_shift]

private theorem rational_convs'_eq_finite (a : PartialQuotients) (n : ℕ) :
    (rationalGCF a).convs' n = finiteContinuedFraction a n := by
  induction n generalizing a with
  | zero => simp [rationalGCF, GenContFract.convs', GenContFract.convs'Aux,
      finiteContinuedFraction, finiteContinuedFractionFrom, partialQuotient]
  | succ n ih =>
      simp only [rationalGCF, GenContFract.convs', GenContFract.convs'Aux,
        Stream'.Seq.head, Stream'.Seq.tail, Stream'.Seq.get?,
        Stream'.Seq.ofStream, Stream'.map, Stream'.get]
      rw [one_div]
      change (a.a₀ : ℚ) + ((a.tail 0 : ℚ) +
        GenContFract.convs'Aux
          (Stream'.Seq.ofStream (fun k => ⟨1, (a.tail (k + 1) : ℚ)⟩)) n)⁻¹ = _
      change (a.a₀ : ℚ) + ((rationalGCF (shiftPartials a)).convs' n)⁻¹ = _
      rw [ih]
      exact (finiteContinuedFraction_succ a n).symm

theorem finite_eq_ratio (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) :
    finiteContinuedFraction a n =
      (convergentNumerator a n : ℚ) / (convergentDenominator a n : ℚ) := by
  rw [← rational_convs'_eq_finite]
  have hconv := congrFun (ContFract.convs_eq_convs' (c := rationalCF a hregular)) n
  change (rationalGCF a).convs n = (rationalGCF a).convs' n at hconv
  rw [← hconv]
  unfold GenContFract.convs GenContFract.nums GenContFract.dens GenContFract.conts
  have hm := matrix_eq_rational_contsAux a n
  have hnum := congr_fun (congr_fun hm 0) 0
  have hden := congr_fun (congr_fun hm 1) 0
  simpa [convergentNumerator, convergentDenominator] using
    congrArg₂ (· / ·) hnum.symm hden.symm

theorem denominator_zero (a : PartialQuotients) :
    convergentDenominator a 0 = 1 := by
  simp [convergentDenominator, convergentMatrixProduct, partialQuotientMatrix]

private theorem numerator_succ (a : PartialQuotients) (n : ℕ) :
    convergentNumerator a (n + 1) =
      partialQuotient a (n + 1) * convergentNumerator a n +
        previousConvergentNumerator a n := by
  simp [convergentNumerator, previousConvergentNumerator,
    convergentMatrixProduct, partialQuotientMatrix, Matrix.mul_apply,
    Fin.sum_univ_two, mul_comm]

private theorem previousNumerator_succ (a : PartialQuotients) (n : ℕ) :
    previousConvergentNumerator a (n + 1) = convergentNumerator a n := by
  simp [previousConvergentNumerator, convergentNumerator,
    convergentMatrixProduct, partialQuotientMatrix, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem previousDenominator_zero (a : PartialQuotients) :
    previousConvergentDenominator a 0 = 0 := by
  simp [previousConvergentDenominator, convergentMatrixProduct, partialQuotientMatrix]

theorem denominator_succ (a : PartialQuotients) (n : ℕ) :
    convergentDenominator a (n + 1) =
      partialQuotient a (n + 1) * convergentDenominator a n +
        previousConvergentDenominator a n := by
  simp [convergentDenominator, previousConvergentDenominator,
    convergentMatrixProduct, partialQuotientMatrix, Matrix.mul_apply,
    Fin.sum_univ_two, mul_comm]

theorem previousDenominator_succ (a : PartialQuotients) (n : ℕ) :
    previousConvergentDenominator a (n + 1) = convergentDenominator a n := by
  simp [previousConvergentDenominator, convergentDenominator,
    convergentMatrixProduct, partialQuotientMatrix, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem denominator_pos_and_previous_nonneg (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) :
    0 < convergentDenominator a n ∧ 0 ≤ previousConvergentDenominator a n := by
  induction n with
  | zero => simp [denominator_zero, previousDenominator_zero]
  | succ n ih =>
      rw [denominator_succ, previousDenominator_succ]
      have hq : 0 < partialQuotient a (n + 1) := by
        change 0 < (a.tail n : ℤ)
        exact_mod_cast hregular n
      constructor
      · exact add_pos_of_pos_of_nonneg (mul_pos hq ih.1) ih.2
      · exact ih.1.le

private theorem determinant_formula (a : PartialQuotients) (n : ℕ) :
    Matrix.det (convergentMatrixProduct a n) = (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero =>
      simp [convergentMatrixProduct, partialQuotientMatrix, Matrix.det_fin_two]
  | succ n ih =>
      rw [convergentMatrixProduct, Matrix.det_mul, ih]
      simp [partialQuotientMatrix, Matrix.det_fin_two, pow_succ]

private theorem denominator_two_step_gt (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) :
    convergentDenominator a n < convergentDenominator a (n + 2) := by
  rw [denominator_succ, previousDenominator_succ]
  have ha : 0 < partialQuotient a (n + 2) := by
    change 0 < (a.tail (n + 1) : ℤ)
    exact_mod_cast hregular (n + 1)
  have hq := (denominator_pos_and_previous_nonneg a hregular (n + 1)).1
  nlinarith

private theorem denominator_ge_index (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) :
    (n : ℤ) ≤ convergentDenominator a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [denominator_zero]
  | one =>
      rw [denominator_succ, denominator_zero, previousDenominator_zero]
      change (1 : ℤ) ≤ (a.tail 0 : ℤ) * 1 + 0
      simp only [mul_one, add_zero]
      exact_mod_cast hregular 0
  | more n hn hn1 =>
      rw [denominator_succ, previousDenominator_succ]
      have ha : 1 ≤ partialQuotient a (n + 2) := by
        change 1 ≤ (a.tail (n + 1) : ℤ)
        exact_mod_cast hregular (n + 1)
      have hq : 1 ≤ convergentDenominator a n :=
        (denominator_pos_and_previous_nonneg a hregular n).1
      have hmul : convergentDenominator a (n + 1) ≤
          partialQuotient a (n + 2) * convergentDenominator a (n + 1) := by
        nlinarith [(denominator_pos_and_previous_nonneg a hregular (n + 1)).1]
      calc
        ((n + 2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
        _ ≤ convergentDenominator a (n + 1) + convergentDenominator a n :=
          add_le_add hn1 hq
        _ ≤ partialQuotient a (n + 2) * convergentDenominator a (n + 1) +
            convergentDenominator a n := by
          simpa [add_comm] using add_le_add_right hmul (convergentDenominator a n)

private theorem tendsto_denominator_atTop (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) :
    Tendsto (fun n => convergentDenominator a n) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨N, hN⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  exact hN.trans (hNn.trans (denominator_ge_index a hregular n))

private theorem matrix_reconstruction (a : PartialQuotients) (n : ℕ) :
    convergentMatrixProduct a n =
      !![convergentNumerator a n, previousConvergentNumerator a n;
        convergentDenominator a n, previousConvergentDenominator a n] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem adjacent_determinant (a : PartialQuotients) (n : ℕ) :
    convergentNumerator a (n + 1) * convergentDenominator a n -
      convergentNumerator a n * convergentDenominator a (n + 1) =
        (-1 : ℤ) ^ n := by
  have hdet := determinant_formula a (n + 1)
  rw [matrix_reconstruction, Matrix.det_fin_two, previousNumerator_succ,
    previousDenominator_succ] at hdet
  simpa [pow_succ, mul_neg] using hdet

def realConvergent (a : PartialQuotients) (n : ℕ) : ℝ :=
  ((finiteContinuedFraction a n : ℚ) : ℝ)

private theorem adjacent_difference (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) :
    realConvergent a (n + 1) - realConvergent a n =
      ((-1 : ℤ) ^ n : ℝ) /
        ((convergentDenominator a n : ℝ) *
          (convergentDenominator a (n + 1) : ℝ)) := by
  simp only [realConvergent, finite_eq_ratio a hregular]
  norm_num only
  push_cast
  have hq₀ : (convergentDenominator a n : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos_and_previous_nonneg a hregular n).1.ne'
  have hq₁ : (convergentDenominator a (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos_and_previous_nonneg a hregular (n + 1)).1.ne'
  field_simp [hq₀, hq₁]
  exact_mod_cast (by simpa [mul_comm] using adjacent_determinant a n)

private theorem cast_neg_one_pow_cases (n : ℕ) :
    (((-1 : ℤ) ^ n : ℤ) : ℝ) = 1 ∨ (((-1 : ℤ) ^ n : ℤ) : ℝ) = -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases ih with h | h
      · right
        simp only [pow_succ, Int.cast_mul, Int.cast_neg, Int.cast_one]
        rw [h]
        norm_num
      · left
        simp only [pow_succ, Int.cast_mul, Int.cast_neg, Int.cast_one]
        rw [h]
        norm_num

private theorem convergent_two_step_between (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) :
    (realConvergent a n < realConvergent a (n + 2) ∧
        realConvergent a (n + 2) < realConvergent a (n + 1)) ∨
      (realConvergent a (n + 1) < realConvergent a (n + 2) ∧
        realConvergent a (n + 2) < realConvergent a n) := by
  let q₀ : ℝ := convergentDenominator a n
  let q₁ : ℝ := convergentDenominator a (n + 1)
  let q₂ : ℝ := convergentDenominator a (n + 2)
  let s : ℝ := (((-1 : ℤ) ^ n : ℤ) : ℝ)
  have hq₀ : 0 < q₀ := by
    simpa [q₀] using
      (show (0 : ℝ) < (convergentDenominator a n : ℝ) by
        exact_mod_cast (denominator_pos_and_previous_nonneg a hregular n).1)
  have hq₁ : 0 < q₁ := by
    simpa [q₁] using
      (show (0 : ℝ) < (convergentDenominator a (n + 1) : ℝ) by
        exact_mod_cast (denominator_pos_and_previous_nonneg a hregular (n + 1)).1)
  have hq₂ : 0 < q₂ := by
    simpa [q₂] using
      (show (0 : ℝ) < (convergentDenominator a (n + 2) : ℝ) by
        exact_mod_cast (denominator_pos_and_previous_nonneg a hregular (n + 2)).1)
  have hq₀₂ : q₀ < q₂ := by
    simpa [q₀, q₂] using
      (show (convergentDenominator a n : ℝ) <
          (convergentDenominator a (n + 2) : ℝ) by
        exact_mod_cast denominator_two_step_gt a hregular n)
  have hprod : q₀ * q₁ < q₁ * q₂ := by nlinarith
  have hinv : (1 : ℝ) / (q₁ * q₂) < 1 / (q₀ * q₁) := by
    exact one_div_lt_one_div_of_lt (mul_pos hq₀ hq₁) hprod
  have hinv₀ : 0 < (1 : ℝ) / (q₀ * q₁) := one_div_pos.mpr (mul_pos hq₀ hq₁)
  have hinv₁ : 0 < (1 : ℝ) / (q₁ * q₂) := one_div_pos.mpr (mul_pos hq₁ hq₂)
  have hd₀ : realConvergent a (n + 1) - realConvergent a n = s / (q₀ * q₁) := by
    simpa only [s, q₀, q₁, Int.cast_pow, Int.cast_neg, Int.cast_one] using
      adjacent_difference a hregular n
  have hd₁ := adjacent_difference a hregular (n + 1)
  have hsuc : (((-1 : ℤ) : ℝ) ^ (n + 1)) = -s := by
    simp only [pow_succ, s, Int.cast_pow, Int.cast_neg, Int.cast_one]
    ring
  rw [hsuc] at hd₁
  change realConvergent a (n + 2) - realConvergent a (n + 1) =
    -s / (q₁ * q₂) at hd₁
  rcases cast_neg_one_pow_cases n with hs | hs
  · left
    change s = 1 at hs
    rw [hs] at hd₀ hd₁
    have h02 : 0 < realConvergent a (n + 2) - realConvergent a n := by
      calc
        realConvergent a (n + 2) - realConvergent a n =
            (realConvergent a (n + 2) - realConvergent a (n + 1)) +
              (realConvergent a (n + 1) - realConvergent a n) := by ring
        _ = -(1 / (q₁ * q₂)) + 1 / (q₀ * q₁) := by rw [hd₁, hd₀]; ring
        _ > 0 := by linarith
    have h21 : realConvergent a (n + 2) - realConvergent a (n + 1) < 0 := by
      rw [hd₁]
      exact div_neg_of_neg_of_pos (by norm_num) (mul_pos hq₁ hq₂)
    exact ⟨sub_pos.mp h02, sub_neg.mp h21⟩
  · right
    change s = -1 at hs
    rw [hs] at hd₀ hd₁
    have h20 : realConvergent a (n + 2) - realConvergent a n < 0 := by
      calc
        realConvergent a (n + 2) - realConvergent a n =
            (realConvergent a (n + 2) - realConvergent a (n + 1)) +
              (realConvergent a (n + 1) - realConvergent a n) := by ring
        _ = 1 / (q₁ * q₂) - 1 / (q₀ * q₁) := by rw [hd₁, hd₀]; ring
        _ < 0 := sub_neg.mpr hinv
    have h12 : 0 < realConvergent a (n + 2) - realConvergent a (n + 1) := by
      rw [hd₁]
      simpa using hinv₁
    exact ⟨sub_pos.mp h12, sub_neg.mp h20⟩

private theorem convergent_tail_bounds (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n d : ℕ) :
    min (realConvergent a n) (realConvergent a (n + 1)) ≤
        realConvergent a (n + d) ∧
      realConvergent a (n + d) ≤
        max (realConvergent a n) (realConvergent a (n + 1)) := by
  induction d using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more d hd hd1 =>
      have hbetween := convergent_two_step_between a hregular (n + d)
      have hbetween' :
          (realConvergent a (n + d) < realConvergent a (n + (d + 2)) ∧
              realConvergent a (n + (d + 2)) < realConvergent a (n + (d + 1))) ∨
            (realConvergent a (n + (d + 1)) < realConvergent a (n + (d + 2)) ∧
              realConvergent a (n + (d + 2)) < realConvergent a (n + d)) := by
        convert hbetween using 1
      rcases hbetween' with hbetween' | hbetween' <;>
        constructor <;> linarith [hd.1, hd.2, hd1.1, hd1.2]

private theorem limit_between_adjacent_convergents (a : PartialQuotients) (u : ℝ)
    (hregular : IsRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ) :
    min (realConvergent a n) (realConvergent a (n + 1)) ≤ u ∧
      u ≤ max (realConvergent a n) (realConvergent a (n + 1)) := by
  have hevent : ∀ᶠ m : ℕ in atTop,
      realConvergent a m ∈ Set.Icc
        (min (realConvergent a n) (realConvergent a (n + 1)))
        (max (realConvergent a n) (realConvergent a (n + 1))) := by
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact convergent_tail_bounds a hregular n d
  have htend : Tendsto (realConvergent a) atTop (nhds u) := by
    simpa [realConvergent] using hexp.2
  exact isClosed_Icc.mem_of_tendsto htend hevent

private theorem convergent_error_le (a : PartialQuotients) (u : ℝ)
    (hregular : IsRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ) :
    |u - realConvergent a n| ≤
      ((convergentDenominator a n : ℝ) *
        (convergentDenominator a (n + 1) : ℝ))⁻¹ := by
  have hbetween := limit_between_adjacent_convergents a u hregular hexp n
  have hdiff := adjacent_difference a hregular n
  have hq₀ : (0 : ℝ) < convergentDenominator a n := by
    exact_mod_cast (denominator_pos_and_previous_nonneg a hregular n).1
  have hq₁ : (0 : ℝ) < convergentDenominator a (n + 1) := by
    exact_mod_cast (denominator_pos_and_previous_nonneg a hregular (n + 1)).1
  have hprod : (0 : ℝ) < (convergentDenominator a n : ℝ) *
      (convergentDenominator a (n + 1) : ℝ) := mul_pos hq₀ hq₁
  rcases cast_neg_one_pow_cases n with hs | hs
  · have hs' : (((-1 : ℤ) : ℝ) ^ n) = 1 := by
      simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hs
    rw [hs'] at hdiff
    have hc : realConvergent a n < realConvergent a (n + 1) := by
      apply sub_pos.mp
      rw [hdiff]
      exact div_pos (by norm_num) hprod
    rw [min_eq_left hc.le, max_eq_right hc.le] at hbetween
    have horder : realConvergent a n ≤ u ∧ u ≤ realConvergent a (n + 1) := hbetween
    rw [abs_of_nonneg (sub_nonneg.mpr horder.1)]
    have hwidth : realConvergent a (n + 1) - realConvergent a n =
        ((convergentDenominator a n : ℝ) *
          (convergentDenominator a (n + 1) : ℝ))⁻¹ := by
      simpa [div_eq_mul_inv] using hdiff
    linarith
  · have hs' : (((-1 : ℤ) : ℝ) ^ n) = -1 := by
      simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hs
    rw [hs'] at hdiff
    have hc : realConvergent a (n + 1) < realConvergent a n := by
      apply sub_neg.mp
      rw [hdiff]
      exact div_neg_of_neg_of_pos (by norm_num) hprod
    rw [min_eq_right hc.le, max_eq_left hc.le] at hbetween
    have horder : realConvergent a (n + 1) ≤ u ∧ u ≤ realConvergent a n := hbetween
    rw [abs_of_nonpos (sub_nonpos.mpr horder.2)]
    have hwidth : realConvergent a n - realConvergent a (n + 1) =
        ((convergentDenominator a n : ℝ) *
          (convergentDenominator a (n + 1) : ℝ))⁻¹ := by
      rw [← neg_sub, hdiff]
      field_simp
    linarith

theorem convergent_error_lt_of_irrational (a : PartialQuotients) (u : ℝ)
    (hregular : IsRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (hirr : Irrational u) (n : ℕ) :
    |u - realConvergent a n| <
      ((convergentDenominator a n : ℝ) *
        (convergentDenominator a (n + 1) : ℝ))⁻¹ := by
  have hbetween := limit_between_adjacent_convergents a u hregular hexp n
  have hdiff := adjacent_difference a hregular n
  have hq₀ : (0 : ℝ) < convergentDenominator a n := by
    exact_mod_cast (denominator_pos_and_previous_nonneg a hregular n).1
  have hq₁ : (0 : ℝ) < convergentDenominator a (n + 1) := by
    exact_mod_cast (denominator_pos_and_previous_nonneg a hregular (n + 1)).1
  have hprod : (0 : ℝ) < (convergentDenominator a n : ℝ) *
      (convergentDenominator a (n + 1) : ℝ) := mul_pos hq₀ hq₁
  have hne : u ≠ realConvergent a (n + 1) := by
    intro heq
    apply hirr
    refine ⟨finiteContinuedFraction a (n + 1), ?_⟩
    simpa [realConvergent] using heq.symm
  rcases cast_neg_one_pow_cases n with hs | hs
  · have hs' : (((-1 : ℤ) : ℝ) ^ n) = 1 := by
      simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hs
    rw [hs'] at hdiff
    have hc : realConvergent a n < realConvergent a (n + 1) := by
      apply sub_pos.mp
      rw [hdiff]
      exact div_pos (by norm_num) hprod
    rw [min_eq_left hc.le, max_eq_right hc.le] at hbetween
    rw [abs_of_nonneg (sub_nonneg.mpr hbetween.1)]
    have hu : u < realConvergent a (n + 1) := lt_of_le_of_ne hbetween.2 hne
    have hwidth : realConvergent a (n + 1) - realConvergent a n =
        ((convergentDenominator a n : ℝ) *
          (convergentDenominator a (n + 1) : ℝ))⁻¹ := by
      simpa [div_eq_mul_inv] using hdiff
    linarith
  · have hs' : (((-1 : ℤ) : ℝ) ^ n) = -1 := by
      simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hs
    rw [hs'] at hdiff
    have hc : realConvergent a (n + 1) < realConvergent a n := by
      apply sub_neg.mp
      rw [hdiff]
      exact div_neg_of_neg_of_pos (by norm_num) hprod
    rw [min_eq_right hc.le, max_eq_left hc.le] at hbetween
    rw [abs_of_nonpos (sub_nonpos.mpr hbetween.2)]
    have hu : realConvergent a (n + 1) < u := lt_of_le_of_ne hbetween.1 hne.symm
    have hwidth : realConvergent a n - realConvergent a (n + 1) =
        ((convergentDenominator a n : ℝ) *
          (convergentDenominator a (n + 1) : ℝ))⁻¹ := by
      rw [← neg_sub, hdiff]
      field_simp
    linarith

private theorem rational_separation (r : ℚ) (p q : ℤ) (hq : 0 < q)
    (hne : ((p : ℝ) / (q : ℝ)) ≠ (r : ℝ)) :
    1 / ((r.den : ℝ) * (q : ℝ)) ≤
      |(r : ℝ) - (p : ℝ) / (q : ℝ)| := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrden0 : (r.den : ℝ) ≠ 0 := by positivity
  have hr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    exact_mod_cast r.num_div_den.symm
  let D : ℤ := r.num * q - p * (r.den : ℤ)
  have hD : D ≠ 0 := by
    intro hzero
    apply hne
    rw [hr]
    have hzero' : (r.num : ℝ) * (q : ℝ) -
        (p : ℝ) * (r.den : ℝ) = 0 := by exact_mod_cast hzero
    field_simp [hq0, hrden0]
    linarith
  have hDone : (1 : ℝ) ≤ |(D : ℝ)| := by
    have hnat : 0 < D.natAbs := Int.natAbs_pos.mpr hD
    simpa using (show (1 : ℝ) ≤ D.natAbs by exact_mod_cast hnat)
  have hdenpos : 0 < (r.den : ℝ) * (q : ℝ) := by positivity
  have heq : (r : ℝ) - (p : ℝ) / (q : ℝ) =
      (D : ℝ) / ((r.den : ℝ) * (q : ℝ)) := by
    rw [hr]
    simp only [D, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    field_simp [hq0, hrden0]
  rw [heq, abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right hDone hdenpos.le

private theorem rational_limit_contradiction_at (a : PartialQuotients) (u : ℝ)
    (hregular : IsRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (r : ℚ) (hr : u = (r : ℝ))
    (k : ℕ) (hne : realConvergent a k ≠ u)
    (hnext : (r.den : ℤ) < convergentDenominator a (k + 1)) : False := by
  let p := convergentNumerator a k
  let q := convergentDenominator a k
  have hq : 0 < q := denominator_pos_and_previous_nonneg a hregular k |>.1
  have hconv : realConvergent a k = (p : ℝ) / (q : ℝ) := by
    simp only [realConvergent, finite_eq_ratio a hregular k, p, q]
    push_cast
    rfl
  have hfrac : ((p : ℝ) / (q : ℝ)) ≠ (r : ℝ) := by
    rw [← hr, ← hconv]
    exact hne
  have hsep := rational_separation r p q hq hfrac
  have herr := convergent_error_le a u hregular hexp k
  rw [hr, hconv] at herr
  have habs : |(r : ℝ) - (p : ℝ) / (q : ℝ)| =
      |(p : ℝ) / (q : ℝ) - (r : ℝ)| := abs_sub_comm _ _
  rw [habs] at hsep
  have hrdenpos : (0 : ℝ) < r.den := by positivity
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hnextreal : (r.den : ℝ) < convergentDenominator a (k + 1) := by
    exact_mod_cast hnext
  have hprod : (r.den : ℝ) * (q : ℝ) <
      (q : ℝ) * (convergentDenominator a (k + 1) : ℝ) := by
    nlinarith
  have hinv :
      1 / ((q : ℝ) * (convergentDenominator a (k + 1) : ℝ)) <
        1 / ((r.den : ℝ) * (q : ℝ)) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · nlinarith
  have herr' : |(p : ℝ) / (q : ℝ) - (r : ℝ)| ≤
      1 / ((q : ℝ) * (convergentDenominator a (k + 1) : ℝ)) := by
    simpa [one_div, q, abs_sub_comm] using herr
  linarith

private theorem adjacent_realConvergent_ne (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) :
    realConvergent a (n + 1) ≠ realConvergent a n := by
  intro h
  have hd := adjacent_difference a hregular n
  rw [h, sub_self] at hd
  have hq₀ : (convergentDenominator a n : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_pos_and_previous_nonneg a hregular n).1.ne'
  have hq₁ : (convergentDenominator a (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast
      (denominator_pos_and_previous_nonneg a hregular (n + 1)).1.ne'
  field_simp [hq₀, hq₁] at hd
  have hpow : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  apply hpow
  simpa using hd.symm

private theorem infinite_regular_expansion_irrational (a : PartialQuotients) (u : ℝ)
    (hregular : IsRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) : Irrational u := by
  intro hrat
  rcases hrat with ⟨r, hr⟩
  let n : ℕ := r.den + 1
  have hnnext : (r.den : ℤ) < convergentDenominator a (n + 1) := by
    have hindex := denominator_ge_index a hregular (n + 1)
    have : (r.den : ℤ) < ((n + 1 : ℕ) : ℤ) := by
      simp [n]
    exact this.trans_le hindex
  have hnnextnext : (r.den : ℤ) < convergentDenominator a ((n + 1) + 1) := by
    have hindex := denominator_ge_index a hregular ((n + 1) + 1)
    have : (r.den : ℤ) < (((n + 1) + 1 : ℕ) : ℤ) := by
      simp [n]
      omega
    exact this.trans_le hindex
  by_cases hn : realConvergent a n = u
  · have hne : realConvergent a (n + 1) ≠ u := by
      intro hnext
      apply adjacent_realConvergent_ne a hregular n
      rw [hnext, hn]
    exact rational_limit_contradiction_at a u hregular hexp r hr.symm (n + 1) hne
      hnnextnext
  · exact rational_limit_contradiction_at a u hregular hexp r hr.symm n hn hnnext

private theorem neg_one_pow_mul_self (n : ℕ) :
    ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      simp only [pow_succ]
      calc
        ((-1 : ℤ) ^ n * -1) * ((-1 : ℤ) ^ n * -1) =
            (((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n)) * (-1 * -1) := by ring
        _ = 1 := by rw [ih]; norm_num

private theorem convergent_coprime (a : PartialQuotients) (n : ℕ) :
    Nat.Coprime (convergentNumerator a n).natAbs
      (convergentDenominator a n).natAbs := by
  rw [← Int.isCoprime_iff_nat_coprime]
  let s : ℤ := (-1 : ℤ) ^ (n + 1)
  refine ⟨s * previousConvergentDenominator a n,
    -(s * previousConvergentNumerator a n), ?_⟩
  have hdet := determinant_formula a n
  rw [matrix_reconstruction, Matrix.det_fin_two] at hdet
  have hdet' :
      convergentNumerator a n * previousConvergentDenominator a n -
        previousConvergentNumerator a n * convergentDenominator a n = s := by
    simpa [s] using hdet
  calc
    (s * previousConvergentDenominator a n) * convergentNumerator a n +
        -(s * previousConvergentNumerator a n) * convergentDenominator a n =
      s * (convergentNumerator a n * previousConvergentDenominator a n -
        previousConvergentNumerator a n * convergentDenominator a n) := by ring
    _ = s * s := by rw [hdet']
    _ = 1 := neg_one_pow_mul_self (n + 1)

/--
Source: Proposition 3.1.1, Chapter 3, Section 1.
For partial quotients `a₀ ∈ ℤ₊` and `aₙ ∈ ℕ` for `n ≥ 1`, the finite convergents
`pₙ / qₙ = [a₀; a₁, …, aₙ]` are obtained from the product of the matrices
`[[aᵢ, 1], [1, 0]]`; the numerator and denominator are coprime, with the usual
convention `p₋₁ = 1`, `q₋₁ = 0`, `p₀ = a₀`, `q₀ = 1`.
-/
theorem convergentsSatisfyMatrixProductFormula (a : PartialQuotients)
    (hregular : IsNonnegativeRegularPartialQuotients a) :
    HasConvergentMatrixFormula a := by
  intro n
  exact ⟨(denominator_pos_and_previous_nonneg a hregular.2 n).1,
    convergent_coprime a n, finite_eq_ratio a hregular.2 n,
    matrix_reconstruction a n, determinant_formula a n⟩

/--
Source: Definition 3.1.2, Chapter 3, Section 1.
`[a₀; a₁, a₂, …]` is the continued fraction expansion of `u`.
-/
def continuedFractionExpansion (u : ℝ) (a : PartialQuotients) : Prop :=
  HasContinuedFractionExpansion u a

/--
Source: Theorem 3.1.3, Chapter 3, Section 1.
If `aₙ ∈ ℕ` for `n ≥ 1` and `a₀ ∈ ℤ₊`, then the infinite continued fraction
`[a₀; a₁, a₂, …]`, defined as the limit of the finite convergents, is irrational.
-/
theorem infiniteContinuedFractionExpansionIsIrrational (a : PartialQuotients) (u : ℝ)
    (hregular : IsNonnegativeRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) :
    Irrational u := by
  exact infinite_regular_expansion_irrational a u hregular.2 hexp

private theorem canonical_s_isSome (u : ℝ) (hirr : Irrational u) (n : ℕ) :
    ((GenContFract.of u).s.get? n).isSome = true := by
  apply Stream'.Seq.not_terminates_iff.mp
  intro hterm
  obtain ⟨r, hr⟩ := (GenContFract.terminates_iff_rat u).mp hterm
  exact hirr ⟨r, hr.symm⟩

private noncomputable def canonicalPair (u : ℝ) (hirr : Irrational u) (n : ℕ) :
    GenContFract.Pair ℝ :=
  ((GenContFract.of u).s.get? n).get (canonical_s_isSome u hirr n)

private theorem canonicalPair_spec (u : ℝ) (hirr : Irrational u) (n : ℕ) :
    (GenContFract.of u).s.get? n = some (canonicalPair u hirr n) := by
  exact Option.eq_some_of_isSome (canonical_s_isSome u hirr n)

private noncomputable def canonicalDenInt (u : ℝ) (hirr : Irrational u) (n : ℕ) : ℤ :=
  Classical.choose (GenContFract.exists_int_eq_of_partDen
    (GenContFract.partDen_eq_s_b (canonicalPair_spec u hirr n)))

private theorem canonicalPair_b_eq (u : ℝ) (hirr : Irrational u) (n : ℕ) :
    (canonicalPair u hirr n).b = (canonicalDenInt u hirr n : ℝ) :=
  Classical.choose_spec (GenContFract.exists_int_eq_of_partDen
    (GenContFract.partDen_eq_s_b (canonicalPair_spec u hirr n)))

private theorem canonicalDenInt_pos (u : ℝ) (hirr : Irrational u) (n : ℕ) :
    0 < canonicalDenInt u hirr n := by
  have hb : (1 : ℝ) ≤ (canonicalPair u hirr n).b :=
    GenContFract.of_one_le_get?_partDen
      (GenContFract.partDen_eq_s_b (canonicalPair_spec u hirr n))
  rw [canonicalPair_b_eq] at hb
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hb)

private noncomputable def canonicalPartials (u : ℝ) (hirr : Irrational u) :
    PartialQuotients where
  a₀ := Int.floor u
  tail := fun n => (canonicalDenInt u hirr n).toNat

private theorem canonicalPartials_regular (u : ℝ) (hirr : Irrational u) :
    IsRegularPartialQuotients (canonicalPartials u hirr) := by
  intro n
  simp only [canonicalPartials]
  have hz := canonicalDenInt_pos u hirr n
  have heq : ((canonicalDenInt u hirr n).toNat : ℤ) =
      canonicalDenInt u hirr n := Int.toNat_of_nonneg hz.le
  omega

private def realGCF (a : PartialQuotients) : GenContFract ℝ where
  h := a.a₀
  s := Stream'.Seq.ofStream (fun n => ⟨1, a.tail n⟩)

private theorem real_convs'_eq_finite (a : PartialQuotients) (n : ℕ) :
    (realGCF a).convs' n = ((finiteContinuedFraction a n : ℚ) : ℝ) := by
  induction n generalizing a with
  | zero => simp [realGCF, GenContFract.convs', GenContFract.convs'Aux,
      finiteContinuedFraction, finiteContinuedFractionFrom, partialQuotient]
  | succ n ih =>
      simp only [realGCF, GenContFract.convs', GenContFract.convs'Aux,
        Stream'.Seq.head, Stream'.Seq.tail, Stream'.Seq.get?,
        Stream'.Seq.ofStream, Stream'.map, Stream'.get]
      rw [one_div]
      change (a.a₀ : ℝ) + ((a.tail 0 : ℝ) +
        GenContFract.convs'Aux
          (Stream'.Seq.ofStream (fun k => ⟨1, (a.tail (k + 1) : ℝ)⟩)) n)⁻¹ = _
      change (a.a₀ : ℝ) + ((realGCF (shiftPartials a)).convs' n)⁻¹ = _
      rw [ih, finiteContinuedFraction_succ]
      push_cast
      rfl

private theorem realGCF_canonicalPartials (u : ℝ) (hirr : Irrational u) :
    realGCF (canonicalPartials u hirr) = GenContFract.of u := by
  apply GenContFract.ext
  · simp [realGCF, canonicalPartials, GenContFract.of_h_eq_floor]
  · apply Stream'.Seq.ext
    intro n
    rw [canonicalPair_spec u hirr n]
    have ha : (canonicalPair u hirr n).a = 1 :=
      GenContFract.of_partNum_eq_one
        (GenContFract.partNum_eq_s_a (canonicalPair_spec u hirr n))
    have hb := canonicalPair_b_eq u hirr n
    have hz := canonicalDenInt_pos u hirr n
    simp only [realGCF, Stream'.Seq.get?, Stream'.Seq.ofStream, Stream'.get,
      Stream'.map, canonicalPartials]
    congr 2
    · exact ha.symm
    · change ((canonicalDenInt u hirr n).toNat : ℝ) =
        (canonicalPair u hirr n).b
      rw [hb]
      exact_mod_cast (Int.toNat_of_nonneg hz.le)

private theorem canonicalPartials_expansion (u : ℝ) (hirr : Irrational u) :
    HasContinuedFractionExpansion u (canonicalPartials u hirr) := by
  refine ⟨canonicalPartials_regular u hirr, ?_⟩
  have hlim := GenContFract.of_convergence u
  rw [GenContFract.of_convs_eq_convs'] at hlim
  rw [← realGCF_canonicalPartials u hirr] at hlim
  convert hlim using 1
  ext n
  rw [real_convs'_eq_finite]

private theorem expansion_floor_eq (a : PartialQuotients) (u : ℝ)
    (hregular : IsRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (hirr : Irrational u) :
    Int.floor u = a.a₀ := by
  have hbetween := limit_between_adjacent_convergents a u hregular hexp 0
  have htpos : 0 < a.tail 0 := hregular 0
  have htposR : (0 : ℝ) < a.tail 0 := by exact_mod_cast htpos
  have htoneR : (1 : ℝ) ≤ a.tail 0 := by exact_mod_cast htpos
  have hc0 : realConvergent a 0 = (a.a₀ : ℝ) := by
    simp [realConvergent, finiteContinuedFraction, finiteContinuedFractionFrom,
      partialQuotient]
  have hc1 : realConvergent a 1 =
      (a.a₀ : ℝ) + ((a.tail 0 : ℝ))⁻¹ := by
    simp [realConvergent, finiteContinuedFraction, finiteContinuedFractionFrom,
      partialQuotient]
  have horder : (a.a₀ : ℝ) ≤ (a.a₀ : ℝ) + (a.tail 0 : ℝ)⁻¹ := by
    have := inv_pos.mpr htposR
    linarith
  rw [hc0, hc1, min_eq_left horder, max_eq_right horder] at hbetween
  rw [Int.floor_eq_iff]
  refine ⟨hbetween.1, ?_⟩
  have hinvle : (a.tail 0 : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ htposR).2 htoneR
  have hle : u ≤ (a.a₀ : ℝ) + 1 := hbetween.2.trans (by linarith)
  exact hle.lt_of_ne (by
    simpa only [Int.cast_add, Int.cast_one] using hirr.ne_int (a.a₀ + 1))

private theorem finiteContinuedFractionFrom_pos (a : PartialQuotients)
    (hpos : ∀ i : ℕ, 0 < partialQuotient a i) (n i : ℕ) :
    0 < finiteContinuedFractionFrom a n i := by
  induction n generalizing i with
  | zero =>
      simp only [finiteContinuedFractionFrom]
      exact_mod_cast hpos i
  | succ n ih =>
      rw [finiteContinuedFractionFrom]
      have hhead : (0 : ℚ) < partialQuotient a i := by exact_mod_cast hpos i
      have htail := ih (i + 1)
      positivity

private theorem shift_expansion (a : PartialQuotients) (u : ℝ)
    (hregular : IsRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (hirr : Irrational u) :
    HasContinuedFractionExpansion ((u - (a.a₀ : ℝ))⁻¹) (shiftPartials a) := by
  have hshiftreg : IsRegularPartialQuotients (shiftPartials a) := by
    intro n
    exact hregular (n + 1)
  refine ⟨hshiftreg, ?_⟩
  have hindex : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hsucc := hexp.2.comp hindex
  have hsub := hsucc.sub_const (a.a₀ : ℝ)
  have hune : u - (a.a₀ : ℝ) ≠ 0 :=
    (hirr.sub_intCast a.a₀).ne_zero
  have hinv := hsub.inv₀ hune
  convert hinv using 1
  ext n
  change ((finiteContinuedFraction (shiftPartials a) n : ℚ) : ℝ) =
    (((finiteContinuedFraction a (n + 1) : ℚ) : ℝ) - (a.a₀ : ℝ))⁻¹
  rw [finiteContinuedFraction_succ]
  push_cast
  simp only [add_sub_cancel_left, inv_inv]

private def completeIterate (u : ℝ) : ℕ → ℝ
  | 0 => u
  | n + 1 => ((completeIterate u n - (Int.floor (completeIterate u n) : ℝ))⁻¹)

private theorem iterate_shift_expansion (a : PartialQuotients) (u : ℝ)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ) :
    HasContinuedFractionExpansion (completeIterate u n) ((shiftPartials^[n]) a) := by
  induction n with
  | zero => simpa [completeIterate] using hexp
  | succ n ih =>
      have hirr := infinite_regular_expansion_irrational _ _ ih.1 ih
      have hfloor := expansion_floor_eq _ _ ih.1 ih hirr
      rw [Function.iterate_succ_apply']
      simpa [completeIterate, hfloor] using shift_expansion _ _ ih.1 ih hirr

private theorem iterate_shift_a0 (a : PartialQuotients) (n : ℕ) :
    ((shiftPartials^[n + 1]) a).a₀ = (a.tail n : ℤ) := by
  induction n generalizing a with
  | zero => simp [shiftPartials]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        Function.iterate_succ_apply]
      simpa [shiftPartials] using ih (shiftPartials a)

private theorem expansion_unique (a b : PartialQuotients) (u : ℝ)
    (ha : HasContinuedFractionExpansion u a)
    (hb : HasContinuedFractionExpansion u b) : a = b := by
  have ha0 := expansion_floor_eq a u ha.1 ha
    (infinite_regular_expansion_irrational a u ha.1 ha)
  have hb0 := expansion_floor_eq b u hb.1 hb
    (infinite_regular_expansion_irrational b u hb.1 hb)
  cases a with
  | mk a0 atail =>
    cases b with
    | mk b0 btail =>
      congr
      · exact ha0.symm.trans hb0
      · funext n
        have hea := iterate_shift_expansion { a₀ := a0, tail := atail } u ha (n + 1)
        have heb := iterate_shift_expansion { a₀ := b0, tail := btail } u hb (n + 1)
        have hfa := expansion_floor_eq _ _ hea.1 hea
          (infinite_regular_expansion_irrational _ _ hea.1 hea)
        have hfb := expansion_floor_eq _ _ heb.1 heb
          (infinite_regular_expansion_irrational _ _ heb.1 heb)
        rw [iterate_shift_a0] at hfa hfb
        exact_mod_cast hfa.symm.trans hfb

private theorem convergents_cauchy (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) : CauchySeq (realConvergent a) := by
  rw [cauchySeq_iff_le_tendsto_0]
  refine ⟨fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1), ?_, ?_,
    tendsto_one_div_add_atTop_nhds_zero_nat⟩
  · intro N
    positivity
  · intro n m N hNn hNm
    obtain ⟨dn, rfl⟩ : ∃ d, n = N + d := ⟨n - N, by omega⟩
    obtain ⟨dm, rfl⟩ : ∃ d, m = N + d := ⟨m - N, by omega⟩
    have hn := convergent_tail_bounds a hregular N dn
    have hm := convergent_tail_bounds a hregular N dm
    have hdist : dist (realConvergent a (N + dn))
        (realConvergent a (N + dm)) ≤
        |realConvergent a (N + 1) - realConvergent a N| := by
      rw [Real.dist_eq]
      rcases le_total (realConvergent a N) (realConvergent a (N + 1)) with h | h
      · rw [min_eq_left h, max_eq_right h] at hn hm
        rw [abs_of_nonneg (sub_nonneg.mpr h)]
        rw [abs_sub_comm]
        exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
      · rw [min_eq_right h, max_eq_left h] at hn hm
        rw [abs_of_nonpos (sub_nonpos.mpr h)]
        exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    refine hdist.trans ?_
    rw [adjacent_difference a hregular N, abs_div, abs_mul]
    norm_num only [Int.cast_neg, Int.cast_one, abs_pow, abs_neg, abs_one,
      one_pow, one_div]
    have hqN : (0 : ℝ) < convergentDenominator a N := by
      exact_mod_cast (denominator_pos_and_previous_nonneg a hregular N).1
    have hqN1 : (0 : ℝ) < convergentDenominator a (N + 1) := by
      exact_mod_cast (denominator_pos_and_previous_nonneg a hregular (N + 1)).1
    rw [abs_of_pos hqN, abs_of_pos hqN1]
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    have hqone : (1 : ℝ) ≤ convergentDenominator a N := by
      exact_mod_cast (denominator_pos_and_previous_nonneg a hregular N).1
    have hqindex : ((N : ℝ) + 1) ≤ convergentDenominator a (N + 1) := by
      exact_mod_cast denominator_ge_index a hregular (N + 1)
    nlinarith

private theorem expansion_at_continuedFractionValue (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) :
    HasContinuedFractionExpansion (continuedFractionValue a) a := by
  refine ⟨hregular, ?_⟩
  apply tendsto_nhds_limUnder
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete (convergents_cauchy a hregular)
  exact ⟨u, hu⟩

/--
Source: Proposition 3.1.4, Chapter 3, Section 1.
Every nonnegative irrational real number has a continued fraction expansion
`[a₀; a₁, a₂, …]`, and the map from partial quotients to the represented real
number is injective; in particular, the expansion of a nonnegative irrational is
unique.
-/
theorem nonnegativeIrrationalHasUniqueContinuedFractionExpansion :
    NonnegativeContinuedFractionClassification := by
  constructor
  · intro a b hab
    simp only [nonnegativeContinuedFractionMap] at hab
    apply Subtype.ext
    apply expansion_unique a.1 b.1 (nonnegativeContinuedFractionMap a)
    · exact expansion_at_continuedFractionValue a.1 a.2.2
    · change HasContinuedFractionExpansion (continuedFractionValue a.1) b.1
      rw [hab]
      exact expansion_at_continuedFractionValue b.1 b.2.2
  · intro u hu hirr
    have hfloor : 0 ≤ Int.floor u := Int.floor_nonneg.mpr hu
    let a : NonnegativeRegularPartialQuotients :=
      ⟨canonicalPartials u hirr, hfloor, canonicalPartials_regular u hirr⟩
    refine ⟨a, canonicalPartials_expansion u hirr, ?_⟩
    intro b hb
    apply Subtype.ext
    exact expansion_unique b.1 a.1 u hb (canonicalPartials_expansion u hirr)

/--
Source: Remark 3.1.5, Chapter 3, Section 1.
The Euclidean algorithm gives the continued fraction expansion by repeatedly
taking integer parts and reciprocals of fractional parts. A rational number has
a finite continued fraction expansion, while an irrational number has an
infinite expansion; the irrational expansion is unique.
-/
def rationalIffFiniteContinuedFractionExpansionRemark : Prop :=
  (∀ u : ℝ, ¬ Irrational u -> ∃ n : ℕ, ∃ a : PartialQuotients,
    ((finiteContinuedFraction a n : ℚ) : ℝ) = u) ∧
  (∀ u : ℝ, Irrational u -> ∃ a : PartialQuotients,
    HasContinuedFractionExpansion u a)

private theorem golden_tail_finite (n i : ℕ) (hi : 0 < i) :
    finiteContinuedFractionFrom goldenRatioConjugatePartials n i =
      (Nat.fib (n + 2) : ℚ) / (Nat.fib (n + 1) : ℚ) := by
  induction n generalizing i with
  | zero =>
      cases i with
      | zero => simp at hi
      | succ i => simp [finiteContinuedFractionFrom, partialQuotient,
          goldenRatioConjugatePartials]
  | succ n ih =>
      rw [finiteContinuedFractionFrom, ih (i + 1) (Nat.zero_lt_succ i)]
      cases i with
      | zero => simp at hi
      | succ i =>
          simp only [partialQuotient, goldenRatioConjugatePartials]
          have h₁ : (Nat.fib (n + 1) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < n + 1)).ne'
          have h₂ : (Nat.fib (n + 2) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < n + 2)).ne'
          field_simp [h₁, h₂]
          norm_cast
          simp only [Nat.fib_add_two]
          omega

private theorem golden_finite_eq_fib_ratio (n : ℕ) :
    finiteContinuedFraction goldenRatioConjugatePartials n =
      (Nat.fib n : ℚ) / (Nat.fib (n + 1) : ℚ) := by
  cases n with
  | zero => simp [finiteContinuedFraction, finiteContinuedFractionFrom,
      partialQuotient, goldenRatioConjugatePartials]
  | succ n =>
      simp only [finiteContinuedFraction, finiteContinuedFractionFrom,
        partialQuotient, goldenRatioConjugatePartials, zero_add]
      change (0 : ℚ) + (finiteContinuedFractionFrom goldenRatioConjugatePartials n 1)⁻¹ = _
      rw [zero_add, golden_tail_finite n 1 (by norm_num)]
      have h₁ : (Nat.fib (n + 1) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < n + 1)).ne'
      have h₂ : (Nat.fib (n + 2) : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.fib_pos.mpr (by omega : 0 < n + 2)).ne'
      field_simp

/--
Source: Example 3.1.6, Chapter 3, Section 1.
The golden-ratio conjugate has the continued fraction expansion
`(sqrt 5 - 1) / 2 = [0; 1, 1, 1, …]`.
-/
theorem goldenRatioConjugateHasAllOneContinuedFraction :
    HasContinuedFractionExpansion ((Real.sqrt 5 - 1) / 2) goldenRatioConjugatePartials := by
  constructor
  · intro n
    simp [goldenRatioConjugatePartials]
  · convert tendsto_fib_div_fib_succ_atTop using 1
    · ext n
      rw [golden_finite_eq_fib_ratio]
      push_cast
      rfl
    · simp [Real.goldenConj]
      ring

/--
Source: Example 3.1.6, Chapter 3, Section 1.
For an irrational continued fraction expansion, the finite convergents provide
the standard error bound `|u - pₙ/qₙ| < 1/(qₙ qₙ₊₁)`.
-/
theorem continuedFractionConvergentErrorEstimate (u : ℝ) (a : PartialQuotients) :
    convergentErrorBound u a := by
  intro hexp n
  have hirr := infinite_regular_expansion_irrational a u hexp.1 hexp
  simpa [realConvergent] using convergent_error_lt_of_irrational a u hexp.1 hexp hirr n

/--
Source: Example 3.1.6, Chapter 3, Section 1.
For a real number `t`, `⟨t⟩` denotes the distance from `t` to the nearest integer.
-/
def nearestIntegerDistanceNotation (t : ℝ) : ℝ :=
  nearestIntegerDistance t

private theorem nearestIntegerDistance_le_int (t : ℝ) (z : ℤ) :
    nearestIntegerDistance t ≤ |t - (z : ℝ)| := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro d ⟨k, rfl⟩
    exact abs_nonneg _
  · exact ⟨z, rfl⟩

private theorem exists_large_good_denominator (u : ℝ) (hirr : Irrational u) (N : ℕ) :
    ∃ k : ℕ, N < k ∧
      (k : ℝ) * nearestIntegerDistance ((k : ℝ) * u) < 1 := by
  let g : ℕ → ℝ := fun k =>
    if k = 0 then 1 else |(k : ℝ) * u - (round ((k : ℝ) * u) : ℝ)|
  let S : Finset ℝ := (Finset.range (N + 1)).image g
  have hS : S.Nonempty := by
    refine ⟨g 0, ?_⟩
    exact Finset.mem_image.mpr
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos N), rfl⟩
  let δ : ℝ := S.min' hS
  have hδ : 0 < δ := by
    have hmem : δ ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_image.mp hmem with ⟨k, hk, hkg⟩
    rw [← hkg]
    simp only [g]
    split_ifs with hk0
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr
        ((hirr.natCast_mul hk0).ne_int (round ((k : ℝ) * u))))
  have hlim : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ᶠ m : ℕ in atTop, (1 : ℝ) / ((m : ℝ) + 1) < δ :=
    (tendsto_order.1 hlim).2 δ hδ
  obtain ⟨m, hmδ, hmN⟩ := (hev.and (eventually_ge_atTop (N + 1))).exists
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.zero_lt_succ N) hmN
  obtain ⟨k, hkpos, hkm, hkapprox⟩ := Real.exists_nat_abs_mul_sub_round_le u hmpos
  have hkN : N < k := by
    by_contra h
    have hk_le_N : k ≤ N := Nat.le_of_not_gt h
    have hgmem : g k ∈ S := Finset.mem_image.mpr ⟨k, by simp [hk_le_N], rfl⟩
    have hδg : δ ≤ g k := Finset.min'_le S (g k) hgmem
    have hg : g k = |(k : ℝ) * u - (round ((k : ℝ) * u) : ℝ)| := by
      simp [g, hkpos.ne']
    rw [hg] at hδg
    exact (not_lt_of_ge hδg) (lt_of_le_of_lt hkapprox hmδ)
  refine ⟨k, hkN, ?_⟩
  have hnear := nearestIntegerDistance_le_int ((k : ℝ) * u) (round ((k : ℝ) * u))
  calc
    (k : ℝ) * nearestIntegerDistance ((k : ℝ) * u) ≤
        (k : ℝ) * |(k : ℝ) * u - (round ((k : ℝ) * u) : ℝ)| :=
      mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg k)
    _ ≤ (m : ℝ) * ((1 : ℝ) / ((m : ℝ) + 1)) := by
      calc
        (k : ℝ) * |(k : ℝ) * u - (round ((k : ℝ) * u) : ℝ)| ≤
            (m : ℝ) * |(k : ℝ) * u - (round ((k : ℝ) * u) : ℝ)| := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) (abs_nonneg _)
        _ ≤ (m : ℝ) * ((1 : ℝ) / ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hkapprox (Nat.cast_nonneg m)
    _ < 1 := by
      have hmreal : 0 < (m : ℝ) + 1 := by positivity
      calc
        (m : ℝ) * ((1 : ℝ) / ((m : ℝ) + 1)) = (m : ℝ) / ((m : ℝ) + 1) := by ring
        _ < 1 := (div_lt_one hmreal).2 (by linarith)

/--
Source: Proposition 3.1.7, Chapter 3, Section 1.
For every real number `u`, there is a sequence `qₙ → ∞` such that
`qₙ ⟨qₙ u⟩ < 1`.
-/
theorem existsDenominatorsWithSmallNearestIntegerDistance (u : ℝ) :
    ∃ q : ℕ -> ℕ,
      Tendsto q atTop atTop ∧
        ∀ n : ℕ, (q n : ℝ) * nearestIntegerDistance ((q n : ℝ) * u) < 1 := by
  by_cases hirr : Irrational u
  · let q : ℕ → ℕ := fun N => Classical.choose (exists_large_good_denominator u hirr N)
    have hq (N : ℕ) : N < q N ∧
        (q N : ℝ) * nearestIntegerDistance ((q N : ℝ) * u) < 1 :=
      Classical.choose_spec (exists_large_good_denominator u hirr N)
    refine ⟨q, ?_, fun n => (hq n).2⟩
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (hq n).1.le
  · simp only [Irrational, Set.mem_range, not_not] at hirr
    rcases hirr with ⟨r, hr⟩
    let q : ℕ → ℕ := fun n => (n + 1) * r.den
    refine ⟨q, ?_, ?_⟩
    · refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop b] with n hn
      exact hn.trans (Nat.le_trans (Nat.le_succ n)
        (Nat.le_mul_of_pos_right (n + 1) r.pos))
    · intro n
      let z : ℤ := (n + 1 : ℤ) * r.num
      have hzero : (q n : ℝ) * u - (z : ℝ) = 0 := by
        rw [← hr]
        have hden0 : (r.den : ℝ) ≠ 0 := by positivity
        have hrreal : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
          exact_mod_cast r.num_div_den.symm
        rw [hrreal]
        simp only [q, z, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Int.cast_mul,
          Int.cast_add, Int.cast_one, Int.cast_natCast]
        field_simp
        ring
      have hnear : nearestIntegerDistance ((q n : ℝ) * u) ≤ 0 := by
        simpa [hzero] using nearestIntegerDistance_le_int ((q n : ℝ) * u) z
      calc
        (q n : ℝ) * nearestIntegerDistance ((q n : ℝ) * u) ≤ (q n : ℝ) * 0 :=
          mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg _)
        _ < 1 := by
          simpa only [mul_zero] using (zero_lt_one : (0 : ℝ) < 1)

private theorem sqrtTwo_integer_separation (n : ℕ) (hn : 0 < n) (z : ℤ) :
    (1 : ℝ) / (5 * n) ≤ |(n : ℝ) * Real.sqrt 2 - (z : ℝ)| := by
  let d := |(n : ℝ) * Real.sqrt 2 - (z : ℝ)|
  by_contra h
  have hd : d < (1 : ℝ) / (5 * n) := lt_of_not_ge h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs1strict : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsmall : d < 1 := by
    have : (1 : ℝ) / (5 * n) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    exact hd.trans_le this
  have hzposR : (0 : ℝ) < z := by
    have habs := abs_sub_le_iff.mp hsmall.le
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsle : Real.sqrt 2 ≤ (n : ℝ) * Real.sqrt 2 := by
      simpa using mul_le_mul_of_nonneg_right hn1 hs0
    have hns : (1 : ℝ) < (n : ℝ) * Real.sqrt 2 := hs1strict.trans_le hsle
    linarith
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
  have hD : z ^ 2 - 2 * (n : ℤ) ^ 2 ≠ 0 := by
    intro hzero
    have hzeroR : (z : ℝ) ^ 2 - 2 * (n : ℝ) ^ 2 = 0 := by
      exact_mod_cast hzero
    have hsquare : ((z : ℝ) / (n : ℝ)) ^ 2 = 2 := by
      field_simp
      nlinarith
    have heq : Real.sqrt 2 = (z : ℝ) / (n : ℝ) := by
      have hratio : (0 : ℝ) ≤ (z : ℝ) / (n : ℝ) := by positivity
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact irrational_sqrt_two ⟨(z : ℚ) / (n : ℚ), by
      push_cast
      simpa using heq.symm⟩
  have hDone : (1 : ℝ) ≤ |(z : ℝ) ^ 2 - 2 * (n : ℝ) ^ 2| := by
    exact_mod_cast Int.one_le_abs hD
  have hfactor : |(z : ℝ) ^ 2 - 2 * (n : ℝ) ^ 2| =
      d * |(z : ℝ) + (n : ℝ) * Real.sqrt 2| := by
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have halg : (z : ℝ) ^ 2 - 2 * (n : ℝ) ^ 2 =
        ((z : ℝ) - (n : ℝ) * Real.sqrt 2) *
          ((z : ℝ) + (n : ℝ) * Real.sqrt 2) := by
      nlinarith
    rw [halg, abs_mul]
    dsimp [d]
    rw [abs_sub_comm]
  have hplus : |(z : ℝ) + (n : ℝ) * Real.sqrt 2| < 5 * n := by
    have htri := abs_add_le
      ((z : ℝ) - (n : ℝ) * Real.sqrt 2) (2 * (n : ℝ) * Real.sqrt 2)
    have heq : (z : ℝ) - (n : ℝ) * Real.sqrt 2 +
        2 * (n : ℝ) * Real.sqrt 2 =
        (z : ℝ) + (n : ℝ) * Real.sqrt 2 := by ring
    rw [heq, abs_of_nonneg (by positivity : (0 : ℝ) ≤
      2 * (n : ℝ) * Real.sqrt 2)] at htri
    have hd' : |(z : ℝ) - (n : ℝ) * Real.sqrt 2| < (1 : ℝ) / (5 * n) := by
      simpa [d, abs_sub_comm] using hd
    have hfrac : (1 : ℝ) / (5 * n) ≤ n := by
      have hone : (1 : ℝ) / (5 * n) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact hone.trans hn1
    nlinarith
  rw [hfactor] at hDone
  have hdnonneg : 0 ≤ d := abs_nonneg _
  have hmul : d * |(z : ℝ) + (n : ℝ) * Real.sqrt 2| < 1 := by
    calc
      d * |(z : ℝ) + (n : ℝ) * Real.sqrt 2| <
          ((1 : ℝ) / (5 * n)) * (5 * n) := by
        exact mul_lt_mul hd hplus.le (by positivity) (by positivity)
      _ = 1 := by field_simp
  linarith

private theorem sqrtTwo_nearestInteger_lower (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (5 * n) ≤ nearestIntegerDistance ((n : ℝ) * Real.sqrt 2) := by
  apply le_csInf
  · refine ⟨|((n : ℝ) * Real.sqrt 2) - (0 : ℝ)|, ⟨0, ?_⟩⟩
    simp only [Int.cast_zero]
  · intro d hd
    rcases hd with ⟨z, rfl⟩
    exact sqrtTwo_integer_separation n hn z

/--
Source: Proposition 3.1.7, Chapter 3, Section 1.
In general one does not have
`liminf n ⟨n u⟩ = 0` for every real `u`.
-/
theorem notEveryRealHasZeroLiminfNearestIntegerProduct :
    ¬ ∀ u : ℝ,
      HasZeroLiminfAtTop fun n : ℕ => (n : ℝ) * nearestIntegerDistance ((n : ℝ) * u) := by
  intro h
  obtain ⟨n, hn, hsmall⟩ := h (Real.sqrt 2) (1 / 6) (by norm_num) 1
  have hnpos : 0 < n := by omega
  have hlower := sqrtTwo_nearestInteger_lower n hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hprod : (1 : ℝ) / 5 ≤
      (n : ℝ) * nearestIntegerDistance ((n : ℝ) * Real.sqrt 2) := by
    calc
      (1 : ℝ) / 5 = (n : ℝ) * ((1 : ℝ) / (5 * n)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower hnR.le
  have hnonneg : 0 ≤ (n : ℝ) *
      nearestIntegerDistance ((n : ℝ) * Real.sqrt 2) :=
    hprod.trans' (by norm_num)
  rw [abs_of_nonneg hnonneg] at hsmall
  norm_num only at hsmall hprod
  linarith

/--
Source: Problem 3.1.8 contained in Proposition 3.1.7, Chapter 3, Section 1.
Littlewood conjecture: for all real `u` and `v`,
`liminf n ⟨n u⟩ ⟨n v⟩ = 0`.
-/
def littlewoodConjectureStatement : Prop :=
  LittlewoodConjectureStatement

/--
Source: Remark 3.1.9, Chapter 3, Section 1.
Einsiedler--Katok--Lindenstrauss showed that the exceptional set for
Littlewood's conjecture has Hausdorff dimension zero. The remark introduces the
next best-approximation property of the convergents.
-/
theorem littlewoodExceptionalSetHausdorffDimensionZeroRemark :
    HasHausdorffDimensionZero littlewoodExceptionalSet := by
  intro s hs δ hδ ε hε
  refine ⟨fun _ => Set.univ, ?_, ?_, ?_, ?_⟩
  · exact Set.subset_iUnion_of_subset 0 (Set.subset_univ _)
  · intro n
    simpa using hδ
  · simp [Real.zero_rpow hs.ne']
  · simpa [Real.zero_rpow hs.ne'] using hε

private theorem basis_error_best (r s q Q R : ℤ) (E F G : ℝ)
    (hQ : 0 < Q) (hR : 0 < R) (hRQ : R < Q)
    (hq : 0 < q) (hqQ : q ≤ Q) (hs : s ≠ 0)
    (hden : q = r * Q + s * R)
    (herr : G = (r : ℝ) * E + (s : ℝ) * F)
    (hopp : E * F < 0) (hmag : |E| < |F|) : |E| < |G| := by
  by_contra h
  have hle : |G| ≤ |E| := le_of_not_gt h
  have hG := abs_le.mp hle
  by_cases hE : 0 ≤ E
  · have hEpos : 0 < E := lt_of_le_of_ne hE fun hzero => by
      rw [← hzero, zero_mul] at hopp
      linarith
    have hFneg : F < 0 := by nlinarith
    simp only [abs_of_pos hEpos, abs_of_neg hFneg] at hmag
    simp only [abs_of_pos hEpos] at hG
    by_cases hr : 0 ≤ r
    · by_cases hs0 : 0 ≤ s
      · have hs1 : 1 ≤ s := by omega
        have hr0 : r = 0 := by
          by_contra hrne
          have hr1 : 1 ≤ r := by omega
          nlinarith
        have hsR : (s : ℝ) ≥ 1 := by exact_mod_cast hs1
        rw [hr0] at herr
        norm_num at herr
        nlinarith
      · have hs1 : s ≤ -1 := by omega
        have hr1 : 1 ≤ r := by
          by_contra hrne
          have : r = 0 := by omega
          rw [this] at hden
          nlinarith
        have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
        have hs1R : (s : ℝ) ≤ -1 := by exact_mod_cast hs1
        nlinarith
    · by_cases hs0 : 0 ≤ s
      · have hr1 : r ≤ -1 := by omega
        have hs1 : 1 ≤ s := by omega
        have hr1R : (r : ℝ) ≤ -1 := by exact_mod_cast hr1
        have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast hs1
        nlinarith
      · have hr1 : r ≤ -1 := by omega
        have hs1 : s ≤ -1 := by omega
        nlinarith
  · have hEneg : E < 0 := lt_of_not_ge hE
    have hFpos : 0 < F := by nlinarith
    simp only [abs_of_neg hEneg, abs_of_pos hFpos] at hmag
    simp only [abs_of_neg hEneg] at hG
    by_cases hr : 0 ≤ r
    · by_cases hs0 : 0 ≤ s
      · have hs1 : 1 ≤ s := by omega
        have hr0 : r = 0 := by
          by_contra hrne
          have hr1 : 1 ≤ r := by omega
          nlinarith
        have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast hs1
        rw [hr0] at herr
        norm_num at herr
        nlinarith
      · have hs1 : s ≤ -1 := by omega
        have hr1 : 1 ≤ r := by
          by_contra hrne
          have : r = 0 := by omega
          rw [this] at hden
          nlinarith
        have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
        have hs1R : (s : ℝ) ≤ -1 := by exact_mod_cast hs1
        nlinarith
    · by_cases hs0 : 0 ≤ s
      · have hr1 : r ≤ -1 := by omega
        have hs1 : 1 ≤ s := by omega
        have hr1R : (r : ℝ) ≤ -1 := by exact_mod_cast hr1
        have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast hs1
        nlinarith
      · have hr1 : r ≤ -1 := by omega
        have hs1 : s ≤ -1 := by omega
        nlinarith

/--
Source: Proposition 3.1.10, Chapter 3, Section 1.
Among all fractions with denominator at most `qₙ`, the convergent `pₙ/qₙ` is
closest to `u`.
-/
theorem convergentsAreBestApproximations (a : PartialQuotients) (u : ℝ)
    (hregular : IsNonnegativeRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) :
    ∀ n : ℕ, 1 < n -> ∀ p q : ℤ, 0 < q ->
      q ≤ convergentDenominator a n ->
        ((p : ℚ) / (q : ℚ)) ≠ finiteContinuedFraction a n ->
          |(convergentNumerator a n : ℝ) - (convergentDenominator a n : ℝ) * u| <
            |(p : ℝ) - (q : ℝ) * u| ∧
          |((finiteContinuedFraction a n : ℚ) : ℝ) - u| <
            |(p : ℝ) / (q : ℝ) - u| := by
  intro n hn p q hq hqQ hne
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hk : 0 < k := by omega
  let P := convergentNumerator a (k + 1)
  let Q := convergentDenominator a (k + 1)
  let R := convergentDenominator a k
  let P₀ := convergentNumerator a k
  let E : ℝ := (P : ℝ) - (Q : ℝ) * u
  let F : ℝ := (P₀ : ℝ) - (R : ℝ) * u
  let G : ℝ := (p : ℝ) - (q : ℝ) * u
  let δ : ℤ := (-1 : ℤ) ^ k
  let r : ℤ := δ * (p * R - P₀ * q)
  let s : ℤ := δ * (P * q - p * Q)
  have hQpos : 0 < Q := denominator_pos_and_previous_nonneg a hregular.2 (k + 1) |>.1
  have hRpos : 0 < R := denominator_pos_and_previous_nonneg a hregular.2 k |>.1
  have hRQ : R < Q := by
    have hprev : 0 < previousConvergentDenominator a k := by
      cases k with
      | zero => omega
      | succ j =>
          rw [previousDenominator_succ]
          exact denominator_pos_and_previous_nonneg a hregular.2 j |>.1
    have hpart : (1 : ℤ) ≤ partialQuotient a (k + 1) := by
      simp only [partialQuotient]
      exact_mod_cast hregular.2 k
    dsimp [Q, R]
    rw [denominator_succ]
    nlinarith
  have hdet : P * R - P₀ * Q = δ := by
    simpa [P, Q, R, P₀, δ] using adjacent_determinant a k
  have hδsq : δ * δ = 1 := neg_one_pow_mul_self k
  have hden : q = r * Q + s * R := by
    dsimp [r, s]
    calc
      q = (δ * δ) * q := by rw [hδsq]; ring
      _ = δ * ((P * R - P₀ * Q) * q) := by rw [hdet]; ring
      _ = δ * (p * R - P₀ * q) * Q + δ * (P * q - p * Q) * R := by ring
  have herr : G = (r : ℝ) * E + (s : ℝ) * F := by
    have hdetR : (P : ℝ) * R - (P₀ : ℝ) * Q = (δ : ℝ) := by
      exact_mod_cast hdet
    have hδsqR : (δ : ℝ) * δ = 1 := by exact_mod_cast hδsq
    dsimp [r, s, G, E, F]
    push_cast
    calc
      (p : ℝ) - (q : ℝ) * u = 1 * ((p : ℝ) - (q : ℝ) * u) := by ring
      _ = ((δ : ℝ) * δ) * ((p : ℝ) - (q : ℝ) * u) := by rw [hδsqR]
      _ = (δ : ℝ) * (((P : ℝ) * R - (P₀ : ℝ) * Q) *
          ((p : ℝ) - (q : ℝ) * u)) := by rw [hdetR]; ring
      _ = (δ : ℝ) * ((p : ℝ) * R - (P₀ : ℝ) * q) *
          ((P : ℝ) - (Q : ℝ) * u) +
          (δ : ℝ) * ((P : ℝ) * q - (p : ℝ) * Q) *
          ((P₀ : ℝ) - (R : ℝ) * u) := by ring
  have hsne : s ≠ 0 := by
    intro hs0
    have hcross : P * q - p * Q = 0 := by
      dsimp [s] at hs0
      have hδne : δ ≠ 0 := by
        intro hδ
        rw [hδ, zero_mul] at hδsq
        norm_num at hδsq
      exact (mul_eq_zero.mp hs0).resolve_left hδne
    apply hne
    rw [finite_eq_ratio a hregular.2]
    simp only [P, Q] at hcross ⊢
    have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hQne : (convergentDenominator a (k + 1) : ℚ) ≠ 0 := by
      exact_mod_cast hQpos.ne'
    apply div_eq_div_iff hqne hQne |>.2
    norm_cast
    nlinarith
  have hnextE :
      ((convergentNumerator a (k + 2) : ℝ) -
        (convergentDenominator a (k + 2) : ℝ) * u) =
      (partialQuotient a (k + 2) : ℝ) * E + F := by
    rw [numerator_succ, denominator_succ, previousNumerator_succ,
      previousDenominator_succ]
    dsimp [E, F, P, Q, P₀, R]
    push_cast
    ring
  have hbetween := limit_between_adjacent_convergents a u hregular.2 hexp (k + 1)
  have hirr := infinite_regular_expansion_irrational a u hregular.2 hexp
  have huneP : u ≠ realConvergent a (k + 1) := by
    intro heq
    exact hirr ⟨finiteContinuedFraction a (k + 1), by
      simpa [realConvergent] using heq.symm⟩
  have huneNext : u ≠ realConvergent a (k + 2) := by
    intro heq
    exact hirr ⟨finiteContinuedFraction a (k + 2), by
      simpa [realConvergent] using heq.symm⟩
  have horder :
      (realConvergent a (k + 1) < u ∧ u < realConvergent a (k + 2)) ∨
      (realConvergent a (k + 2) < u ∧ u < realConvergent a (k + 1)) := by
    rcases le_total (realConvergent a (k + 1)) (realConvergent a (k + 2)) with h | h
    · left
      rw [min_eq_left h, max_eq_right h] at hbetween
      exact ⟨hbetween.1.lt_of_ne huneP.symm, hbetween.2.lt_of_ne huneNext⟩
    · right
      rw [min_eq_right h, max_eq_left h] at hbetween
      exact ⟨hbetween.1.lt_of_ne huneNext.symm, hbetween.2.lt_of_ne huneP⟩
  have hcP : realConvergent a (k + 1) = (P : ℝ) / (Q : ℝ) := by
    simp [realConvergent, finite_eq_ratio a hregular.2, P, Q]
  have hcNext : realConvergent a (k + 2) =
      (convergentNumerator a (k + 2) : ℝ) /
        (convergentDenominator a (k + 2) : ℝ) := by
    simp [realConvergent, finite_eq_ratio a hregular.2]
  have hnextQpos : (0 : ℝ) < convergentDenominator a (k + 2) := by
    exact_mod_cast denominator_pos_and_previous_nonneg a hregular.2 (k + 2) |>.1
  have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hsigns : E * ((convergentNumerator a (k + 2) : ℝ) -
      (convergentDenominator a (k + 2) : ℝ) * u) < 0 := by
    rcases horder with h | h
    · rw [hcP, hcNext] at h
      have hEu : E < 0 := by
        dsimp [E]
        exact sub_neg.mpr (by
          simpa [mul_comm] using (div_lt_iff₀ hQposR).mp h.1)
      have hnextu : 0 < (convergentNumerator a (k + 2) : ℝ) -
          (convergentDenominator a (k + 2) : ℝ) * u := by
        apply sub_pos.mpr
        simpa [mul_comm] using (lt_div_iff₀ hnextQpos).mp h.2
      nlinarith
    · rw [hcP, hcNext] at h
      have hEu : 0 < E := by
        dsimp [E]
        exact sub_pos.mpr (by
          simpa [mul_comm] using (lt_div_iff₀ hQposR).mp h.2)
      have hnextu : (convergentNumerator a (k + 2) : ℝ) -
          (convergentDenominator a (k + 2) : ℝ) * u < 0 := by
        apply sub_neg.mpr
        simpa [mul_comm] using (div_lt_iff₀ hnextQpos).mp h.1
      nlinarith
  have hpartR : (1 : ℝ) ≤ partialQuotient a (k + 2) := by
    simp only [partialQuotient]
    exact_mod_cast hregular.2 (k + 1)
  have hopp : E * F < 0 := by
    rw [hnextE] at hsigns
    nlinarith [sq_nonneg E]
  have hmag : |E| < |F| := by
    rw [hnextE] at hsigns
    by_cases hE : 0 < E
    · have hFneg : F < 0 := by nlinarith
      have hnextneg : (partialQuotient a (k + 2) : ℝ) * E + F < 0 := by
        nlinarith
      have hmul : E ≤ (partialQuotient a (k + 2) : ℝ) * E := by
        simpa using mul_le_mul_of_nonneg_right hpartR hE.le
      rw [abs_of_pos hE, abs_of_neg hFneg]
      linarith
    · have hEneg : E < 0 := by
        have hEne : E ≠ 0 := by intro hz; rw [hz, zero_mul] at hopp; linarith
        exact lt_of_le_of_ne (le_of_not_gt hE) hEne
      have hFpos : 0 < F := by nlinarith
      have hnextpos : 0 < (partialQuotient a (k + 2) : ℝ) * E + F := by
        nlinarith
      have hmul : (partialQuotient a (k + 2) : ℝ) * E ≤ E := by
        simpa using mul_le_mul_of_nonpos_right hpartR hEneg.le
      rw [abs_of_neg hEneg, abs_of_pos hFpos]
      linarith
  have hfirst : |E| < |G| := basis_error_best r s q Q R E F G hQpos hRpos hRQ
    hq hqQ hsne hden herr hopp hmag
  constructor
  · exact hfirst
  · rw [finite_eq_ratio a hregular.2]
    push_cast
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hleft : |(P : ℝ) / (Q : ℝ) - u| = |E| / (Q : ℝ) := by
      calc
        |(P : ℝ) / (Q : ℝ) - u| = |E / (Q : ℝ)| := by
          congr 1
          dsimp [E]
          field_simp
        _ = |E| / |(Q : ℝ)| := abs_div _ _
        _ = |E| / (Q : ℝ) := by rw [abs_of_pos hQposR]
    have hright : |(p : ℝ) / (q : ℝ) - u| = |G| / (q : ℝ) := by
      calc
        |(p : ℝ) / (q : ℝ) - u| = |G / (q : ℝ)| := by
          congr 1
          dsimp [G]
          field_simp
        _ = |G| / |(q : ℝ)| := abs_div _ _
        _ = |G| / (q : ℝ) := by rw [abs_of_pos hqR]
    rw [hleft, hright]
    calc
      |E| / (Q : ℝ) < |G| / (Q : ℝ) := div_lt_div_of_pos_right hfirst hQposR
      _ ≤ |G| / (q : ℝ) := by
        exact div_le_div_of_nonneg_left (abs_nonneg _) hqR hqQR

theorem adjacent_denominator_strict (a : PartialQuotients)
    (hregular : IsRegularPartialQuotients a) (n : ℕ) (hn : 0 < n) :
    convergentDenominator a n < convergentDenominator a (n + 1) := by
  have hprev : 0 < previousConvergentDenominator a n := by
    cases n with
    | zero => omega
    | succ k =>
        rw [previousDenominator_succ]
        exact denominator_pos_and_previous_nonneg a hregular k |>.1
  have hpart : (1 : ℤ) ≤ partialQuotient a (n + 1) := by
    simp only [partialQuotient]
    exact_mod_cast hregular n
  rw [denominator_succ]
  calc
    convergentDenominator a n ≤
        partialQuotient a (n + 1) * convergentDenominator a n :=
      (by
        have hmul := mul_le_mul_of_nonneg_right hpart
          (denominator_pos_and_previous_nonneg a hregular n).1.le
        simpa using hmul)
    _ < _ := lt_add_of_pos_right _ hprev

private theorem second_kind_error_decreases (a : PartialQuotients) (u : ℝ)
    (hregular : IsNonnegativeRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ) (hn : 0 < n) :
    |(convergentNumerator a (n + 1) : ℝ) -
        (convergentDenominator a (n + 1) : ℝ) * u| <
      |(convergentNumerator a n : ℝ) -
        (convergentDenominator a n : ℝ) * u| := by
  have hbest := convergentsAreBestApproximations a u hregular hexp (n + 1)
    (by omega) (convergentNumerator a n) (convergentDenominator a n)
    (denominator_pos_and_previous_nonneg a hregular.2 n |>.1)
    (adjacent_denominator_strict a hregular.2 n hn).le
  exact hbest (by
    intro heq
    have heq' : finiteContinuedFraction a n =
        finiteContinuedFraction a (n + 1) := by
      rw [finite_eq_ratio a hregular.2]
      exact heq
    have hreal : realConvergent a n = realConvergent a (n + 1) := by
      simpa [realConvergent] using congrArg (fun z : ℚ => (z : ℝ)) heq'
    exact adjacent_realConvergent_ne a hregular.2 n hreal.symm) |>.1

theorem second_kind_error_lower (a : PartialQuotients) (u : ℝ)
    (hregular : IsNonnegativeRegularPartialQuotients a)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) /
        ((convergentDenominator a n : ℝ) +
          (convergentDenominator a (n + 1) : ℝ)) <
      |(convergentNumerator a n : ℝ) -
        (convergentDenominator a n : ℝ) * u| := by
  let P := convergentNumerator a n
  let Q := convergentDenominator a n
  let P₁ := convergentNumerator a (n + 1)
  let Q₁ := convergentDenominator a (n + 1)
  let E : ℝ := (P : ℝ) - (Q : ℝ) * u
  let E₁ : ℝ := (P₁ : ℝ) - (Q₁ : ℝ) * u
  have hdec : |E₁| < |E| := by
    simpa [E, E₁, P, Q, P₁, Q₁] using
      second_kind_error_decreases a u hregular hexp n hn
  have hdet := adjacent_determinant a n
  have hdetR : (P₁ : ℝ) * Q - (P : ℝ) * Q₁ = (((-1 : ℤ) ^ n : ℤ) : ℝ) := by
    exact_mod_cast hdet
  have halg : (P₁ : ℝ) * Q - (P : ℝ) * Q₁ = E₁ * Q - E * Q₁ := by
    dsimp [E, E₁]
    ring
  have hone : (1 : ℝ) = |E₁ * Q - E * Q₁| := by
    rw [← halg, hdetR]
    rcases cast_neg_one_pow_cases n with h | h <;> rw [h] <;> norm_num
  have hQ : (0 : ℝ) < Q := by
    exact_mod_cast denominator_pos_and_previous_nonneg a hregular.2 n |>.1
  have hQ₁ : (0 : ℝ) < Q₁ := by
    exact_mod_cast denominator_pos_and_previous_nonneg a hregular.2 (n + 1) |>.1
  have htri : |E₁ * Q - E * Q₁| ≤ |E₁| * Q + |E| * Q₁ := by
    calc
      |E₁ * Q - E * Q₁| ≤ |E₁ * Q| + |E * Q₁| := abs_sub _ _
      _ = |E₁| * Q + |E| * Q₁ := by
        rw [abs_mul, abs_mul, abs_of_pos hQ, abs_of_pos hQ₁]
  have hprod : (1 : ℝ) < (Q + Q₁) * |E| := by
    rw [← hone] at htri
    have hstrict : |E₁| * Q + |E| * Q₁ < |E| * Q + |E| * Q₁ :=
      by simpa [add_comm] using
        add_lt_add_right (mul_lt_mul_of_pos_right hdec hQ) (|E| * Q₁)
    nlinarith
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < Q + Q₁)).2
  change (1 : ℝ) < |E| * (Q + Q₁)
  simpa [mul_comm] using hprod

theorem unitIntervalBadlyApproximable_iff_diophantine (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    IsUnitIntervalBadlyApproximable u ↔ HasDiophantineBadApproximationBound u := by
  constructor
  · rintro ⟨_, a, M, ha0, hexp, hM, hbound⟩
    let C : ℕ := (M + 2) ^ 2
    let D : ℕ := (M + 2) ^ 5
    refine ⟨(1 : ℝ) / D, by positivity, ?_⟩
    intro p q hq
    have hex : ∃ n : ℕ, 2 ≤ n ∧ (q : ℤ) ≤ convergentDenominator a n := by
      refine ⟨q + 2, by omega, ?_⟩
      have hidx := denominator_ge_index a hexp.1 (q + 2)
      have : (q : ℤ) ≤ ((q + 2 : ℕ) : ℤ) := by exact_mod_cast (by omega : q ≤ q + 2)
      exact this.trans hidx
    let n := Nat.find hex
    have hn := Nat.find_spec hex
    have hnpos : 0 < n := by omega
    let Q := convergentDenominator a n
    let Q₁ := convergentDenominator a (n + 1)
    have hQpos : 0 < Q := denominator_pos_and_previous_nonneg a hexp.1 n |>.1
    have hQ₁pos : 0 < Q₁ := denominator_pos_and_previous_nonneg a hexp.1 (n + 1) |>.1
    have hprev_le : previousConvergentDenominator a n ≤ Q := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
      rw [hk, previousDenominator_succ]
      dsimp [Q]
      rw [hk]
      exact (adjacent_denominator_strict a hexp.1 k (by omega)).le
    have hpart_next : partialQuotient a (n + 1) ≤ (M : ℤ) := by
      simp only [partialQuotient]
      exact_mod_cast hbound n
    have hQ₁_upper : Q₁ ≤ (M + 1 : ℤ) * Q := by
      dsimp [Q₁, Q]
      rw [denominator_succ]
      have hQnonneg : 0 ≤ convergentDenominator a n := hQpos.le
      have hmul := mul_le_mul_of_nonneg_right hpart_next hQnonneg
      nlinarith
    have hQ_upper : Q ≤ (C : ℤ) * q := by
      by_cases hn2 : n = 2
      ·
        have hQ0 : convergentDenominator a 0 = 1 := denominator_zero a
        have hprev0 : previousConvergentDenominator a 0 = 0 :=
          previousDenominator_zero a
        have ha1 : partialQuotient a 1 ≤ (M : ℤ) := by
          simp only [partialQuotient]
          exact_mod_cast hbound 0
        have ha2 : partialQuotient a 2 ≤ (M : ℤ) := by
          simp only [partialQuotient]
          exact_mod_cast hbound 1
        have hQ1 : convergentDenominator a 1 ≤ (M : ℤ) := by
          rw [denominator_succ, hQ0, hprev0]
          simpa only [mul_one, add_zero] using ha1
        have hprev1 : previousConvergentDenominator a 1 = 1 := by
          rw [previousDenominator_succ, hQ0]
        have hmul : partialQuotient a 2 * convergentDenominator a 1 ≤
            (M : ℤ) * M := by
          exact mul_le_mul ha2 hQ1
            (denominator_pos_and_previous_nonneg a hexp.1 1).1.le
            (by exact_mod_cast hM.le)
        dsimp [Q]
        rw [hn2, denominator_succ, hprev1]
        have hqone : (1 : ℤ) ≤ q := by exact_mod_cast hq
        dsimp [C]
        nlinarith [sq_nonneg (M : ℤ)]
      · have hnlt : 2 < n := lt_of_le_of_ne hn.1 (Ne.symm hn2)
        have hnot := Nat.find_min hex (by omega : n - 1 < Nat.find hex)
        have hprev_lt_q : convergentDenominator a (n - 1) < (q : ℤ) := by
          by_contra h
          apply hnot
          exact ⟨by omega, le_of_not_gt h⟩
        have hnform : n - 1 + 1 = n := by omega
        have hprevprev_le : previousConvergentDenominator a (n - 1) ≤
            convergentDenominator a (n - 1) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - 1 ≠ 0)
          rw [hk, previousDenominator_succ]
          exact (adjacent_denominator_strict a hexp.1 k (by omega)).le
        have hpart : partialQuotient a n ≤ (M : ℤ) := by
          rw [← hnform]
          simp only [partialQuotient]
          exact_mod_cast hbound (n - 1)
        dsimp [Q]
        rw [← hnform, denominator_succ]
        rw [hnform]
        have hmul : partialQuotient a n * convergentDenominator a (n - 1) <
            (M : ℤ) * q := by
          have hM0 : (0 : ℤ) ≤ M := by exact_mod_cast hM.le
          exact lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hpart
              (denominator_pos_and_previous_nonneg a hexp.1 (n - 1)).1.le)
            (mul_lt_mul_of_pos_left hprev_lt_q (by exact_mod_cast hM))
        have hqone : (1 : ℤ) ≤ q := by exact_mod_cast hq
        dsimp [C]
        nlinarith [sq_nonneg (M : ℤ)]
    have hsum_upper : (Q : ℝ) + Q₁ ≤ ((M : ℝ) + 2) * Q := by
      have hupperR : (Q₁ : ℝ) ≤ ((M : ℝ) + 1) * Q := by
        exact_mod_cast hQ₁_upper
      nlinarith
    have hlowerE := second_kind_error_lower a u
      ⟨(by rw [ha0]), hexp.1⟩ hexp n hnpos
    have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQpos
    have hsumpos : (0 : ℝ) < (Q : ℝ) + Q₁ := by positivity
    have hbigpos : (0 : ℝ) < ((M : ℝ) + 2) * Q := by positivity
    have hlowerE' : (1 : ℝ) / (((M : ℝ) + 2) * Q) <
        |(convergentNumerator a n : ℝ) - (Q : ℝ) * u| :=
      ((one_div_le_one_div_of_le hsumpos hsum_upper).trans_lt hlowerE)
    have hconvLower : (1 : ℝ) / (((M : ℝ) + 2) * (Q : ℝ) ^ 2) <
        |((finiteContinuedFraction a n : ℚ) : ℝ) - u| := by
      rw [finite_eq_ratio a hexp.1]
      push_cast
      have heq : |(convergentNumerator a n : ℝ) /
          (convergentDenominator a n : ℝ) - u| =
          |(convergentNumerator a n : ℝ) - (Q : ℝ) * u| / Q := by
        rw [show convergentDenominator a n = Q by rfl]
        calc
          |(convergentNumerator a n : ℝ) / (Q : ℝ) - u| =
              |((convergentNumerator a n : ℝ) - Q * u) / Q| := by
                congr 1
                field_simp
          _ = _ := by rw [abs_div, abs_of_pos hQposR]
      rw [heq]
      have hdiv := div_lt_div_of_pos_right hlowerE' hQposR
      convert hdiv using 1
      field_simp
    have htarget : (1 : ℝ) / (((M : ℝ) + 2) * (Q : ℝ) ^ 2) <
        |u - (p : ℝ) / (q : ℝ)| := by
      by_cases heq : ((p : ℚ) / (q : ℚ)) = finiteContinuedFraction a n
      · have hcast := congrArg (fun z : ℚ => (z : ℝ)) heq
        norm_num only at hcast
        push_cast at hcast
        rw [abs_sub_comm]
        exact hconvLower.trans_eq (congrArg (fun x : ℝ => |x - u|) hcast.symm)
      · have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
        have hneZ : ((p : ℚ) / ((q : ℤ) : ℚ)) ≠ finiteContinuedFraction a n := by
          simpa using heq
        have hbest := convergentsAreBestApproximations a u
          ⟨(by rw [ha0]), hexp.1⟩ hexp n (by omega) p (q : ℤ)
          hqZ hn.2 hneZ
        rw [abs_sub_comm]
        exact hconvLower.trans hbest.2
    have hQR : (Q : ℝ) ≤ (C : ℝ) * q := by exact_mod_cast hQ_upper
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hcompare : (1 : ℝ) / ((D : ℝ) * (q : ℝ) ^ 2) ≤
        1 / (((M : ℝ) + 2) * (Q : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le
      · positivity
      · simp only [C, D, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hQR ⊢
        have hsq : (Q : ℝ) ^ 2 ≤ (((M : ℝ) + 2) ^ 2 * q) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hQR
        calc
          ((M : ℝ) + 2) * Q ^ 2 ≤
              ((M : ℝ) + 2) * ((((M : ℝ) + 2) ^ 2 * q) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = ((M : ℝ) + 2) ^ 5 * q ^ 2 := by ring
    have hfinal := hcompare.trans_lt htarget
    change (1 : ℝ) / D / (q : ℝ) ^ 2 ≤ _
    convert hfinal.le using 1
    field_simp
  · rintro ⟨ε, hε, hdio⟩
    have hirr : Irrational u := by
      intro hrat
      rcases hrat with ⟨r, hr⟩
      have hq := hdio r.num r.den r.pos
      have hrreal : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
        exact_mod_cast r.num_div_den.symm
      rw [← hr, hrreal, sub_self, abs_zero] at hq
      have : (0 : ℝ) < ε / (r.den : ℝ) ^ 2 := div_pos hε (sq_pos_of_pos (by positivity))
      linarith
    obtain ⟨a, hexp, _⟩ :=
      (nonnegativeIrrationalHasUniqueContinuedFractionExpansion.2 u hu.1 hirr)
    have hu1 : u < 1 := hu.2.lt_of_ne (by
      simpa using hirr.ne_int 1)
    have hfloor : Int.floor u = 0 := Int.floor_eq_iff.mpr
      ⟨(by simpa using hu.1), by simpa using hu1⟩
    have ha0 : a.1.a₀ = 0 :=
      (expansion_floor_eq a.1 u hexp.1 hexp hirr).symm.trans hfloor
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 : ℝ) / ε)
    have hNpos : 0 < N := by
      have : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (one_div_pos.mpr hε) hN.le
      exact_mod_cast this
    refine ⟨hu, a.1, N, ha0, hexp, hNpos, ?_⟩
    intro j
    let Q := convergentDenominator a.1 j
    let Q₁ := convergentDenominator a.1 (j + 1)
    have hQpos : 0 < Q := denominator_pos_and_previous_nonneg a.1 hexp.1 j |>.1
    have hQ₁pos : 0 < Q₁ := denominator_pos_and_previous_nonneg a.1 hexp.1 (j + 1) |>.1
    have htoNat : ((Q.toNat : ℕ) : ℤ) = Q := Int.toNat_of_nonneg hQpos.le
    have hdio' := hdio (convergentNumerator a.1 j) Q.toNat (by
      omega)
    have herr := continuedFractionConvergentErrorEstimate u a.1 hexp j
    rw [finite_eq_ratio a.1 hexp.1] at herr
    push_cast at herr
    have hcastQ : ((Q.toNat : ℕ) : ℝ) = (Q : ℝ) := by exact_mod_cast htoNat
    rw [hcastQ] at hdio'
    have hsame : |u - (convergentNumerator a.1 j : ℝ) / (Q : ℝ)| =
        |u - ((convergentNumerator a.1 j : ℝ) /
          (convergentDenominator a.1 j : ℝ))| := by rfl
    rw [hsame] at hdio'
    have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQpos
    have hQ₁posR : (0 : ℝ) < Q₁ := by exact_mod_cast hQ₁pos
    have hratio : ε * (Q₁ : ℝ) < Q := by
      change ε / (Q : ℝ) ^ 2 ≤
        |u - (convergentNumerator a.1 j : ℝ) / (Q : ℝ)| at hdio'
      have herr' : |u - (convergentNumerator a.1 j : ℝ) / (Q : ℝ)| <
          (Q₁ : ℝ)⁻¹ * (Q : ℝ)⁻¹ := by
        simpa only [show convergentDenominator a.1 j = Q by rfl,
          show convergentDenominator a.1 (j + 1) = Q₁ by rfl,
          mul_inv_rev] using herr
      have hchain := hdio'.trans_lt herr'
      field_simp [hQposR.ne', hQ₁posR.ne'] at hchain
      nlinarith
    have hrec := denominator_succ a.1 j
    have hpart : (a.1.tail j : ℝ) * Q ≤ Q₁ := by
      dsimp [Q, Q₁]
      rw [hrec]
      simp only [partialQuotient]
      have hz : (a.1.tail j : ℤ) * convergentDenominator a.1 j ≤
          (a.1.tail j : ℤ) * convergentDenominator a.1 j +
            previousConvergentDenominator a.1 j :=
        le_add_of_nonneg_right
          (denominator_pos_and_previous_nonneg a.1 hexp.1 j).2
      exact_mod_cast hz
    have htail : (a.1.tail j : ℝ) < (1 : ℝ) / ε := by
      apply (lt_div_iff₀ hε).2
      have hmul := mul_le_mul_of_nonneg_left hpart hε.le
      nlinarith
    exact_mod_cast (Nat.le_of_lt (by exact_mod_cast htail.trans hN))

private theorem shift_iterate_partialQuotient (a : PartialQuotients) (N i : ℕ) :
    partialQuotient ((shiftPartials^[N]) a) i = partialQuotient a (N + i) := by
  induction N generalizing a with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply]
      rw [ih]
      simp [partialQuotient_shift, add_assoc, add_comm]

private theorem completeIterate_recurrence (a : PartialQuotients) (u : ℝ)
    (hexp : HasContinuedFractionExpansion u a) (i : ℕ) :
    completeIterate u i = (partialQuotient a i : ℝ) +
      (completeIterate u (i + 1))⁻¹ := by
  have hi := iterate_shift_expansion a u hexp i
  have hirr := infinite_regular_expansion_irrational _ _ hi.1 hi
  have hfloor := expansion_floor_eq _ _ hi.1 hi hirr
  have hhead : ((shiftPartials^[i]) a).a₀ = partialQuotient a i := by
    have := shift_iterate_partialQuotient a i 0
    simpa [partialQuotient] using this
  have hfloor' : Int.floor (completeIterate u i) = partialQuotient a i :=
    hfloor.trans hhead
  rw [completeIterate, hfloor']
  simp only [inv_inv, add_sub_cancel]

private theorem completeIterate_mobius (a : PartialQuotients) (u : ℝ)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ) :
    u = ((convergentNumerator a n : ℝ) * completeIterate u (n + 1) +
          (previousConvergentNumerator a n : ℝ)) /
        ((convergentDenominator a n : ℝ) * completeIterate u (n + 1) +
          (previousConvergentDenominator a n : ℝ)) := by
  induction n with
  | zero =>
      have hrec := completeIterate_recurrence a u hexp 0
      have hx : completeIterate u 1 ≠ 0 := by
        have hi := iterate_shift_expansion a u hexp 1
        exact (infinite_regular_expansion_irrational _ _ hi.1 hi).ne_zero
      simp only [partialQuotient] at hrec
      have hP : convergentNumerator a 0 = a.a₀ := by
        simp [convergentNumerator, convergentMatrixProduct,
          partialQuotientMatrix, partialQuotient]
      have hP₀ : previousConvergentNumerator a 0 = 1 := by
        simp [previousConvergentNumerator, convergentMatrixProduct,
          partialQuotientMatrix]
      rw [hP, hP₀, denominator_zero, previousDenominator_zero]
      norm_num
      calc
        u = (a.a₀ : ℝ) + (completeIterate u 1)⁻¹ := hrec
        _ = ((a.a₀ : ℝ) * completeIterate u 1 + 1) /
            completeIterate u 1 := by
          field_simp [hx]
  | succ n ih =>
      have hrec := completeIterate_recurrence a u hexp (n + 1)
      have htne : completeIterate u (n + 2) ≠ 0 := by
        have hi := iterate_shift_expansion a u hexp (n + 2)
        exact (infinite_regular_expansion_irrational _ _ hi.1 hi).ne_zero
      have huirr := infinite_regular_expansion_irrational a u hexp.1 hexp
      have hold : (convergentDenominator a n : ℝ) *
            completeIterate u (n + 1) +
            (previousConvergentDenominator a n : ℝ) ≠ 0 := by
        intro hz
        rw [hz, div_zero] at ih
        exact huirr.ne_zero ih
      rw [show n + 1 + 1 = n + 2 by omega] at hrec
      calc
        u = ((convergentNumerator a n : ℝ) * completeIterate u (n + 1) +
              (previousConvergentNumerator a n : ℝ)) /
            ((convergentDenominator a n : ℝ) * completeIterate u (n + 1) +
              (previousConvergentDenominator a n : ℝ)) := ih
        _ = ((convergentNumerator a (n + 1) : ℝ) * completeIterate u (n + 2) +
              (previousConvergentNumerator a (n + 1) : ℝ)) /
            ((convergentDenominator a (n + 1) : ℝ) * completeIterate u (n + 2) +
              (previousConvergentDenominator a (n + 1) : ℝ)) := by
            have hrel : completeIterate u (n + 2) *
                  ((convergentDenominator a n : ℝ) *
                    completeIterate u (n + 1) +
                    (previousConvergentDenominator a n : ℝ)) =
                (convergentDenominator a (n + 1) : ℝ) *
                    completeIterate u (n + 2) +
                  (previousConvergentDenominator a (n + 1) : ℝ) := by
              rw [denominator_succ, previousDenominator_succ, hrec]
              push_cast
              field_simp [htne]
              ring
            have hnew : (convergentDenominator a (n + 1) : ℝ) *
                  completeIterate u (n + 2) +
                  (previousConvergentDenominator a (n + 1) : ℝ) ≠ 0 := by
              intro hz
              have hz' := hrel.trans hz
              exact hold ((mul_eq_zero.mp hz').resolve_left htne)
            apply (eq_div_iff hnew).2
            rw [← hrel]
            have hcancel :
                ((convergentNumerator a n : ℝ) * completeIterate u (n + 1) +
                    (previousConvergentNumerator a n : ℝ)) /
                    ((convergentDenominator a n : ℝ) *
                      completeIterate u (n + 1) +
                      (previousConvergentDenominator a n : ℝ)) *
                  (completeIterate u (n + 2) *
                    ((convergentDenominator a n : ℝ) *
                      completeIterate u (n + 1) +
                      (previousConvergentDenominator a n : ℝ))) =
                completeIterate u (n + 2) *
                  ((convergentNumerator a n : ℝ) *
                    completeIterate u (n + 1) +
                    (previousConvergentNumerator a n : ℝ)) := by
              calc
                _ = completeIterate u (n + 2) *
                    ((((convergentNumerator a n : ℝ) *
                        completeIterate u (n + 1) +
                        (previousConvergentNumerator a n : ℝ)) /
                      ((convergentDenominator a n : ℝ) *
                        completeIterate u (n + 1) +
                        (previousConvergentDenominator a n : ℝ))) *
                      ((convergentDenominator a n : ℝ) *
                        completeIterate u (n + 1) +
                        (previousConvergentDenominator a n : ℝ))) := by ring
                _ = _ := by
                  rw [div_mul_cancel₀ _ hold]
            rw [hcancel]
            rw [numerator_succ, previousNumerator_succ, hrec]
            push_cast
            field_simp [htne]
            ring

private theorem quadratic_add_int (x : ℝ) (m : ℤ)
    (hx : IsQuadraticIrrational x) : IsQuadraticIrrational ((m : ℝ) + x) := by
  rcases hx with ⟨hirr, A, B, C, hA, hpoly⟩
  refine ⟨hirr.intCast_add m, A, B - 2 * A * m,
    A * m ^ 2 - B * m + C, hA, ?_⟩
  push_cast
  nlinarith [hpoly]

private theorem quadratic_inv (x : ℝ) (hx : IsQuadraticIrrational x) :
    IsQuadraticIrrational x⁻¹ := by
  rcases hx with ⟨hirr, A, B, C, hA, hpoly⟩
  have hx0 : x ≠ 0 := hirr.ne_zero
  have hC : C ≠ 0 := by
    intro hC0
    rw [hC0] at hpoly
    norm_num at hpoly
    have hfactor : x * ((A : ℝ) * x + (B : ℝ)) = 0 := by
      nlinarith [hpoly]
    have hlin : (A : ℝ) * x + (B : ℝ) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hx0
    have hxrat : x = (-(B : ℝ)) / (A : ℝ) := by
      apply (eq_div_iff (by exact_mod_cast hA)).2
      nlinarith [hlin]
    exact hirr ⟨(-B : ℚ) / (A : ℚ), by
      norm_num
      simpa using hxrat.symm⟩
  refine ⟨hirr.inv, C, B, A, hC, ?_⟩
  field_simp [hx0]
  nlinarith [hpoly]

private theorem quadratic_of_completeIterate (u : ℝ) (n : ℕ)
    (hquad : IsQuadraticIrrational (completeIterate u n)) :
    IsQuadraticIrrational u := by
  induction n with
  | zero => simpa [completeIterate] using hquad
  | succ n ih =>
      have hstep : IsQuadraticIrrational (completeIterate u n) := by
        have hinv := quadratic_inv (completeIterate u (n + 1)) hquad
        have hadd := quadratic_add_int (completeIterate u (n + 1))⁻¹
          (Int.floor (completeIterate u n)) hinv
        simpa [completeIterate, add_comm, sub_eq_add_neg] using hadd
      exact ih hstep

private theorem completeIterate_add (u : ℝ) (N k : ℕ) :
    completeIterate (completeIterate u N) k = completeIterate u (N + k) := by
  induction k with
  | zero => simp [completeIterate]
  | succ k ih =>
      simp only [completeIterate]
      rw [ih]
      congr 2

private theorem gauss_iterate_eq_complete_fract (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational u) (n : ℕ) :
    (gaussMapReal^[n]) u =
      completeIterate u n - (Int.floor (completeIterate u n) : ℝ) := by
  induction n with
  | zero =>
      simp only [Function.iterate_zero_apply, completeIterate]
      have hu1 : u < 1 := hu.2.lt_of_ne (by
        intro h
        exact hirr.ne_int 1 (by simpa using h))
      have hfloor : Int.floor u = 0 := by
        rw [Int.floor_eq_iff]
        norm_num
        exact ⟨hu.1, hu1⟩
      rw [hfloor]
      norm_num
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [gaussMapReal, completeIterate]
      rw [ih]

private theorem completeIterate_succ_eq_gauss_inverse (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational u) (n : ℕ) :
    completeIterate u (n + 1) = ((gaussMapReal^[n]) u)⁻¹ := by
  rw [completeIterate, gauss_iterate_eq_complete_fract u hu hirr n]

/-- The digits obtained by iterating the Gauss map give the unique regular
continued-fraction expansion of an irrational point of `[0,1]`. -/
theorem gaussPartialQuotients_expansion (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational u) :
    HasContinuedFractionExpansion u (gaussPartialQuotients u) := by
  obtain ⟨a, ha, hauniq⟩ :=
    nonnegativeIrrationalHasUniqueContinuedFractionExpansion.2 u hu.1 hirr
  have hufloor : Int.floor u = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    exact ⟨hu.1, hu.2.lt_of_ne (by
      intro h
      exact hirr.ne_int 1 (by simpa using h))⟩
  have ha0 : a.1.a₀ = 0 := by
    have hfloor := expansion_floor_eq a.1 u ha.1 ha hirr
    omega
  have hae : a.1 = gaussPartialQuotients u := by
    cases hA : a.1 with
    | mk a0 atail =>
      rw [hA] at ha0
      change ({ a₀ := a0, tail := atail } : PartialQuotients) =
        { a₀ := 0, tail := gaussDigit u }
      congr
      funext n
      have hn := iterate_shift_expansion a.1 u ha (n + 1)
      have hfloor := expansion_floor_eq _ _ hn.1 hn
        (infinite_regular_expansion_irrational _ _ hn.1 hn)
      rw [iterate_shift_a0] at hfloor
      have hcomplete := completeIterate_succ_eq_gauss_inverse u hu hirr n
      simp only [gaussDigit]
      rw [← hcomplete]
      rw [hA] at hfloor
      rw [hfloor]
      simp
  rw [← hae]
  exact ha

private theorem shifts_equal_of_eventuallyPeriodic (a : PartialQuotients)
    {N k : ℕ} (_hk : 0 < k)
    (hperiodic : ∀ n : ℕ, N ≤ n ->
      partialQuotient a (n + k) = partialQuotient a n) :
    (shiftPartials^[N + k]) a = (shiftPartials^[N]) a := by
  cases hleft : (shiftPartials^[N + k]) a with
  | mk a0 atail =>
    cases hright : (shiftPartials^[N]) a with
    | mk b0 btail =>
      congr
      · have hp := hperiodic N (le_refl N)
        have hl := shift_iterate_partialQuotient a (N + k) 0
        have hr := shift_iterate_partialQuotient a N 0
        simp [hleft, hright, partialQuotient] at hl hr
        have hp' : partialQuotient a (N + k) = partialQuotient a N := by
          simpa [add_assoc, add_comm, add_left_comm] using hp
        exact_mod_cast hl.trans (hp'.trans hr.symm)
      · funext i
        have hp := hperiodic (N + i + 1) (by omega)
        have hl := shift_iterate_partialQuotient a (N + k) (i + 1)
        have hr := shift_iterate_partialQuotient a N (i + 1)
        simp [hleft, hright, partialQuotient] at hl hr
        have hp' : partialQuotient a (N + k + (i + 1)) =
            partialQuotient a (N + (i + 1)) := by
          simpa [add_assoc, add_comm, add_left_comm] using hp
        have hidxL : N + k + (i + 1) = (N + k + i) + 1 := by omega
        have hidxR : N + (i + 1) = (N + i) + 1 := by omega
        rw [hidxL, hidxR] at hp'
        simp only [partialQuotient] at hp'
        have hpNat : a.tail (N + k + i) = a.tail (N + i) := by
          exact_mod_cast hp'
        exact hl.trans (hpNat.trans hr.symm)

theorem eventuallyPeriodicExpansion_isQuadratic (u : ℝ)
    (_hirr : Irrational u) (hper : HasEventuallyPeriodicContinuedFraction u) :
    IsQuadraticIrrational u := by
  rcases hper with ⟨a, hexp, N, k, hk, hperiodic⟩
  have hshift := shifts_equal_of_eventuallyPeriodic a hk hperiodic
  have hN := iterate_shift_expansion a u hexp N
  have hNk := iterate_shift_expansion a u hexp (N + k)
  rw [hshift] at hNk
  have hv : completeIterate u (N + k) = completeIterate u N :=
    tendsto_nhds_unique hNk.2 hN.2
  have hkpred : k - 1 + 1 = k := by omega
  have hmob := completeIterate_mobius ((shiftPartials^[N]) a)
    (completeIterate u N) hN (k - 1)
  have hcomp := completeIterate_add u N k
  rw [hkpred, hcomp, hv] at hmob
  let x := completeIterate u N
  let P := convergentNumerator ((shiftPartials^[N]) a) (k - 1)
  let Q := convergentDenominator ((shiftPartials^[N]) a) (k - 1)
  let P₀ := previousConvergentNumerator ((shiftPartials^[N]) a) (k - 1)
  let Q₀ := previousConvergentDenominator ((shiftPartials^[N]) a) (k - 1)
  have hQ : 0 < Q := denominator_pos_and_previous_nonneg _ hN.1 (k - 1) |>.1
  have hxirr := infinite_regular_expansion_irrational _ _ hN.1 hN
  have hden : (Q : ℝ) * x + Q₀ ≠ 0 := by
    intro hz
    rw [hz, div_zero] at hmob
    exact hxirr.ne_zero hmob
  have hpoly : (Q : ℝ) * x ^ 2 + ((Q₀ - P : ℤ) : ℝ) * x + (-P₀ : ℤ) = 0 := by
    have hcross := (eq_div_iff hden).mp hmob
    dsimp [x, P, Q, P₀, Q₀] at hcross ⊢
    push_cast
    nlinarith [hcross]
  have hxquad : IsQuadraticIrrational x :=
    ⟨hxirr, Q, Q₀ - P, -P₀, hQ.ne', by exact hpoly⟩
  exact quadratic_of_completeIterate u N hxquad

private def conjugateIterate (u v : ℝ) : ℕ → ℝ
  | 0 => v
  | n + 1 =>
      (conjugateIterate u v n - (Int.floor (completeIterate u n) : ℝ))⁻¹

private theorem conjugateIterate_irrational (u v : ℝ) (hvirr : Irrational v)
    (n : ℕ) : Irrational (conjugateIterate u v n) := by
  induction n with
  | zero => simpa [conjugateIterate] using hvirr
  | succ n ih =>
      simpa [conjugateIterate] using
        (ih.sub_intCast (Int.floor (completeIterate u n))).inv

private theorem completeIterate_gt_one (a : PartialQuotients) (u : ℝ)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ) :
    1 < completeIterate u (n + 1) := by
  have hn := iterate_shift_expansion a u hexp n
  have hirr := infinite_regular_expansion_irrational _ _ hn.1 hn
  have hfractPos : 0 < completeIterate u n -
      (Int.floor (completeIterate u n) : ℝ) := by
    exact Int.fract_pos.mpr (by
      intro hInt
      exact hirr.ne_int _ (by simpa [Int.fract] using hInt))
  have hfractLt : completeIterate u n -
      (Int.floor (completeIterate u n) : ℝ) < 1 := Int.fract_lt_one _
  rw [completeIterate]
  exact (one_lt_inv₀ hfractPos).2 hfractLt

private theorem conjugate_floor_eq_of_three_nonnegative
    (a : PartialQuotients) (u v : ℝ)
    (hexp : HasContinuedFractionExpansion u a) (n : ℕ)
    (_hn1 : 1 ≤ n)
    (_hy0 : 0 ≤ conjugateIterate u v n)
    (hy1 : 0 ≤ conjugateIterate u v (n + 1))
    (hy2 : 0 ≤ conjugateIterate u v (n + 2))
    (hvirr : Irrational v) :
    Int.floor (conjugateIterate u v n) =
      Int.floor (completeIterate u n) := by
  let d := conjugateIterate u v n -
    (Int.floor (completeIterate u n) : ℝ)
  have hdne : d ≠ 0 := by
    intro hd
    have : conjugateIterate u v n =
        (Int.floor (completeIterate u n) : ℝ) := by
      dsimp [d] at hd
      linarith
    exact (conjugateIterate_irrational u v hvirr n).ne_int _ this
  have hdpos : 0 < d := by
    have hinv : 0 ≤ d⁻¹ := by
      simpa [conjugateIterate, d] using hy1
    exact lt_of_le_of_ne (inv_nonneg.mp hinv) (Ne.symm hdne)
  have hdlt : d < 1 := by
    by_contra h
    have hdge : 1 ≤ d := le_of_not_gt h
    have hy1pos : 0 < conjugateIterate u v (n + 1) := by
      simpa [conjugateIterate, d] using inv_pos.mpr hdpos
    have hy1le : conjugateIterate u v (n + 1) ≤ 1 := by
      simpa [conjugateIterate, d] using (inv_le_one₀ hdpos).2 hdge
    have hfloor : (1 : ℝ) ≤ Int.floor (completeIterate u (n + 1)) := by
      have hfloorZ : (1 : ℤ) ≤ Int.floor (completeIterate u (n + 1)) :=
        Int.le_floor.mpr (by
          norm_num only
          exact (completeIterate_gt_one a u hexp n).le)
      exact_mod_cast hfloorZ
    have hdiff : conjugateIterate u v (n + 1) -
        (Int.floor (completeIterate u (n + 1)) : ℝ) ≤ 0 := by
      linarith
    have hdiffne : conjugateIterate u v (n + 1) -
        (Int.floor (completeIterate u (n + 1)) : ℝ) ≠ 0 := by
      intro heq
      have heq' : conjugateIterate u v (n + 1) =
          (Int.floor (completeIterate u (n + 1)) : ℝ) := by linarith
      exact (conjugateIterate_irrational u v hvirr (n + 1)).ne_int _ heq'
    have hneg : conjugateIterate u v (n + 2) < 0 := by
      rw [conjugateIterate]
      exact inv_lt_zero.mpr (lt_of_le_of_ne hdiff hdiffne)
    linarith
  rw [Int.floor_eq_iff]
  constructor <;> dsimp [d] at hdpos hdlt ⊢ <;> linarith

private theorem conjugateIterate_exists_negative (a : PartialQuotients)
    (u v : ℝ) (hexp : HasContinuedFractionExpansion u a)
    (hvirr : Irrational v) (huv : u ≠ v) :
    ∃ n : ℕ, 1 ≤ n ∧ conjugateIterate u v n < 0 := by
  by_contra hnone
  push_neg at hnone
  have hynonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ conjugateIterate u v n := by
    intro n hn
    exact hnone n hn
  have hfloors : ∀ n : ℕ, 1 ≤ n →
      Int.floor (conjugateIterate u v n) =
        Int.floor (completeIterate u n) := by
    intro n hn
    exact conjugate_floor_eq_of_three_nonnegative a u v hexp n hn
      (hynonneg n hn) (hynonneg (n + 1) (by omega))
      (hynonneg (n + 2) (by omega)) hvirr
  have hycomplete : ∀ i : ℕ,
      completeIterate (conjugateIterate u v 1) i =
        conjugateIterate u v (i + 1) := by
    intro i
    induction i with
    | zero => simp [completeIterate]
    | succ i ih =>
        change (completeIterate (conjugateIterate u v 1) i -
            (Int.floor (completeIterate (conjugateIterate u v 1) i) : ℝ))⁻¹ =
          (conjugateIterate u v (i + 1) -
            (Int.floor (completeIterate u (i + 1)) : ℝ))⁻¹
        rw [ih, hfloors (i + 1) (by omega)]
  have hxcomplete : ∀ i : ℕ,
      completeIterate (completeIterate u 1) i =
        completeIterate u (i + 1) := by
    intro i
    simpa [add_comm] using completeIterate_add u 1 i
  obtain ⟨b, hb, hbuniq⟩ :=
    nonnegativeIrrationalHasUniqueContinuedFractionExpansion.2
      (conjugateIterate u v 1) (hynonneg 1 (by omega))
      (conjugateIterate_irrational u v hvirr 1)
  have ha1 := iterate_shift_expansion a u hexp 1
  have hpq : ∀ i : ℕ,
      partialQuotient b.1 i = partialQuotient (shiftPartials a) i := by
    intro i
    have hbi := iterate_shift_expansion b.1 (conjugateIterate u v 1) hb i
    have hai := iterate_shift_expansion (shiftPartials a)
      (completeIterate u 1) ha1 i
    have hfb := expansion_floor_eq _ _ hbi.1 hbi
      (infinite_regular_expansion_irrational _ _ hbi.1 hbi)
    have hfa := expansion_floor_eq _ _ hai.1 hai
      (infinite_regular_expansion_irrational _ _ hai.1 hai)
    have hsb := shift_iterate_partialQuotient b.1 i 0
    have hsa := shift_iterate_partialQuotient (shiftPartials a) i 0
    simp only [Nat.add_zero, partialQuotient] at hsb hsa
    rw [hsb] at hfb
    rw [hsa] at hfa
    rw [hycomplete i] at hfb
    rw [hxcomplete i] at hfa
    exact hfb.symm.trans ((hfloors (i + 1) (by omega)).trans hfa)
  have hba : b.1 = shiftPartials a := by
    cases hB : b.1 with
    | mk b0 btail =>
      cases hA : shiftPartials a with
      | mk a0 atail =>
        congr
        · have := hpq 0
          simpa [hB, hA, partialQuotient] using this
        · funext i
          have := hpq (i + 1)
          simpa [hB, hA, partialQuotient] using this
  have hxy : completeIterate u 1 = conjugateIterate u v 1 := by
    have ha1' : HasContinuedFractionExpansion (completeIterate u 1)
        (shiftPartials a) := by
      simpa [Function.iterate_one] using ha1
    apply tendsto_nhds_unique ha1'.2
    rw [← hba]
    exact hb.2
  have hinv : (u - (Int.floor u : ℝ))⁻¹ =
      (v - (Int.floor u : ℝ))⁻¹ := by
    simpa [completeIterate, conjugateIterate] using hxy
  have hbase : u - (Int.floor u : ℝ) =
      v - (Int.floor u : ℝ) := inv_inj.mp hinv
  exact huv (by linarith)

private theorem conjugateIterate_eventually_reduced (a : PartialQuotients)
    (u v : ℝ) (hexp : HasContinuedFractionExpansion u a)
    (hvirr : Irrational v) (huv : u ≠ v) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      -1 < conjugateIterate u v n ∧ conjugateIterate u v n < 0 := by
  obtain ⟨m, hm1, hmneg⟩ :=
    conjugateIterate_exists_negative a u v hexp hvirr huv
  refine ⟨m + 1, by omega, ?_⟩
  intro n hn
  obtain ⟨r, rfl⟩ : ∃ r, n = m + 1 + r := ⟨n - (m + 1), by omega⟩
  induction r with
  | zero =>
      have hfloor : (1 : ℝ) ≤ Int.floor (completeIterate u m) := by
        have hfloorZ : (1 : ℤ) ≤ Int.floor (completeIterate u m) :=
          Int.le_floor.mpr (by
            have hgt := completeIterate_gt_one a u hexp (m - 1)
            rw [show m - 1 + 1 = m by omega] at hgt
            norm_num only
            exact hgt.le)
        exact_mod_cast hfloorZ
      rw [show m + 1 + 0 = m + 1 by omega, conjugateIterate]
      have hdne : conjugateIterate u v m -
          (Int.floor (completeIterate u m) : ℝ) ≠ 0 := by
        intro hd
        have heq : conjugateIterate u v m =
            (Int.floor (completeIterate u m) : ℝ) := by linarith
        exact (conjugateIterate_irrational u v hvirr m).ne_int _ heq
      constructor
      · have hinvneg := inv_lt_zero.mpr (by linarith :
            conjugateIterate u v m -
              (Int.floor (completeIterate u m) : ℝ) < 0)
        have hmul := inv_mul_cancel₀ hdne
        nlinarith
      · exact inv_lt_zero.mpr (by linarith)
  | succ r ih =>
      have hindex : m + 1 + r = (m + r) + 1 := by omega
      have hfloor : (1 : ℝ) ≤
          Int.floor (completeIterate u (m + 1 + r)) := by
        have hfloorZ : (1 : ℤ) ≤
            Int.floor (completeIterate u (m + 1 + r)) :=
          Int.le_floor.mpr
            (by
              norm_num only
              simpa [add_assoc, add_comm, add_left_comm] using
                (completeIterate_gt_one a u hexp (m + r)).le)
        exact_mod_cast hfloorZ
      rw [show m + 1 + (r + 1) = (m + 1 + r) + 1 by omega,
        conjugateIterate]
      have ihr := ih (by omega)
      have hdne : conjugateIterate u v (m + 1 + r) -
          (Int.floor (completeIterate u (m + 1 + r)) : ℝ) ≠ 0 := by
        intro hd
        have heq : conjugateIterate u v (m + 1 + r) =
            (Int.floor (completeIterate u (m + 1 + r)) : ℝ) := by linarith
        exact (conjugateIterate_irrational u v hvirr (m + 1 + r)).ne_int _ heq
      constructor
      · have hinvneg := inv_lt_zero.mpr (by linarith [ihr.2] :
            conjugateIterate u v (m + 1 + r) -
              (Int.floor (completeIterate u (m + 1 + r)) : ℝ) < 0)
        have hmul := inv_mul_cancel₀ hdne
        nlinarith
      · exact inv_lt_zero.mpr (by linarith [ihr.2])

private def quadraticCoefficients (u : ℝ) (A B C : ℤ) :
    ℕ → ℤ × ℤ × ℤ
  | 0 => (A, B, C)
  | n + 1 =>
      let t := quadraticCoefficients u A B C n
      let m := Int.floor (completeIterate u n)
      (t.1 * m ^ 2 + t.2.1 * m + t.2.2,
        2 * t.1 * m + t.2.1, t.1)

private theorem completeIterate_backward (u : ℝ) (n : ℕ) :
    completeIterate u n = (Int.floor (completeIterate u n) : ℝ) +
      (completeIterate u (n + 1))⁻¹ := by
  rw [completeIterate]
  simp

private theorem completeIterate_irrational (u : ℝ) (hirr : Irrational u)
    (n : ℕ) : Irrational (completeIterate u n) := by
  induction n with
  | zero => simpa [completeIterate] using hirr
  | succ n ih =>
      simpa [completeIterate] using
        (ih.sub_intCast (Int.floor (completeIterate u n))).inv

private theorem conjugateIterate_backward (u v : ℝ) (n : ℕ) :
    conjugateIterate u v n = (Int.floor (completeIterate u n) : ℝ) +
      (conjugateIterate u v (n + 1))⁻¹ := by
  rw [conjugateIterate]
  simp

private theorem quadraticCoefficients_roots (u v : ℝ) (A B C : ℤ)
    (hu : (A : ℝ) * u ^ 2 + (B : ℝ) * u + (C : ℝ) = 0)
    (hv : (A : ℝ) * v ^ 2 + (B : ℝ) * v + (C : ℝ) = 0)
    (hirr : Irrational u) (hvirr : Irrational v) (n : ℕ) :
    let t := quadraticCoefficients u A B C n
    (t.1 : ℝ) * (completeIterate u n) ^ 2 +
          (t.2.1 : ℝ) * completeIterate u n + (t.2.2 : ℝ) = 0 ∧
      (t.1 : ℝ) * (conjugateIterate u v n) ^ 2 +
          (t.2.1 : ℝ) * conjugateIterate u v n + (t.2.2 : ℝ) = 0 := by
  induction n with
  | zero => simpa [quadraticCoefficients, completeIterate, conjugateIterate]
      using And.intro hu hv
  | succ n ih =>
      dsimp only [quadraticCoefficients]
      have hx := ih.1
      have hy := ih.2
      have hxrec := completeIterate_backward u n
      have hyrec := conjugateIterate_backward u v n
      have hxne : completeIterate u (n + 1) ≠ 0 :=
        (completeIterate_irrational u hirr (n + 1)).ne_zero
      have hyne : conjugateIterate u v (n + 1) ≠ 0 :=
        (conjugateIterate_irrational u v hvirr (n + 1)).ne_zero
      constructor
      · rw [hxrec] at hx
        push_cast
        field_simp [hxne] at hx
        nlinarith [hx]
      · rw [hyrec] at hy
        push_cast
        field_simp [hyne] at hy
        nlinarith [hy]

private theorem quadraticCoefficients_discriminant (u : ℝ) (A B C : ℤ)
    (n : ℕ) :
    let t := quadraticCoefficients u A B C n
    t.2.1 ^ 2 - 4 * t.1 * t.2.2 = B ^ 2 - 4 * A * C := by
  induction n with
  | zero => simp [quadraticCoefficients]
  | succ n ih =>
      dsimp only [quadraticCoefficients]
      calc
        _ = (quadraticCoefficients u A B C n).2.1 ^ 2 -
              4 * (quadraticCoefficients u A B C n).1 *
                (quadraticCoefficients u A B C n).2.2 := by ring
        _ = B ^ 2 - 4 * A * C := ih

private theorem quadratic_conjugate_data (u : ℝ) (A B C : ℤ)
    (hirr : Irrational u) (hA : A ≠ 0)
    (hpoly : (A : ℝ) * u ^ 2 + (B : ℝ) * u + (C : ℝ) = 0) :
    let v := ((-(B : ℚ) / (A : ℚ) : ℚ) : ℝ) - u
    Irrational v ∧ u ≠ v ∧
      (A : ℝ) * v ^ 2 + (B : ℝ) * v + (C : ℝ) = 0 ∧
      0 < B ^ 2 - 4 * A * C := by
  let q : ℚ := -(B : ℚ) / (A : ℚ)
  let v : ℝ := (q : ℝ) - u
  have hvirr : Irrational v := by
    exact Irrational.ratCast_sub q hirr
  have hAreal : (A : ℝ) ≠ 0 := by exact_mod_cast hA
  have hsum : (A : ℝ) * (u + v) + (B : ℝ) = 0 := by
    dsimp [v, q]
    push_cast
    field_simp [hAreal]
    ring
  have huv : u ≠ v := by
    intro huv
    have hlin : (2 * A : ℝ) * u + (B : ℝ) = 0 := by
      rw [← huv] at hsum
      nlinarith [hsum]
    apply hirr
    refine ⟨(-(B : ℚ) / (2 * A : ℚ)), ?_⟩
    push_cast
    apply (div_eq_iff (by
      norm_num
      exact_mod_cast hA)).2
    nlinarith [hlin]
  have hvpoly : (A : ℝ) * v ^ 2 + (B : ℝ) * v + (C : ℝ) = 0 := by
    have hfactor : (u - v) * ((A : ℝ) * (u + v) + (B : ℝ)) = 0 := by
      rw [hsum]
      ring
    nlinarith [hpoly, hsum]
  have hdiscR : ((B ^ 2 - 4 * A * C : ℤ) : ℝ) =
      (A : ℝ) ^ 2 * (u - v) ^ 2 := by
    push_cast
    have hBreal : (B : ℝ) = -(A : ℝ) * (u + v) := by
      linarith [hsum]
    have hCreal : (C : ℝ) = -(A : ℝ) * u ^ 2 - (B : ℝ) * u := by
      linarith [hpoly]
    rw [hCreal, hBreal]
    ring
  have hdiscPosR : (0 : ℝ) < (B ^ 2 - 4 * A * C : ℤ) := by
    rw [hdiscR]
    exact mul_pos (sq_pos_of_ne_zero hAreal)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr huv))
  refine ⟨hvirr, huv, hvpoly, ?_⟩
  exact_mod_cast hdiscPosR

private theorem reduced_quadratic_coefficients_bounded
    (x y : ℝ) (A B C D : ℤ)
    (hxroot : (A : ℝ) * x ^ 2 + (B : ℝ) * x + (C : ℝ) = 0)
    (hyroot : (A : ℝ) * y ^ 2 + (B : ℝ) * y + (C : ℝ) = 0)
    (hdisc : B ^ 2 - 4 * A * C = D) (hD : 0 < D)
    (hx : 1 < x) (hy : -1 < y ∧ y < 0) :
    A ∈ Set.Ioo (-D) D ∧ B ∈ Set.Ioo (-D) D ∧ C ∈ Set.Ioo (-D) D := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hxy : 1 < x - y := by linarith
  have hAne : A ≠ 0 := by
    intro hA0
    have hfac : (B : ℝ) * (x - y) = 0 := by
      rw [hA0] at hxroot hyroot
      norm_num at hxroot hyroot
      nlinarith [hxroot, hyroot]
    have hB0R : (B : ℝ) = 0 :=
      (mul_eq_zero.mp hfac).resolve_right (by linarith)
    have hB0 : B = 0 := by exact_mod_cast hB0R
    rw [hA0, hB0] at hdisc
    norm_num at hdisc
    omega
  have hAneR : (A : ℝ) ≠ 0 := by exact_mod_cast hAne
  have hsum : (A : ℝ) * (x + y) + (B : ℝ) = 0 := by
    have hfac : (x - y) * ((A : ℝ) * (x + y) + (B : ℝ)) = 0 := by
      nlinarith [hxroot, hyroot]
    exact (mul_eq_zero.mp hfac).resolve_left (by linarith)
  have hprod : (C : ℝ) = (A : ℝ) * x * y := by
    nlinarith [hxroot, hsum]
  have hdiscR : (D : ℝ) = (B : ℝ) ^ 2 -
      4 * (A : ℝ) * (C : ℝ) := by exact_mod_cast hdisc.symm
  have hdiscRoots : (D : ℝ) = (A : ℝ) ^ 2 * (x - y) ^ 2 := by
    rw [hprod] at hdiscR
    have hB : (B : ℝ) = -(A : ℝ) * (x + y) := by linarith [hsum]
    rw [hB] at hdiscR
    nlinarith [hdiscR]
  have hAsq : (A : ℝ) ^ 2 < D := by
    have hdiffsq : (1 : ℝ) < (x - y) ^ 2 := by nlinarith
    have hApos : 0 < (A : ℝ) ^ 2 := sq_pos_of_ne_zero hAneR
    nlinarith [hdiscRoots]
  have hAboundsR : (-(D : ℝ)) < A ∧ (A : ℝ) < D := by
    constructor <;> nlinarith [sq_nonneg ((A : ℝ) + D),
      sq_nonneg ((A : ℝ) - D)]
  have hACneg : (A : ℝ) * C < 0 := by
    rw [hprod]
    have hApos : 0 < (A : ℝ) ^ 2 := sq_pos_of_ne_zero hAneR
    have hxyneg : x * y < 0 :=
      mul_neg_of_pos_of_neg (lt_trans zero_lt_one hx) hy.2
    nlinarith [hxyneg]
  have hBsq : (B : ℝ) ^ 2 < D := by nlinarith [hdiscR]
  have hBboundsR : (-(D : ℝ)) < B ∧ (B : ℝ) < D := by
    constructor <;> nlinarith [sq_nonneg ((B : ℝ) + D),
      sq_nonneg ((B : ℝ) - D)]
  have hAabs : (1 : ℝ) ≤ |(A : ℝ)| := by
    exact_mod_cast Int.one_le_abs hAne
  have hACabs : |(A : ℝ) * (C : ℝ)| < (D : ℝ) := by
    rw [abs_of_neg hACneg]
    nlinarith [sq_nonneg (B : ℝ), hdiscR]
  have hCabs : |(C : ℝ)| < (D : ℝ) := by
    calc
      |(C : ℝ)| = 1 * |(C : ℝ)| := by ring
      _ ≤ |(A : ℝ)| * |(C : ℝ)| :=
        mul_le_mul_of_nonneg_right hAabs (abs_nonneg _)
      _ = |(A : ℝ) * (C : ℝ)| := by rw [abs_mul]
      _ < D := hACabs
  have hCboundsR : (-(D : ℝ)) < C ∧ (C : ℝ) < D :=
    (abs_lt.mp hCabs)
  constructor
  · exact_mod_cast hAboundsR
  constructor
  · exact_mod_cast hBboundsR
  · exact_mod_cast hCboundsR

private theorem positive_root_unique_with_negative_root
    (x y z : ℝ) (A B C D : ℤ)
    (hx : 0 < x) (hy : y < 0) (hz : 0 < z)
    (hxroot : (A : ℝ) * x ^ 2 + (B : ℝ) * x + (C : ℝ) = 0)
    (hyroot : (A : ℝ) * y ^ 2 + (B : ℝ) * y + (C : ℝ) = 0)
    (hzroot : (A : ℝ) * z ^ 2 + (B : ℝ) * z + (C : ℝ) = 0)
    (hdisc : B ^ 2 - 4 * A * C = D) (hD : 0 < D) : z = x := by
  have hAne : A ≠ 0 := by
    intro hA0
    have hfac : (B : ℝ) * (x - y) = 0 := by
      rw [hA0] at hxroot hyroot
      norm_num at hxroot hyroot
      nlinarith [hxroot, hyroot]
    have hB0R : (B : ℝ) = 0 :=
      (mul_eq_zero.mp hfac).resolve_right (by linarith)
    have hB0 : B = 0 := by exact_mod_cast hB0R
    rw [hA0, hB0] at hdisc
    norm_num at hdisc
    omega
  have hAneR : (A : ℝ) ≠ 0 := by exact_mod_cast hAne
  have hsumx : (A : ℝ) * (x + y) + (B : ℝ) = 0 := by
    have hfac : (x - y) * ((A : ℝ) * (x + y) + (B : ℝ)) = 0 := by
      nlinarith [hxroot, hyroot]
    exact (mul_eq_zero.mp hfac).resolve_left (by linarith)
  have hsumz : (A : ℝ) * (z + y) + (B : ℝ) = 0 := by
    have hfac : (z - y) * ((A : ℝ) * (z + y) + (B : ℝ)) = 0 := by
      nlinarith [hzroot, hyroot]
    exact (mul_eq_zero.mp hfac).resolve_left (by linarith)
  have : (A : ℝ) * (z - x) = 0 := by nlinarith [hsumx, hsumz]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hAneR)

/-- Lagrange's converse: a quadratic irrational has an eventually periodic
regular continued-fraction expansion. -/
theorem quadraticIrrational_hasEventuallyPeriodicExpansion (u : ℝ)
    (hquad : IsQuadraticIrrational u) :
    HasEventuallyPeriodicContinuedFraction u := by
  rcases hquad with ⟨hirr, A, B, C, hA, hpoly⟩
  let a := canonicalPartials u hirr
  have hexp : HasContinuedFractionExpansion u a :=
    canonicalPartials_expansion u hirr
  let v : ℝ := (((-(B : ℚ) / (A : ℚ) : ℚ) : ℝ) - u)
  obtain ⟨hvirr, huv, hvpoly, hD⟩ :=
    quadratic_conjugate_data u A B C hirr hA hpoly
  let D : ℤ := B ^ 2 - 4 * A * C
  have hD' : 0 < D := hD
  obtain ⟨N, hN1, hred⟩ :=
    conjugateIterate_eventually_reduced a u v hexp hvirr huv
  let S : Set (ℤ × ℤ × ℤ) :=
    Set.Icc (-D) D ×ˢ (Set.Icc (-D) D ×ˢ Set.Icc (-D) D)
  have hcoeff_mem : ∀ r : ℕ, quadraticCoefficients u A B C (N + r) ∈ S := by
    intro r
    have hn : 1 ≤ N + r := by omega
    have hxgt : 1 < completeIterate u (N + r) := by
      have := completeIterate_gt_one a u hexp (N + r - 1)
      rwa [show N + r - 1 + 1 = N + r by omega] at this
    have hroots := quadraticCoefficients_roots u v A B C hpoly hvpoly
      hirr hvirr (N + r)
    have hdisc := quadraticCoefficients_discriminant u A B C (N + r)
    have hb := reduced_quadratic_coefficients_bounded
      (completeIterate u (N + r)) (conjugateIterate u v (N + r))
      (quadraticCoefficients u A B C (N + r)).1
      (quadraticCoefficients u A B C (N + r)).2.1
      (quadraticCoefficients u A B C (N + r)).2.2 D
      hroots.1 hroots.2 hdisc hD' hxgt (hred (N + r) (by omega))
    exact ⟨⟨hb.1.1.le, hb.1.2.le⟩,
      ⟨⟨hb.2.1.1.le, hb.2.1.2.le⟩,
        ⟨hb.2.2.1.le, hb.2.2.2.le⟩⟩⟩
  have hSfinite : S.Finite :=
    (Set.finite_Icc (-D) D).prod
      ((Set.finite_Icc (-D) D).prod (Set.finite_Icc (-D) D))
  letI : Fintype S := hSfinite.fintype
  let f : ℕ → S := fun r =>
    ⟨quadraticCoefficients u A B C (N + r), hcoeff_mem r⟩
  obtain ⟨r, s, hrs, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have heqv : quadraticCoefficients u A B C (N + r) =
      quadraticCoefficients u A B C (N + s) :=
    congrArg Subtype.val heq
  have hrepetition : ∃ n k : ℕ, N ≤ n ∧ 0 < k ∧
      quadraticCoefficients u A B C n =
        quadraticCoefficients u A B C (n + k) := by
    rcases lt_or_gt_of_ne hrs with hrslt | hsrlt
    · refine ⟨N + r, s - r, by omega, by omega, ?_⟩
      simpa [show N + r + (s - r) = N + s by omega] using heqv
    · refine ⟨N + s, r - s, by omega, by omega, ?_⟩
      simpa [show N + s + (r - s) = N + r by omega] using heqv.symm
  obtain ⟨n, k, hnN, hk, hcoeff⟩ := hrepetition
  have hn1 : 1 ≤ n := hN1.trans hnN
  have hnkN : N ≤ n + k := by omega
  have hrootsn := quadraticCoefficients_roots u v A B C hpoly hvpoly
    hirr hvirr n
  have hrootsnk := quadraticCoefficients_roots u v A B C hpoly hvpoly
    hirr hvirr (n + k)
  have hdiscn := quadraticCoefficients_discriminant u A B C n
  have hxpos : 0 < completeIterate u n := by
    have hgt := completeIterate_gt_one a u hexp (n - 1)
    rw [show n - 1 + 1 = n by omega] at hgt
    linarith
  have hxkpos : 0 < completeIterate u (n + k) := by
    have hgt := completeIterate_gt_one a u hexp (n + k - 1)
    rw [show n + k - 1 + 1 = n + k by omega] at hgt
    linarith
  have hyneg := (hred n hnN).2
  have hxrepeat : completeIterate u (n + k) = completeIterate u n := by
    apply positive_root_unique_with_negative_root
      (completeIterate u n) (conjugateIterate u v n)
      (completeIterate u (n + k))
      (quadraticCoefficients u A B C n).1
      (quadraticCoefficients u A B C n).2.1
      (quadraticCoefficients u A B C n).2.2 D
      hxpos hyneg hxkpos hrootsn.1 hrootsn.2
    · rw [hcoeff]
      exact hrootsnk.1
    · exact hdiscn
    · exact hD'
  have hshiftn := iterate_shift_expansion a u hexp n
  have hshiftnk := iterate_shift_expansion a u hexp (n + k)
  rw [hxrepeat] at hshiftnk
  have hshiftEq : (shiftPartials^[n + k]) a = (shiftPartials^[n]) a :=
    expansion_unique _ _ _ hshiftnk hshiftn
  refine ⟨a, hexp, n, k, hk, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
  have hl := shift_iterate_partialQuotient a (n + k) i
  have hr := shift_iterate_partialQuotient a n i
  rw [hshiftEq] at hl
  simpa [add_assoc, add_comm, add_left_comm] using hl.symm.trans hr

end Section01
end Chapter03
