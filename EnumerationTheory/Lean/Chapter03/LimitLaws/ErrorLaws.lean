import Chapter03.LimitLaws.LevyLaws

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter03

theorem approximation_error_log_gap_bounds (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hirr : Irrational x) (m : ℕ) (hm : 0 < m) :
    -Real.log 2 ≤
        Real.log |x - ((finiteContinuedFraction
          (gaussPartialQuotients x) m : ℚ) : ℝ)| +
          Real.log (convergentDenominator
            (gaussPartialQuotients x) m : ℝ) +
          Real.log (convergentDenominator
            (gaussPartialQuotients x) (m + 1) : ℝ) ∧
      Real.log |x - ((finiteContinuedFraction
          (gaussPartialQuotients x) m : ℚ) : ℝ)| +
          Real.log (convergentDenominator
            (gaussPartialQuotients x) m : ℝ) +
          Real.log (convergentDenominator
            (gaussPartialQuotients x) (m + 1) : ℝ) ≤ 0 := by
  let a := gaussPartialQuotients x
  let p : ℝ := convergentNumerator a m
  let q : ℝ := convergentDenominator a m
  let Q : ℝ := convergentDenominator a (m + 1)
  let e : ℝ := |x - ((finiteContinuedFraction a m : ℚ) : ℝ)|
  have hexp := Section01.gaussPartialQuotients_expansion x hx hirr
  have hreg : IsRegularPartialQuotients a := by simpa [a] using hexp.1
  have hnreg : IsNonnegativeRegularPartialQuotients a := by
    exact ⟨by simp [a, gaussPartialQuotients], hreg⟩
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Section01.denominator_pos_and_previous_nonneg a hreg m).1
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (Section01.denominator_pos_and_previous_nonneg a hreg (m + 1)).1
  have hqQ : q ≤ Q := by
    dsimp [q, Q, a]
    exact_mod_cast gaussDenominator_monotone x hx hirr m
  have hepos : 0 < e := by
    dsimp [e]
    exact abs_pos.mpr (by
      intro heq
      apply hirr
      refine ⟨finiteContinuedFraction a m, ?_⟩
      linarith)
  have hupper : e < (q * Q)⁻¹ := by
    simpa [e, q, Q, a, Section01.realConvergent] using
      Section01.convergent_error_lt_of_irrational a x hreg hexp hirr m
  have herrRel : |p - q * x| = q * e := by
    dsimp [p, q, e]
    rw [Section01.finite_eq_ratio a hreg m]
    push_cast
    have hqNe : (convergentDenominator a m : ℝ) ≠ 0 := by positivity
    rw [show (convergentNumerator a m : ℝ) -
        (convergentDenominator a m : ℝ) * x =
        -(convergentDenominator a m : ℝ) *
          (x - (convergentNumerator a m : ℝ) /
            (convergentDenominator a m : ℝ)) by
      field_simp [hqNe]
      ring]
    rw [abs_mul, abs_neg, abs_of_pos hq]
  have hlowerSecond := Section01.second_kind_error_lower a x hnreg hexp m hm
  change 1 / (q + Q) < |p - q * x| at hlowerSecond
  rw [herrRel] at hlowerSecond
  have hlower : (q * (q + Q))⁻¹ < e := by
    have hsum : 0 < q + Q := add_pos hq hQ
    rw [show (q * (q + Q))⁻¹ = (1 / (q + Q)) / q by
      field_simp [hq.ne', hsum.ne']]
    exact (div_lt_iff₀ hq).2 (by simpa [mul_comm] using hlowerSecond)
  have hsumUpper : q + Q ≤ 2 * Q := by linarith
  have hlogUpper := Real.log_le_log hepos (le_of_lt hupper)
  have hlogLower := Real.log_le_log (by positivity : 0 < (q * (q + Q))⁻¹)
    (le_of_lt hlower)
  have hlogSum := Real.log_le_log (add_pos hq hQ) hsumUpper
  rw [Real.log_inv, Real.log_mul hq.ne' (add_pos hq hQ).ne'] at hlogLower
  rw [Real.log_inv, Real.log_mul hq.ne' hQ.ne'] at hlogUpper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQ.ne'] at hlogSum
  change -Real.log 2 ≤ Real.log e + Real.log q + Real.log Q ∧
    Real.log e + Real.log q + Real.log Q ≤ 0
  constructor <;> linarith

theorem convergentApproximationError_exponent_ae :
    AlmostEveryOnUnitInterval fun x : ℝ =>
      Tendsto
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
          Real.log |x - ((finiteContinuedFraction
            (gaussPartialQuotients x) (n + 1) : ℚ) : ℝ)|)
        atTop (nhds continuedFractionErrorExponent) := by
  filter_upwards [convergentDenominator_growth_ae,
    ae_gaussMeasure_irrational] with x hqgrowth hirr
  have hdenTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have honeDiv : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hdenTop
  have hratio : Tendsto
      (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (nhds 1)).add honeDiv
    convert h using 1
    · funext n
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      field_simp [hn.ne']
      push_cast
      ring
    · norm_num
  have hshift := hqgrowth.comp (Filter.tendsto_add_atTop_nat 1)
  have hqnext : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ *
        Real.log (convergentDenominator
          (gaussPartialQuotients x.1) (n + 2) : ℝ))
      atTop (nhds levyConstant) := by
    have hmul := hratio.mul hshift
    simpa only [one_mul] using hmul.congr' (by
      filter_upwards [] with n
      have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hn2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      dsimp
      field_simp [hn1.ne', hn2.ne']
      )
  have hbound : Tendsto (fun n : ℕ => Real.log 2 / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hdenTop
  let gap : ℕ → ℝ := fun n =>
    Real.log |x.1 - ((finiteContinuedFraction
      (gaussPartialQuotients x.1) (n + 1) : ℚ) : ℝ)| +
      Real.log (convergentDenominator
        (gaussPartialQuotients x.1) (n + 1) : ℝ) +
      Real.log (convergentDenominator
        (gaussPartialQuotients x.1) (n + 2) : ℝ)
  have hgapBounds (n : ℕ) : -Real.log 2 ≤ gap n ∧ gap n ≤ 0 := by
    simpa [gap] using approximation_error_log_gap_bounds
      x.1 x.2 hirr (n + 1) (by omega)
  have hnegGap : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * (-gap n))
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (neg_nonneg.mpr (hgapBounds n).2)
    · intro n
      have hg := (hgapBounds n).1
      have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
      calc
        ((n + 1 : ℕ) : ℝ)⁻¹ * (-gap n) ≤
            ((n + 1 : ℕ) : ℝ)⁻¹ * Real.log 2 :=
          mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hn.le)
        _ = Real.log 2 / ((n + 1 : ℕ) : ℝ) := by
          rw [div_eq_mul_inv]
          ring
    · exact hbound
  have hgap : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * gap n)
      atTop (nhds 0) := by
    convert hnegGap.neg using 1
    · funext n
      ring
    · simp
  have hresult := (hgap.sub hqgrowth).sub hqnext
  convert hresult using 1
  · funext n
    dsimp [gap]
    ring
  · dsimp [continuedFractionErrorExponent, levyConstant]
    ring_nf

end Chapter03
