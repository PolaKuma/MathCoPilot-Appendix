import Chapter02.Recurrence.WeightedSyndeticTransfer

open Classical Filter Set

noncomputable section

namespace Chapter02.MultipleKhintchineBohrTriple

universe u

open BohrWeightedUniform
open ForwardKroneckerBohr

/-- The three-term clause of Bergelson--Host--Kra multiple Khintchine,
proved by a nonnegative Bohr peak which localizes the forward-Kronecker
factor while annihilating the characteristic-factor error. -/
theorem triple_syndetic
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A)
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      MultipleKhintchineSyndetic.tripleCorrelation M A n >
        (realMeasure M A) ^ 3 - ε} := by
  let a : ℕ → ℝ :=
    MultipleKhintchineSyndetic.tripleCorrelation M A
  let b : ℕ → ℝ :=
    ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
      M hM A hA
  let c : ℝ := (realMeasure M A) ^ 3 - ε
  let γ : ℝ := ε / 2
  let T : ℝ := b 0 - γ
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  obtain ⟨ρ, hρ0, hρ1, hcontract⟩ :=
    exists_forwardKroneckerPeakBase_contraction
      M hM A hA hApos γ hγ
  let t : ℝ := (1 + ρ) / 2
  let σ : ℝ := t ^ 2
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have ht1 : t < 1 := by
    dsimp [t]
    linarith
  have hσ : 0 < σ := by
    dsimp [σ]
    positivity
  have hρσ : ρ < σ := by
    dsimp [σ, t]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hρ1)]
  have hreturn_one :
      IsSyndetic {n : ℕ |
        b 0 - γ / 2 < b n ∧
        σ ≤
          (forwardKroneckerPeakWeight M hM A hA 1 n).re} := by
    simpa only [b, σ, one_mul, pow_one] using
      (syndetic_forwardKroneckerPeakWeight_floor
        M hM A hA hApos γ hγ t ht0 ht1 1)
  obtain ⟨L, hL, hreturnL⟩ := hreturn_one
  let r : ℝ := ρ / σ
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hσ).2 hρσ
  have htarget :
      0 < γ / (8 * (L : ℝ)) := by
    exact div_pos hγ (mul_pos (by norm_num) (by exact_mod_cast hL))
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one htarget hr1
  let w : ℕ → ℂ :=
    forwardKroneckerPeakWeight M hM A hA k
  have hrpow :
      r ^ k * σ ^ k = ρ ^ k := by
    dsimp [r]
    rw [div_pow]
    field_simp
  have hk_scaled :
      (L : ℝ) * 4 * r ^ k < γ / 2 := by
    have hL8 : 0 < (L : ℝ) * 4 := by
      positivity
    have hmul :=
      mul_lt_mul_of_pos_left hk hL8
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    calc
      (L : ℝ) * 4 * r ^ k <
          (L : ℝ) * 4 * (γ / (8 * (L : ℝ))) := hmul
      _ = γ / 2 := by
        field_simp
        norm_num
  have hratio :
      (L : ℝ) * 4 * ρ ^ k < γ * σ ^ k / 2 := by
    calc
      (L : ℝ) * 4 * ρ ^ k =
          ((L : ℝ) * 4 * r ^ k) * σ ^ k := by
        rw [← hrpow]
        ring
      _ < (γ / 2) * σ ^ k :=
        mul_lt_mul_of_pos_right hk_scaled (pow_pos hσ k)
      _ = γ * σ ^ k / 2 := by ring
  have hthreshold : c + γ ≤ T := by
    have hbase :=
      cube_le_forwardKroneckerTripleCorrelation_zero M hM A hA
    dsimp [c, T, γ, b]
    linarith
  have hw_nonneg : ∀ n, 0 ≤ (w n).re := by
    intro n
    exact forwardKroneckerPeakWeight_re_nonneg
      M hM A hA k n
  have herror : ∀ n, |a n - b n| ≤ 4 := by
    intro n
    have hnorm :=
      norm_tripleCharacteristicError_le_four M hM A hA n
    change
      ‖((a n - b n : ℝ) : ℂ)‖ ≤ 4 at hnorm
    rw [Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  have hsmall : ∀ n, b n ≤ T → (w n).re ≤ ρ ^ k := by
    intro n hn
    have hbase :
        ‖peakBase
            (normalizedForwardKroneckerAutocorrelation M hM A hA)
            1 n‖ ^ 2 ≤ ρ := by
      apply hcontract n
      simpa only [b, T] using hn
    dsimp [w]
    rw [forwardKroneckerPeakWeight_eq_norm_sq_pow,
      Complex.ofReal_re]
    exact pow_le_pow_left₀ (sq_nonneg _) hbase k
  have hreturn : ∀ i : ℕ, ∃ n : ℕ,
      T < b n ∧ σ ^ k ≤ (w n).re ∧ i ≤ n ∧ n < i + L := by
    intro i
    obtain ⟨n, hn, hin, hnupper⟩ := hreturnL i
    refine ⟨n, ?_, ?_, hin, hnupper⟩
    · dsimp [T]
      linarith [hn.1]
    · have hbasefloor :
          σ ≤
            ‖peakBase
                (normalizedForwardKroneckerAutocorrelation M hM A hA)
                1 n‖ ^ 2 := by
        have hwone := hn.2
        rw [forwardKroneckerPeakWeight_eq_norm_sq_pow,
          Complex.ofReal_re] at hwone
        simpa only [pow_one] using hwone
      dsimp [w]
      rw [forwardKroneckerPeakWeight_eq_norm_sq_pow,
        Complex.ofReal_re]
      exact pow_le_pow_left₀ hσ.le hbasefloor k
  have hzero :
      HasUniformComplexCesaroZero
        (fun n ↦ w n * ((a n - b n : ℝ) : ℂ)) := by
    dsimp [w, a, b]
    exact
      tripleCharacteristic_uniformLimitWeight_uniform_cesaro_zero
        M hM A hA
        (forwardKroneckerPeakWeight M hM A hA k)
        (forwardKroneckerPeakWeight_isUniformLimit M hM A hA k)
  have hresult :=
    WeightedSyndeticTransfer.isSyndetic_superlevel_of_weighted_error
      a b w c T γ 4 ρ σ k L
      hγ (by norm_num) hρ0 hσ hL hthreshold
      hw_nonneg herror hsmall hreturn hratio hzero
  simpa only [a, c] using hresult

end Chapter02.MultipleKhintchineBohrTriple
