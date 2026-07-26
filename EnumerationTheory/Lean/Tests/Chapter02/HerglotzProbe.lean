import Chapter02.Spectral.Herglotz

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder

noncomputable section

namespace Chapter02.HerglotzProbe

theorem integral_fourier_mul_fejerPolynomial (φ : ℤ → ℂ) (N : ℕ) (k : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) k x *
        Chapter02.Herglotz.fejerPolynomial φ N x ∂AddCircle.haarAddCircle =
      (N + 1 : ℂ)⁻¹ *
        ∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
          φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
            if k - (m : ℕ) + (n : ℕ) = 0 then 1 else 0 := by
  rw [Chapter02.Herglotz.fejerPolynomial]
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.star_apply, smul_eq_mul]
  let S : AddCircle (1 : ℝ) → ℂ := fun x =>
    ∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
      φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
        (star (fourier (T := (1 : ℝ)) ((m : ℕ) : ℤ) x) *
          fourier (T := (1 : ℝ)) ((n : ℕ) : ℤ) x)
  change (∫ x, fourier (T := (1 : ℝ)) k x * ((N + 1 : ℂ)⁻¹ * S x)
      ∂AddCircle.haarAddCircle) = _
  have hfun : (fun x : AddCircle (1 : ℝ) =>
      fourier (T := (1 : ℝ)) k x * ((N + 1 : ℂ)⁻¹ * S x)) =
      fun x => (N + 1 : ℂ)⁻¹ * (fourier (T := (1 : ℝ)) k x * S x) := by
    funext x
    ring
  rw [hfun]
  rw [integral_const_mul]
  dsimp only [S]
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_finset_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      calc
        (N + 1 : ℂ)⁻¹ *
            (∫ a : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) k a *
              (φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
                (star (fourier (T := (1 : ℝ)) ((m : ℕ) : ℤ) a) *
                  fourier (T := (1 : ℝ)) ((n : ℕ) : ℤ) a))
              ∂AddCircle.haarAddCircle) =
            (N + 1 : ℂ)⁻¹ *
              (φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
                ∫ a : AddCircle (1 : ℝ),
                  fourier (T := (1 : ℝ))
                    (k - ((m : ℕ) : ℤ) + ((n : ℕ) : ℤ)) a
                    ∂AddCircle.haarAddCircle) := by
            congr 1
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [] with a
            rw [Complex.star_def, ← fourier_neg, ← fourier_add]
            rw [mul_left_comm]
            rw [← fourier_add]
            ring
        _ = (N + 1 : ℂ)⁻¹ *
              (φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
              (if k - (m : ℕ) + (n : ℕ) = 0 then 1 else 0)) := by
            rw [Chapter02.Herglotz.integral_fourier]
    · intro n _
      exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
        (HasCompactSupport.of_compactSpace _)
  · intro m _
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)

def pairSet (N k : ℕ) : Finset (Fin (N + 1) × Fin (N + 1)) :=
  Finset.univ.filter fun p =>
    (k : ℤ) - ((p.1 : ℕ) : ℤ) + ((p.2 : ℕ) : ℤ) = 0

def pairEquiv (N k : ℕ) (hk : k ≤ N) : Fin (N + 1 - k) ≃ ↥(pairSet N k) where
  toFun t := ⟨(⟨t.val + k, by omega⟩, ⟨t.val, by omega⟩), by
    simp [pairSet]⟩
  invFun p := ⟨p.val.2.val, by
    have hp := p.property
    simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    omega⟩
  left_inv t := by ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      change p.val.2.val + k = p.val.1.val
      have hp := p.property
      simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      omega
    · apply Fin.ext
      rfl

theorem pairSet_card (N k : ℕ) (hk : k ≤ N) : (pairSet N k).card = N + 1 - k := by
  have h := Fintype.card_congr (pairEquiv N k hk)
  simpa using h.symm

theorem pair_sum_nat (φ : ℤ → ℂ) (N k : ℕ) (hk : k ≤ N) :
    (∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
      φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
        if (k : ℤ) - (m : ℕ) + (n : ℕ) = 0 then 1 else 0) =
      ((N + 1 - k : ℕ) : ℂ) * φ k := by
  rw [← Fintype.sum_prod_type (fun p : Fin (N + 1) × Fin (N + 1) =>
    φ (((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ)) *
      if (k : ℤ) - (p.1 : ℕ) + (p.2 : ℕ) = 0 then 1 else 0)]
  change (∑ p : Fin (N + 1) × Fin (N + 1),
    φ (((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ)) *
      if (k : ℤ) - (p.1 : ℕ) + (p.2 : ℕ) = 0 then 1 else 0) = _
  rw [show (∑ p : Fin (N + 1) × Fin (N + 1),
      φ (((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ)) *
        if (k : ℤ) - (p.1 : ℕ) + (p.2 : ℕ) = 0 then 1 else 0) =
      ∑ p ∈ pairSet N k, φ (((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ)) by
    rw [pairSet, Finset.sum_filter]
    simp]
  calc
    (∑ p ∈ pairSet N k, φ (((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ))) =
        ∑ _p ∈ pairSet N k, φ k := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      congr 1
      omega
    _ = ((pairSet N k).card : ℕ) • φ k := by simp
    _ = ((N + 1 - k : ℕ) : ℂ) * φ k := by
      rw [pairSet_card N k hk]
      simp

@[simp] theorem coe_fejerDensity_complex {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ)
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ((Chapter02.Herglotz.fejerDensity hφ N x : NNReal) : ℂ) =
      Chapter02.Herglotz.fejerPolynomial φ N x := by
  apply Complex.ext
  · simp [Chapter02.Herglotz.coe_fejerDensity]
  · simp [(Complex.nonneg_iff.mp
      (Chapter02.Herglotz.fejerPolynomial_nonneg hφ N x)).2]

noncomputable def fejerFiniteMeasure {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N : ℕ) :
    FiniteMeasure (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle.withDensity
      (fun x => Chapter02.Herglotz.fejerDensity hφ N x), by
    apply isFiniteMeasure_withDensity
    rw [lintegral_coe_eq_integral]
    · exact ENNReal.ofReal_ne_top
    · exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
        (HasCompactSupport.of_compactSpace _)⟩

theorem integral_fourier_fejerFiniteMeasure {φ : ℤ → ℂ}
    (hφ : IsPositiveDefinite φ) (N k : ℕ) (hk : k ≤ N) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
        ∂(fejerFiniteMeasure hφ N : Measure (AddCircle (1 : ℝ))) =
      (N + 1 : ℂ)⁻¹ * (((N + 1 - k : ℕ) : ℂ) * φ k) := by
  change (∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
      ∂AddCircle.haarAddCircle.withDensity
        (fun x => Chapter02.Herglotz.fejerDensity hφ N x)) = _
  rw [integral_withDensity_eq_integral_smul₀
    (Chapter02.Herglotz.fejerDensity hφ N).continuous.aemeasurable]
  calc
    (∫ x : AddCircle (1 : ℝ),
        Chapter02.Herglotz.fejerDensity hφ N x •
          fourier (T := (1 : ℝ)) (k : ℤ) x ∂AddCircle.haarAddCircle) =
        ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x *
          Chapter02.Herglotz.fejerPolynomial φ N x ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [NNReal.smul_def, Complex.real_smul]
      rw [Chapter02.Herglotz.coe_fejerDensity_complex]
      ring
    _ = _ := Chapter02.Herglotz.integral_fourier_mul_fejerPolynomial_nat φ N k hk

theorem coe_mass_fejerFiniteMeasure {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N : ℕ) :
    ((fejerFiniteMeasure hφ N).mass : ℂ) = φ 0 := by
  have h := integral_fourier_fejerFiniteMeasure hφ N 0 (Nat.zero_le N)
  calc
    ((fejerFiniteMeasure hφ N).mass : ℂ) =
        (N + 1 : ℂ)⁻¹ * ((N + 1 : ℂ) * φ 0) := by simpa using h
    _ = φ 0 := by field_simp

theorem mass_fejerFiniteMeasure_eq {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N M : ℕ) :
    (fejerFiniteMeasure hφ N).mass = (fejerFiniteMeasure hφ M).mass := by
  have h : ((fejerFiniteMeasure hφ N).mass : ℂ) =
      ((fejerFiniteMeasure hφ M).mass : ℂ) :=
    (coe_mass_fejerFiniteMeasure hφ N).trans (coe_mass_fejerFiniteMeasure hφ M).symm
  exact_mod_cast h

noncomputable def fejerProbability {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N : ℕ) :
    ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  (fejerFiniteMeasure hφ N).normalize

theorem exists_fejerProbability_limit {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) :
    ∃ (μ : ProbabilityMeasure (AddCircle (1 : ℝ))) (ψ : ℕ → ℕ), StrictMono ψ ∧
      Tendsto (fun n => fejerProbability hφ (ψ n)) atTop (𝓝 μ) := by
  simpa [Function.comp_def] using
    (CompactSpace.tendsto_subseq (fun N => fejerProbability hφ N))

theorem fejerFiniteMeasure_ne_zero {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ)
    (h0 : φ 0 ≠ 0) (N : ℕ) : fejerFiniteMeasure hφ N ≠ 0 := by
  intro hz
  apply h0
  rw [← coe_mass_fejerFiniteMeasure hφ N, hz]
  simp

theorem integral_fourier_fejerProbability {φ : ℤ → ℂ}
    (hφ : IsPositiveDefinite φ) (h0 : φ 0 ≠ 0) (N k : ℕ) (hk : k ≤ N) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
        ∂(fejerProbability hφ N : Measure (AddCircle (1 : ℝ))) =
      (fejerFiniteMeasure hφ N).mass⁻¹ •
        ((N + 1 : ℂ)⁻¹ * (((N + 1 - k : ℕ) : ℂ) * φ k)) := by
  rw [fejerProbability, FiniteMeasure.toMeasure_normalize_eq_of_nonzero
    _ (fejerFiniteMeasure_ne_zero hφ h0 N), integral_smul_nnreal_measure,
    integral_fourier_fejerFiniteMeasure hφ N k hk]

theorem tendsto_fejerMomentFactor (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) (z : ℂ) :
    Tendsto (fun n => (ψ n + 1 : ℂ)⁻¹ *
      (((ψ n + 1 - k : ℕ) : ℂ) * z)) atTop (𝓝 z) := by
  have ht : Tendsto (fun n => ψ n + 1 - k) atTop atTop :=
    (tendsto_sub_atTop_nat k).comp ((tendsto_add_atTop_nat 1).comp hψ.tendsto_atTop)
  have hr := (tendsto_natCast_div_add_atTop (k : ℂ)).comp ht
  have hev : ∀ᶠ n in atTop, k ≤ ψ n := hψ.tendsto_atTop (eventually_ge_atTop k)
  have hr' : Tendsto (fun n => (ψ n + 1 : ℂ)⁻¹ *
      ((ψ n + 1 - k : ℕ) : ℂ)) atTop (𝓝 1) := by
    apply hr.congr'
    filter_upwards [hev] with n hn
    dsimp only [Function.comp_apply]
    rw [div_eq_mul_inv]
    have hd : (((ψ n + 1 - k : ℕ) : ℂ) + (k : ℂ)) = (ψ n + 1 : ℂ) := by
      norm_cast
      omega
    rw [hd]
    ring
  convert hr'.mul_const z using 1
  · funext n
    ring
  · simp

theorem integral_fourier_probabilityLimit {φ : ℤ → ℂ}
    (hφ : IsPositiveDefinite φ) (h0 : φ 0 ≠ 0)
    (μ : ProbabilityMeasure (AddCircle (1 : ℝ))) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (ht : Tendsto (fun n => fejerProbability hφ (ψ n)) atTop (𝓝 μ)) (k : ℕ) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
        ∂(μ : Measure (AddCircle (1 : ℝ))) =
      (fejerFiniteMeasure hφ 0).mass⁻¹ • φ k := by
  let f : BoundedContinuousFunction (AddCircle (1 : ℝ)) ℂ :=
    BoundedContinuousFunction.mkOfCompact (fourier (T := (1 : ℝ)) (k : ℤ))
  have hint := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp ht f
  have hfac := (tendsto_fejerMomentFactor ψ hψ k (φ k)).const_smul
    (fejerFiniteMeasure hφ 0).mass⁻¹
  have hev : ∀ᶠ n in atTop, k ≤ ψ n := hψ.tendsto_atTop (eventually_ge_atTop k)
  have heq : ∀ᶠ n in atTop,
      (∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
          ∂(fejerProbability hφ (ψ n) : Measure (AddCircle (1 : ℝ)))) =
        (fejerFiniteMeasure hφ 0).mass⁻¹ •
          ((ψ n + 1 : ℂ)⁻¹ * (((ψ n + 1 - k : ℕ) : ℂ) * φ k)) := by
    filter_upwards [hev] with n hn
    rw [integral_fourier_fejerProbability hφ h0 (ψ n) k hn,
      mass_fejerFiniteMeasure_eq hφ (ψ n) 0]
  have hcalc := hfac.congr' (heq.mono fun _ h => h.symm)
  have hint' : Tendsto (fun n =>
      ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
        ∂(fejerProbability hφ (ψ n) : Measure (AddCircle (1 : ℝ)))) atTop
      (𝓝 (∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
        ∂(μ : Measure (AddCircle (1 : ℝ))))) := by
    simpa [f] using hint
  exact tendsto_nhds_unique hint' hcalc

noncomputable def scaledProbabilityLimit {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ)
    (μ : ProbabilityMeasure (AddCircle (1 : ℝ))) : FiniteMeasure (AddCircle (1 : ℝ)) :=
  (fejerFiniteMeasure hφ 0).mass • μ.toFiniteMeasure

theorem integral_fourier_scaledProbabilityLimit_nat {φ : ℤ → ℂ}
    (hφ : IsPositiveDefinite φ) (h0 : φ 0 ≠ 0)
    (μ : ProbabilityMeasure (AddCircle (1 : ℝ))) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (ht : Tendsto (fun n => fejerProbability hφ (ψ n)) atTop (𝓝 μ)) (k : ℕ) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
        ∂(scaledProbabilityLimit hφ μ : Measure (AddCircle (1 : ℝ))) = φ k := by
  change (∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
      ∂((fejerFiniteMeasure hφ 0).mass • (μ : Measure (AddCircle (1 : ℝ))))) = _
  rw [integral_smul_nnreal_measure,
    integral_fourier_probabilityLimit hφ h0 μ ψ hψ ht k, smul_smul]
  have hm : (fejerFiniteMeasure hφ 0).mass ≠ 0 :=
    (fejerFiniteMeasure hφ 0).mass_nonzero_iff.mpr (fejerFiniteMeasure_ne_zero hφ h0 0)
  rw [mul_inv_cancel₀ hm, one_smul]

theorem integral_fourier_scaledProbabilityLimit {φ : ℤ → ℂ}
    (hφ : IsPositiveDefinite φ) (h0 : φ 0 ≠ 0)
    (μ : ProbabilityMeasure (AddCircle (1 : ℝ))) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (ht : Tendsto (fun n => fejerProbability hφ (ψ n)) atTop (𝓝 μ)) (j : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) j x
        ∂(scaledProbabilityLimit hφ μ : Measure (AddCircle (1 : ℝ))) = φ j := by
  cases j with
  | ofNat k => exact integral_fourier_scaledProbabilityLimit_nat hφ h0 μ ψ hψ ht k
  | negSucc k =>
      change (∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (-((k + 1 : ℕ) : ℤ)) x
        ∂(scaledProbabilityLimit hφ μ : Measure (AddCircle (1 : ℝ)))) =
          φ (-((k + 1 : ℕ) : ℤ))
      simp_rw [fourier_neg]
      rw [integral_conj, integral_fourier_scaledProbabilityLimit_nat hφ h0 μ ψ hψ ht,
        phi_neg_nat hφ]

end Chapter02.HerglotzProbe
