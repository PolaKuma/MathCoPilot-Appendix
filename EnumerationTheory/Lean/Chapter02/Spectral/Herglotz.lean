import Chapter02.Spectral.CircleFourierUniqueness
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Prokhorov

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder

noncomputable section

namespace Chapter02.Herglotz

/-- The finite Toeplitz matrix attached to an integer sequence. -/
def toeplitz (φ : ℤ → ℂ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun m n => φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ))

/-- A complex matrix whose quadratic forms are all real is Hermitian. -/
lemma hermitian_of_im_quadratic_zero {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ)
    (hM : ∀ x : n → ℂ, (dotProduct (star x) (M.mulVec x)).im = 0) : M.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hii := hM (Pi.single i 1)
  have hjj := hM (Pi.single j 1)
  have hp := hM (Pi.single i 1 + Pi.single j 1)
  have hI := hM (Pi.single i 1 + Pi.single j Complex.I)
  simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single,
    single_dotProduct] at hii hjj hp hI
  apply Complex.ext
  · change (M j i).re = (M i j).re
    linarith
  · change -(M j i).im = (M i j).im
    linarith

/-- Positive definiteness of the sequence is exactly positivity of all its finite
Toeplitz matrices (in the direction needed for Herglotz). -/
theorem toeplitz_posSemidef {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N : ℕ) :
    (toeplitz φ N).PosSemidef := by
  have hquad : ∀ x : Fin (N + 1) → ℂ,
      let q := dotProduct (star x) ((toeplitz φ N).mulVec x)
      q.im = 0 ∧ 0 ≤ q.re := by
    intro x
    have h := hφ N (fun m => star (x m))
    dsimp only at h ⊢
    have heq : dotProduct (star x) ((toeplitz φ N).mulVec x) =
        ∑ m, ∑ n, star (x m) * star (star (x n)) *
          φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) := by
      simp only [toeplitz, dotProduct, Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      simp
      ring
    rw [heq]
    exact h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hermitian_of_im_quadratic_zero _ (fun x => (hquad x).1), ?_⟩
  intro x
  rw [Complex.nonneg_iff]
  exact ⟨(hquad x).2, (hquad x).1.symm⟩

theorem phi_zero_nonneg {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) : 0 ≤ φ 0 := by
  have h := hφ 0 (fun _ => 1)
  norm_num at h
  rw [Complex.nonneg_iff]
  exact ⟨h.2, h.1.symm⟩

theorem phi_neg_nat {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (n : ℕ) :
    φ (-(n : ℤ)) = star (φ n) := by
  have h := (toeplitz_posSemidef hφ n).isHermitian.apply
    (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
    (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
  simp [toeplitz] at h
  exact h.symm

/-- Orthogonality of the integer characters for normalized Haar measure on the
unit additive circle. -/
theorem integral_fourier (k : ℤ) :
    ∫ x : AddCircle 1, fourier k x ∂AddCircle.haarAddCircle =
      if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) 0 k
  rw [MeasureTheory.ContinuousMap.inner_toLp] at h
  simpa [eq_comm] using h

/-- The Cesàro-smoothed Toeplitz polynomial.  Pointwise positivity is the
finite-dimensional heart of the Herglotz construction. -/
noncomputable def fejerPolynomial (φ : ℤ → ℂ) (N : ℕ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ((N + 1 : ℂ)⁻¹) •
    ∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
      (φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ))) •
        (star (fourier (T := (1 : ℝ)) ((m : ℕ) : ℤ)) *
          fourier (T := (1 : ℝ)) ((n : ℕ) : ℤ))

/-- Expanding a Fourier moment of the Fejér polynomial reduces it to the
finite Toeplitz sum selected by character orthogonality. -/
theorem integral_fourier_mul_fejerPolynomial (φ : ℤ → ℂ) (N : ℕ) (k : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) k x *
        fejerPolynomial φ N x ∂AddCircle.haarAddCircle =
      (N + 1 : ℂ)⁻¹ *
        ∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
          φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
            if k - (m : ℕ) + (n : ℕ) = 0 then 1 else 0 := by
  rw [fejerPolynomial]
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
  rw [hfun, integral_const_mul]
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
            rw [mul_left_comm, ← fourier_add]
            ring
        _ = (N + 1 : ℂ)⁻¹ *
              (φ (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) *
              (if k - (m : ℕ) + (n : ℕ) = 0 then 1 else 0)) := by
            rw [integral_fourier]
    · intro n _
      exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
        (HasCompactSupport.of_compactSpace _)
  · intro m _
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)

private def pairSet (N k : ℕ) : Finset (Fin (N + 1) × Fin (N + 1)) :=
  Finset.univ.filter fun p =>
    (k : ℤ) - ((p.1 : ℕ) : ℤ) + ((p.2 : ℕ) : ℤ) = 0

private def pairEquiv (N k : ℕ) (hk : k ≤ N) : Fin (N + 1 - k) ≃ ↥(pairSet N k) where
  toFun t := ⟨(⟨t.val + k, by omega⟩, ⟨t.val, by omega⟩), by simp [pairSet]⟩
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

private theorem pairSet_card (N k : ℕ) (hk : k ≤ N) :
    (pairSet N k).card = N + 1 - k := by
  have h := Fintype.card_congr (pairEquiv N k hk)
  simpa using h.symm

private theorem pair_sum_nat (φ : ℤ → ℂ) (N k : ℕ) (hk : k ≤ N) :
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

/-- The exact positive Fourier moments of the Fejér polynomial. -/
theorem integral_fourier_mul_fejerPolynomial_nat (φ : ℤ → ℂ) (N k : ℕ)
    (hk : k ≤ N) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x *
        fejerPolynomial φ N x ∂AddCircle.haarAddCircle =
      (N + 1 : ℂ)⁻¹ * (((N + 1 - k : ℕ) : ℂ) * φ k) := by
  rw [integral_fourier_mul_fejerPolynomial, pair_sum_nat φ N k hk]

/-- Every Fejér density has total mass `φ 0`. -/
theorem integral_fejerPolynomial (φ : ℤ → ℂ) (N : ℕ) :
    ∫ x : AddCircle (1 : ℝ), fejerPolynomial φ N x
        ∂AddCircle.haarAddCircle = φ 0 := by
  have h := integral_fourier_mul_fejerPolynomial_nat φ N 0 (Nat.zero_le N)
  simp only [Nat.cast_zero, fourier_zero, ContinuousMap.one_apply, one_mul,
    Nat.sub_zero] at h
  calc
    (∫ x : AddCircle (1 : ℝ), fejerPolynomial φ N x
        ∂AddCircle.haarAddCircle) =
        (N + 1 : ℂ)⁻¹ * ((N + 1 : ℂ) * φ 0) := by simpa using h
    _ = φ 0 := by
      field_simp

theorem fejerPolynomial_nonneg {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ)
    (N : ℕ) (x : AddCircle (1 : ℝ)) : 0 ≤ fejerPolynomial φ N x := by
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (toeplitz_posSemidef hφ N)).2
    (fun m => fourier (T := (1 : ℝ)) ((m : ℕ) : ℤ) x)
  have heq : fejerPolynomial φ N x = (N + 1 : ℂ)⁻¹ *
      dotProduct (star (fun m : Fin (N + 1) =>
        fourier (T := (1 : ℝ)) ((m : ℕ) : ℤ) x))
        ((toeplitz φ N).mulVec
          (fun m => fourier (T := (1 : ℝ)) ((m : ℕ) : ℤ) x)) := by
    simp only [fejerPolynomial, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
      ContinuousMap.mul_apply, ContinuousMap.star_apply]
    simp only [smul_eq_mul, toeplitz, dotProduct, Matrix.mulVec]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp
    ring
  rw [Complex.nonneg_iff] at hq ⊢
  rw [heq]
  have hc : (N + 1 : ℂ)⁻¹ = (((N + 1 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv]
    congr 2
    norm_num
  rw [hc]
  constructor
  · rw [Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) hq.1
  · rw [Complex.im_ofReal_mul]
    simpa only [← hq.2, mul_zero]

/-- The nonnegative real-valued Fejér density, bundled as a continuous map. -/
noncomputable def fejerDensity {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N : ℕ) :
    C(AddCircle (1 : ℝ), NNReal) where
  toFun x := ⟨(fejerPolynomial φ N x).re,
    (Complex.nonneg_iff.mp (fejerPolynomial_nonneg hφ N x)).1⟩
  continuous_toFun := Continuous.subtype_mk
    (Complex.continuous_re.comp (fejerPolynomial φ N).continuous)
    _

@[simp] theorem coe_fejerDensity {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ)
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ((fejerDensity hφ N x : NNReal) : ℝ) = (fejerPolynomial φ N x).re := rfl

@[simp] theorem coe_fejerDensity_complex {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ)
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    ((fejerDensity hφ N x : NNReal) : ℂ) = fejerPolynomial φ N x := by
  apply Complex.ext
  · simp [coe_fejerDensity]
  · simp [(Complex.nonneg_iff.mp (fejerPolynomial_nonneg hφ N x)).2]

/-- The finite measure whose Radon--Nikodym density is the Fejér polynomial. -/
noncomputable def fejerFiniteMeasure {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N : ℕ) :
    FiniteMeasure (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle.withDensity (fun x => fejerDensity hφ N x), by
    apply isFiniteMeasure_withDensity
    rw [lintegral_coe_eq_integral]
    · exact ENNReal.ofReal_ne_top
    · exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
        (HasCompactSupport.of_compactSpace _)⟩

/-- Positive Fourier moments of the finite Fejér measures. -/
theorem integral_fourier_fejerFiniteMeasure {φ : ℤ → ℂ}
    (hφ : IsPositiveDefinite φ) (N k : ℕ) (hk : k ≤ N) :
    ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
        ∂(fejerFiniteMeasure hφ N : Measure (AddCircle (1 : ℝ))) =
      (N + 1 : ℂ)⁻¹ * (((N + 1 - k : ℕ) : ℂ) * φ k) := by
  change (∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x
      ∂AddCircle.haarAddCircle.withDensity (fun x => fejerDensity hφ N x)) = _
  rw [integral_withDensity_eq_integral_smul₀
    (fejerDensity hφ N).continuous.aemeasurable]
  calc
    (∫ x : AddCircle (1 : ℝ), fejerDensity hφ N x •
          fourier (T := (1 : ℝ)) (k : ℤ) x ∂AddCircle.haarAddCircle) =
        ∫ x : AddCircle (1 : ℝ), fourier (T := (1 : ℝ)) (k : ℤ) x *
          fejerPolynomial φ N x ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [NNReal.smul_def, Complex.real_smul, coe_fejerDensity_complex]
      ring
    _ = _ := integral_fourier_mul_fejerPolynomial_nat φ N k hk

/-- The finite Fejér measures all have the same mass `φ 0`. -/
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

/-- Probability normalization of the Fejér measure.  When the common mass is
zero this is Mathlib's harmless default probability measure; that case is
handled separately in the Herglotz proof. -/
noncomputable def fejerProbability {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (N : ℕ) :
    ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  (fejerFiniteMeasure hφ N).normalize

/-- Compactness supplies a weakly convergent subsequence of normalized Fejér measures. -/
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

/-- Identification of the positive Fourier moments of a weak subsequential limit. -/
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

/-- Rescale a weak probability limit by the common Fejér mass. -/
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

/-- All integer Fourier moments of the rescaled weak limit equal the original sequence. -/
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
      rfl

private noncomputable def circleEquiv : AddCircle (1 : ℝ) ≃ₜ Circle :=
  AddCircle.homeomorphCircle one_ne_zero

theorem circle_character_comp_equiv (n : ℤ) (x : AddCircle (1 : ℝ)) :
    (((circleEquiv x : Circle) : ℂ) ^ n) = fourier (T := (1 : ℝ)) n x := by
  rw [circleEquiv, AddCircle.homeomorphCircle_apply, fourier_apply,
    AddCircle.toCircle_zsmul]
  rfl

noncomputable def pushToCircle (ν : FiniteMeasure (AddCircle (1 : ℝ))) : CircleMeasureData where
  μ := ν.map circleEquiv
  isFinite := inferInstance

theorem circleFourierCoefficient_pushToCircle
    (ν : FiniteMeasure (AddCircle (1 : ℝ))) (n : ℤ) :
    circleFourierCoefficient (pushToCircle ν) n =
      ∫ x, fourier (T := (1 : ℝ)) n x ∂(ν : Measure (AddCircle (1 : ℝ))) := by
  change (∫ z : Circle, (z : ℂ) ^ n
      ∂Measure.map circleEquiv (ν : Measure (AddCircle (1 : ℝ)))) = _
  rw [circleEquiv.isClosedEmbedding.integral_map]
  apply integral_congr_ae
  filter_upwards [] with x
  exact circle_character_comp_equiv n x

/-- Finite positive circle measures are determined by all Laurent moments. -/
theorem measure_eq_of_circleFourierCoefficient (μ ν : CircleMeasureData)
    (h : ∀ n : ℤ, circleFourierCoefficient μ n = circleFourierCoefficient ν n) : μ = ν := by
  have hall : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z ∂μ.μ = ∫ z, q z ∂ν.μ := by
    intro q hq
    refine Submodule.span_induction (p := fun q _ =>
      ∫ z, q z ∂μ.μ = ∫ z, q z ∂ν.μ) ?_ ?_ ?_ ?_ hq
    · intro q hq
      obtain ⟨n, rfl⟩ := hq
      exact h n
    · simp
    · intro f g _ _ hf hg
      change (∫ z, f z + g z ∂μ.μ) = ∫ z, f z + g z ∂ν.μ
      rw [integral_add, integral_add, hf, hg]
      · exact Continuous.integrable_of_hasCompactSupport f.continuous
          (HasCompactSupport.of_compactSpace _)
      · exact Continuous.integrable_of_hasCompactSupport g.continuous
          (HasCompactSupport.of_compactSpace _)
      · exact Continuous.integrable_of_hasCompactSupport f.continuous
          (HasCompactSupport.of_compactSpace _)
      · exact Continuous.integrable_of_hasCompactSupport g.continuous
          (HasCompactSupport.of_compactSpace _)
    · intro a f _ hf
      simp only [ContinuousMap.smul_apply]
      rw [integral_smul, integral_smul, hf]
  have heq : μ.μ = ν.μ := by
    apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
      CircleFourierUniqueness.laurentBCFAlgebra_separates
    intro q hq
    exact hall q.toContinuousMap hq
  cases μ
  cases ν
  cases heq
  rfl

theorem eq_zero_of_phi_zero {φ : ℤ → ℂ} (hφ : IsPositiveDefinite φ) (h0 : φ 0 = 0) :
    φ = 0 := by
  have hnat : ∀ n : ℕ, φ n = 0 := by
    intro n
    let i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    let x : Fin (n + 1) → ℂ := Pi.single i0 1
    have hquad : dotProduct (star x) ((toeplitz φ n).mulVec x) = 0 := by
      simp [x, i0, toeplitz, h0]
    have hv := ((toeplitz_posSemidef hφ n).dotProduct_mulVec_zero_iff x).mp hquad
    have hn := congrFun hv (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
    simpa [x, i0, toeplitz, Matrix.mulVec] using hn
  funext j
  cases j with
  | ofNat n => exact hnat n
  | negSucc n =>
      change φ (-((n + 1 : ℕ) : ℤ)) = 0
      rw [phi_neg_nat hφ, hnat]
      simp

/-- Herglotz's representation theorem for positive-definite sequences on `ℤ`. -/
theorem herglotz : HerglotzStatement := by
  intro φ hφ
  by_cases h0 : φ 0 = 0
  · have hz := eq_zero_of_phi_zero hφ h0
    let μ0 : CircleMeasureData := ⟨0, inferInstance⟩
    refine ⟨μ0, ?_, ?_⟩
    · intro n
      simp [μ0, circleFourierCoefficient, hz]
    · intro ν hν
      apply measure_eq_of_circleFourierCoefficient
      intro n
      rw [hν n]
      simp [μ0, circleFourierCoefficient, hz]
  · obtain ⟨μ, ψ, hψ, ht⟩ := exists_fejerProbability_limit hφ
    let ρ := pushToCircle (scaledProbabilityLimit hφ μ)
    have hρ : ∀ n : ℤ, circleFourierCoefficient ρ n = φ n := by
      intro n
      change circleFourierCoefficient (pushToCircle (scaledProbabilityLimit hφ μ)) n = φ n
      rw [circleFourierCoefficient_pushToCircle]
      exact integral_fourier_scaledProbabilityLimit hφ h0 μ ψ hψ ht n
    refine ⟨ρ, hρ, ?_⟩
    intro ν hν
    apply measure_eq_of_circleFourierCoefficient
    intro n
    rw [hρ n, hν n]

end Chapter02.Herglotz
