import Chapter02.Spectral.CircleLaurent
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

open Classical Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace Chapter02.CircleFourierUniqueness

def laurentBCFAlgebra : StarSubalgebra ℂ (BoundedContinuousFunction Circle ℂ) :=
  StarSubalgebra.comap (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)
    CircleLaurent.algebra

theorem laurentBCFAlgebra_separates :
    (StarSubalgebra.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)
      laurentBCFAlgebra).SeparatesPoints := by
  rw [show StarSubalgebra.map (BoundedContinuousFunction.toContinuousMapStarₐ ℂ)
      laurentBCFAlgebra = CircleLaurent.algebra by
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro hq
      exact ⟨BoundedContinuousFunction.mkOfCompact q, hq, rfl⟩]
  exact CircleLaurent.algebra_separatesPoints

/-- An integrable real function on the circle with all Laurent moments zero
vanishes almost everywhere. -/
theorem real_ae_zero_of_laurent_moments (μ : CircleMeasureData)
    {r : Circle → ℝ} (hr : Integrable r μ.μ)
    (hmom : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z * (r z : ℂ) ∂μ.μ = 0) : r =ᵐ[μ.μ] 0 := by
  let p : Circle → NNReal := fun z => (r z).toNNReal
  let n : Circle → NNReal := fun z => (-r z).toNNReal
  have hp : AEMeasurable p μ.μ :=
    hr.aestronglyMeasurable.aemeasurable.real_toNNReal
  have hn : AEMeasurable n μ.μ :=
    hr.neg.aestronglyMeasurable.aemeasurable.real_toNNReal
  have hp_lt : ∫⁻ z, (p z : ℝ≥0∞) ∂μ.μ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono (f := fun z => (p z : ℝ≥0∞))
      (g := fun z => ‖r z‖ₑ) fun z => ?_) ?_
    · simp only [p]
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (le_abs_self (r z))
    · exact (hasFiniteIntegral_def r μ.μ).mp hr.hasFiniteIntegral
  have hn_lt : ∫⁻ z, (n z : ℝ≥0∞) ∂μ.μ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono (f := fun z => (n z : ℝ≥0∞))
      (g := fun z => ‖r z‖ₑ) fun z => ?_) ?_
    · simp only [n]
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (neg_le_abs (r z))
    · exact (hasFiniteIntegral_def r μ.μ).mp hr.hasFiniteIntegral
  let P := μ.μ.withDensity fun z => (p z : ℝ≥0∞)
  let N := μ.μ.withDensity fun z => (n z : ℝ≥0∞)
  letI : IsFiniteMeasure P := isFiniteMeasure_withDensity hp_lt.ne
  letI : IsFiniteMeasure N := isFiniteMeasure_withDensity hn_lt.ne
  have hp_real : Integrable (fun z => (p z : ℝ)) μ.μ := by
    apply hr.norm.mono' hp.coe_nnreal_real.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : 0 ≤ r z
    · simp [p, Real.coe_toNNReal', hz, abs_of_nonneg hz]
    · have hz' : r z ≤ 0 := le_of_not_ge hz
      simp [p, Real.coe_toNNReal', hz', abs_of_nonpos hz']
  have hn_real : Integrable (fun z => (n z : ℝ)) μ.μ := by
    apply hr.norm.mono' hn.coe_nnreal_real.aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : 0 ≤ r z
    · simp [n, Real.coe_toNNReal', hz, abs_of_nonneg hz]
    · have hz' : r z ≤ 0 := le_of_not_ge hz
      simp [n, Real.coe_toNNReal', hz', abs_of_nonpos hz']
  have hPN : P = N := by
    apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
      laurentBCFAlgebra_separates
    intro q hq
    dsimp [P, N]
    rw [integral_withDensity_eq_integral_smul₀ hp q,
      integral_withDensity_eq_integral_smul₀ hn q]
    have hqmem : q.toContinuousMap ∈ CircleLaurent.span := hq
    have hzero := hmom q.toContinuousMap hqmem
    have hzero' : ∫ z, q z * (r z : ℂ) ∂μ.μ = 0 := hzero
    have hqr : Integrable (fun z => q z * (r z : ℂ)) μ.μ :=
      hr.ofReal.bdd_mul q.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => q.norm_coe_le_norm z)
    have hqn : Integrable (fun z => (n z : ℝ) • q z) μ.μ := by
      have hnC : Integrable (fun z => (n z : ℂ)) μ.μ := hn_real.ofReal
      simpa [smul_eq_mul, mul_comm] using
        hnC.bdd_mul q.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => q.norm_coe_le_norm z)
    calc
      (∫ z, (p z : NNReal) • q z ∂μ.μ) =
          ∫ z, q z * (r z : ℂ) + (n z : ℝ) • q z ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [NNReal.smul_def, Complex.real_smul, p, n, Real.coe_toNNReal']
        by_cases hz : 0 ≤ r z
        · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
          norm_num
          ring
        · have hz' : r z ≤ 0 := le_of_not_ge hz
          rw [max_eq_right hz', max_eq_left (neg_nonneg.mpr hz')]
          push_cast
          ring
      _ = (∫ z, q z * (r z : ℂ) ∂μ.μ) +
          ∫ z, (n z : ℝ) • q z ∂μ.μ := integral_add hqr hqn
      _ = ∫ z, (n z : NNReal) • q z ∂μ.μ := by
        rw [hzero', zero_add]
        congr 1
  have hden : (fun z => (p z : ℝ≥0∞)) =ᵐ[μ.μ] fun z => (n z : ℝ≥0∞) :=
    (withDensity_eq_iff_of_sigmaFinite hp.coe_nnreal_ennreal
      hn.coe_nnreal_ennreal).mp hPN
  filter_upwards [hden] with z hz
  have hz' : (p z : ℝ) = n z := by exact_mod_cast hz
  simp only [p, n, Real.coe_toNNReal'] at hz'
  dsimp
  by_cases h : 0 ≤ r z
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)] at hz'
    linarith
  · have h' : r z ≤ 0 := le_of_not_ge h
    rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')] at hz'
    linarith

/-- Fourier uniqueness for integrable complex functions on an arbitrary finite
Borel measure on the circle. -/
theorem complex_ae_zero_of_laurent_moments (μ : CircleMeasureData)
    {g : Circle → ℂ} (hg : Integrable g μ.μ)
    (hmom : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z * g z ∂μ.μ = 0) : g =ᵐ[μ.μ] 0 := by
  have hgc : Integrable (fun z => star (g z)) μ.μ := by
    refine ⟨hg.1.star, ?_⟩
    simpa [hasFiniteIntegral_def] using hg.2
  have hconj : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z * star (g z) ∂μ.μ = 0 := by
    intro q hq
    have hs := hmom (star q) (CircleLaurent.star_mem_span hq)
    calc
      (∫ z, q z * star (g z) ∂μ.μ) =
          ∫ z, star (star q z * g z) ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp [mul_comm]
      _ = star (∫ z, star q z * g z ∂μ.μ) := integral_conj
      _ = 0 := by rw [hs]; simp
  have hreMom : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z * ((g z).re : ℂ) ∂μ.μ = 0 := by
    intro q hq
    have hqg : Integrable (fun z => q z * g z) μ.μ :=
      hg.bdd_mul q.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ContinuousMap.norm_coe_le_norm q z)
    have hqgc : Integrable (fun z => q z * star (g z)) μ.μ :=
      hgc.bdd_mul q.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ContinuousMap.norm_coe_le_norm q z)
    calc
      (∫ z, q z * ((g z).re : ℂ) ∂μ.μ) =
          (2 : ℂ)⁻¹ * ((∫ z, q z * g z ∂μ.μ) +
            ∫ z, q z * star (g z) ∂μ.μ) := by
        rw [← integral_add hqg hqgc, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
        <;> ring
      _ = 0 := by rw [hmom q hq, hconj q hq]; simp
  have himMom : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z * ((g z).im : ℂ) ∂μ.μ = 0 := by
    intro q hq
    have hqg : Integrable (fun z => q z * g z) μ.μ :=
      hg.bdd_mul q.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ContinuousMap.norm_coe_le_norm q z)
    have hqgc : Integrable (fun z => q z * star (g z)) μ.μ :=
      hgc.bdd_mul q.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ContinuousMap.norm_coe_le_norm q z)
    calc
      (∫ z, q z * ((g z).im : ℂ) ∂μ.μ) =
          (2 * Complex.I : ℂ)⁻¹ * ((∫ z, q z * g z ∂μ.μ) -
            ∫ z, q z * star (g z) ∂μ.μ) := by
        rw [← integral_sub hqg hqgc, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
        <;> ring
      _ = 0 := by rw [hmom q hq, hconj q hq]; simp
  have hre := real_ae_zero_of_laurent_moments μ hg.re hreMom
  have him := real_ae_zero_of_laurent_moments μ hg.im himMom
  filter_upwards [hre, him] with z hzre hzim
  apply Complex.ext <;> simp_all

end Chapter02.CircleFourierUniqueness
