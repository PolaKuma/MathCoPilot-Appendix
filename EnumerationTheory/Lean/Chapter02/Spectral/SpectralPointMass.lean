import Chapter02.Common

noncomputable section

open Classical Filter
open scoped ComplexConjugate

namespace Chapter02
namespace SpectralPointMass

universe u

lemma measure_eq_mass_smul_dirac_of_ae_eq {X : Type u} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] (a : X) (h : ∀ᵐ x ∂μ, x = a) :
    μ = μ Set.univ • MeasureTheory.Measure.dirac a := by
  apply MeasureTheory.Measure.ext
  intro s hs
  by_cases ha : a ∈ s
  · have hmem : ∀ᵐ x ∂μ, x ∈ s := h.mono (fun _ hx => hx.symm ▸ ha)
    have hfull : μ s = μ Set.univ :=
      (MeasureTheory.ae_mem_iff_measure_eq hs.nullMeasurableSet).mp hmem
    rw [hfull]
    simp [MeasureTheory.Measure.smul_apply, hs, ha]
  · have hnotmem : ∀ᵐ x ∂μ, x ∉ s := h.mono (fun _ hx hxs => ha (hx ▸ hxs))
    have hzero : μ s = 0 :=
      MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr hnotmem
    rw [hzero]
    simp [MeasureTheory.Measure.smul_apply, hs, ha]

lemma eigen_iterate (D : HilbertOperatorData.{u}) (x : D.H) (lam : ℂ)
    (hx : D.U x = lam • x) (n : ℕ) :
    (D.U^[n]) x = lam ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_smul, hx]
      simp only [pow_succ, smul_smul]

lemma spectral_mass (D : HilbertOperatorData.{u}) (x : D.H)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ) :
    μ.μ.real Set.univ = ‖x‖ ^ 2 := by
  have h0 := hμ 0
  have h0' : (μ.μ.real Set.univ : ℂ) = (‖x‖ ^ 2 : ℂ) := by
    simpa [circleFourierCoefficient, inner_self_eq_norm_sq (𝕜 := ℂ)] using h0
  exact_mod_cast h0'

lemma spectral_first_moment (D : HilbertOperatorData.{u}) (x : D.H)
    (lam : Circle) (hx : D.U x = (lam : ℂ) • x)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ) :
    (∫ z, (z : ℂ) ∂μ.μ) = (lam : ℂ) * (‖x‖ ^ 2 : ℂ) := by
  have h1 := hμ 1
  rw [eigen_iterate D x (lam : ℂ) hx 1] at h1
  simpa [circleFourierCoefficient, inner_smul_right,
    inner_self_eq_norm_sq (𝕜 := ℂ)] using h1

lemma circle_norm_sub_sq (z lam : Circle) :
    ‖(z : ℂ) - (lam : ℂ)‖ ^ 2 =
      2 - 2 * Complex.re ((lam : ℂ) * conj (z : ℂ)) := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  simp [RCLike.inner_apply]
  ring

lemma spectral_variance_integral_zero (D : HilbertOperatorData.{u}) (x : D.H)
    (lam : Circle) (hx : D.U x = (lam : ℂ) • x)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ) :
    (∫ z, ‖(z : ℂ) - (lam : ℂ)‖ ^ 2 ∂μ.μ) = 0 := by
  letI : MeasurableSpace Circle := circleMeasurableSpace
  letI : BorelSpace Circle := circleBorelSpace
  letI : OpensMeasurableSpace Circle := circleOpensMeasurableSpace
  letI : MeasurableSpace (Submonoid.unitSphere ℂ) := circleMeasurableSpace
  letI : OpensMeasurableSpace (Submonoid.unitSphere ℂ) := ⟨le_rfl⟩
  letI : MeasureTheory.IsFiniteMeasure μ.μ := μ.isFinite
  have hzint : MeasureTheory.Integrable (fun z : Circle => (z : ℂ)) μ.μ := by
    apply MeasureTheory.Integrable.of_bound
      continuous_subtype_val.aestronglyMeasurable 1
    filter_upwards with z
    simp
  have hstarint : MeasureTheory.Integrable
      (fun z : Circle => conj (z : ℂ)) μ.μ := by
    apply MeasureTheory.Integrable.of_bound
      (continuous_star.comp continuous_subtype_val).aestronglyMeasurable 1
    filter_upwards with z
    simp
  have hterm : MeasureTheory.Integrable
      (fun z : Circle => (lam : ℂ) * conj (z : ℂ)) μ.μ :=
    hstarint.const_mul (lam : ℂ)
  have hre := hterm.re
  calc
    (∫ z, ‖(z : ℂ) - (lam : ℂ)‖ ^ 2 ∂μ.μ) =
        ∫ z, (2 : ℝ) - 2 * Complex.re ((lam : ℂ) * conj (z : ℂ)) ∂μ.μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with z
          exact circle_norm_sub_sq z lam
    _ = μ.μ.real Set.univ * 2 -
        2 * Complex.re ((lam : ℂ) * conj (∫ z, (z : ℂ) ∂μ.μ)) := by
          calc
            (∫ z, (2 : ℝ) -
                2 * Complex.re ((lam : ℂ) * conj (z : ℂ)) ∂μ.μ) =
                (∫ _z : Circle, (2 : ℝ) ∂μ.μ) -
                  ∫ z, 2 * Complex.re ((lam : ℂ) * conj (z : ℂ)) ∂μ.μ :=
              MeasureTheory.integral_sub (MeasureTheory.integrable_const 2)
                (hre.const_mul 2)
            _ = _ := by
              rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
              have hreint :
                  (∫ z, Complex.re ((lam : ℂ) * conj (z : ℂ)) ∂μ.μ) =
                    Complex.re (∫ z, (lam : ℂ) * conj (z : ℂ) ∂μ.μ) :=
                integral_re hterm
              rw [hreint, MeasureTheory.integral_const_mul, integral_conj]
              simp
    _ = 0 := by
      rw [spectral_mass D x μ hμ, spectral_first_moment D x lam hx μ hμ]
      have hlam : (lam : ℂ) * conj (lam : ℂ) = 1 := by
        rw [← Circle.coe_inv_eq_conj]
        simp
      have hrstar : conj (‖x‖ ^ 2 : ℂ) = (‖x‖ ^ 2 : ℂ) := by simp
      change ‖x‖ ^ 2 * 2 -
        2 * Complex.re ((lam : ℂ) * conj ((lam : ℂ) * (‖x‖ ^ 2 : ℂ))) = 0
      rw [map_mul, show conj (‖x‖ ^ 2 : ℂ) = (‖x‖ ^ 2 : ℂ) by exact hrstar,
        ← mul_assoc, hlam, one_mul]
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      ring

lemma spectral_ae_eq_eigenvalue (D : HilbertOperatorData.{u}) (x : D.H)
    (lam : Circle) (hx : D.U x = (lam : ℂ) • x)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ) :
    ∀ᵐ z ∂μ.μ, z = lam := by
  letI : MeasurableSpace Circle := circleMeasurableSpace
  letI : BorelSpace Circle := circleBorelSpace
  letI : OpensMeasurableSpace Circle := circleOpensMeasurableSpace
  letI : MeasurableSpace (Submonoid.unitSphere ℂ) := circleMeasurableSpace
  letI : OpensMeasurableSpace (Submonoid.unitSphere ℂ) := ⟨le_rfl⟩
  letI : MeasureTheory.IsFiniteMeasure μ.μ := μ.isFinite
  have hcont : Continuous
      (fun z : Circle => ‖(z : ℂ) - (lam : ℂ)‖ ^ 2) := by
    fun_prop
  have hint : MeasureTheory.Integrable
      (fun z : Circle => ‖(z : ℂ) - (lam : ℂ)‖ ^ 2) μ.μ := by
    apply MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable 4
    filter_upwards with z
    have hle : ‖(z : ℂ) - (lam : ℂ)‖ ≤ 2 := by
      calc
        ‖(z : ℂ) - (lam : ℂ)‖ ≤ ‖(z : ℂ)‖ + ‖(lam : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg ((z : ℂ) - (lam : ℂ))]
  have hzero :
      (fun z : Circle => ‖(z : ℂ) - (lam : ℂ)‖ ^ 2) =ᵐ[μ.μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun _ => sq_nonneg _) hint).mp
        (spectral_variance_integral_zero D x lam hx μ hμ)
  filter_upwards [hzero] with z hz
  apply Circle.ext
  have hnorm : ‖(z : ℂ) - (lam : ℂ)‖ = 0 :=
    sq_eq_zero_iff.mp hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem eigenvector_spectral_measure_point_mass (D : HilbertOperatorData.{u}) :
    EigenvectorSpectralMeasurePointMassStatement D := by
  intro _hunitary x lam _hxne hx μ hμ
  letI : MeasureTheory.IsFiniteMeasure μ.μ := μ.isFinite
  have hae := spectral_ae_eq_eigenvalue D x lam hx μ hμ
  have hmeasure := measure_eq_mass_smul_dirac_of_ae_eq μ.μ lam hae
  have hmass : μ.μ Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
    apply (ENNReal.toReal_eq_toReal (by finiteness) (by simp)).mp
    simpa [MeasureTheory.Measure.real] using spectral_mass D x μ hμ
  rw [hmeasure, hmass]

end SpectralPointMass
end Chapter02
