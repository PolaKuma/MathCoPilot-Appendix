import Chapter02.Spectral.FiniteSpectralRank

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.RadonNikodymTransfer

def transferRaw (μ ν : CircleMeasureData) (F : Lp ℂ 2 ν.μ) (z : Circle) : ℂ :=
  (Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) * F z

theorem transferRaw_memLp (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (F : Lp ℂ 2 ν.μ) : MemLp (transferRaw μ ν F) 2 μ.μ := by
  let d : Circle → ℝ := fun z ↦ (ν.μ.rnDeriv μ.μ z).toReal
  have hdmeas : Measurable d :=
    (Measure.measurable_rnDeriv ν.μ μ.μ).ennreal_toReal
  have ht : ∀ᵐ z ∂μ.μ, ν.μ.rnDeriv μ.μ z < ⊤ :=
    (Measure.rnDeriv_ne_top ν.μ μ.μ).mono fun _ h ↦ lt_top_iff_ne_top.mpr h
  have hbase : Integrable (fun z ↦ ‖F z‖ ^ 2) ν.μ :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.stronglyMeasurable F).aestronglyMeasurable).mp
      (Lp.memLp F)
  have hbase' : Integrable (fun z ↦ ‖F z‖ ^ 2)
      (μ.μ.withDensity (ν.μ.rnDeriv μ.μ)) := by
    rw [Measure.withDensity_rnDeriv_eq ν.μ μ.μ hνμ]
    exact hbase
  have hweighted : Integrable (fun z ↦ ‖F z‖ ^ 2 * d z) μ.μ :=
    (integrable_withDensity_iff (Measure.measurable_rnDeriv ν.μ μ.μ) ht).mp hbase'
  have hmeas : AEStronglyMeasurable (transferRaw μ ν F) μ.μ := by
    exact ((Complex.continuous_ofReal.measurable.comp hdmeas.sqrt).mul
      (Lp.stronglyMeasurable F).measurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  apply hweighted.congr
  filter_upwards [Measure.rnDeriv_ne_top ν.μ μ.μ] with z hz
  change ‖F z‖ ^ 2 * (ν.μ.rnDeriv μ.μ z).toReal =
    ‖(Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) * F z‖ ^ 2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt ENNReal.toReal_nonneg]
  ring

def transfer (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (F : Lp ℂ 2 ν.μ) : Lp ℂ 2 μ.μ :=
  (transferRaw_memLp μ ν hνμ F).toLp (transferRaw μ ν F)

theorem transfer_coe (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (F : Lp ℂ 2 ν.μ) :
    (fun z ↦ transfer μ ν hνμ F z) =ᵐ[μ.μ] transferRaw μ ν F :=
  (transferRaw_memLp μ ν hνμ F).coeFn_toLp

theorem integral_transfer_cross (μ ν : CircleMeasureData)
    (hνμ : ν.μ ≪ μ.μ) (q : Circle → ℂ) (F G : Lp ℂ 2 ν.μ) :
    ∫ z, q z * (star (transfer μ ν hνμ F z) * transfer μ ν hνμ G z) ∂μ.μ =
      ∫ z, q z * (star (F z) * G z) ∂ν.μ := by
  let r : Circle → ℂ := fun z ↦ q z * (star (F z) * G z)
  let d : Circle → ℝ := fun z ↦ (ν.μ.rnDeriv μ.μ z).toReal
  have hpoint : (fun z ↦ q z *
      (star (transfer μ ν hνμ F z) * transfer μ ν hνμ G z)) =ᵐ[μ.μ]
      fun z ↦ d z • r z := by
    filter_upwards [transfer_coe μ ν hνμ F, transfer_coe μ ν hνμ G,
      Measure.rnDeriv_ne_top ν.μ μ.μ] with z hF hG htop
    rw [hF, hG]
    simp only [transferRaw, Complex.star_def, map_mul]
    have hs : Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) ^ 2 =
        (ν.μ.rnDeriv μ.μ z).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
    rw [show (starRingEnd ℂ)
        (Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) =
        (Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) by simp]
    have hsc : ((Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) ^ 2) =
        ((ν.μ.rnDeriv μ.μ z).toReal : ℂ) := by exact_mod_cast hs
    simp only [r, d, Complex.real_smul]
    calc
      _ = ((Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) ^ 2) *
          (q z * ((starRingEnd ℂ) (F z) * G z)) := by ring
      _ = ((ν.μ.rnDeriv μ.μ z).toReal : ℂ) *
          (q z * ((starRingEnd ℂ) (F z) * G z)) := by rw [hsc]
  calc
    (∫ z, q z * (star (transfer μ ν hνμ F z) *
        transfer μ ν hνμ G z) ∂μ.μ) = ∫ z, d z • r z ∂μ.μ :=
      integral_congr_ae hpoint
    _ = ∫ z, r z ∂μ.μ.withDensity (ν.μ.rnDeriv μ.μ) :=
      (integral_withDensity_eq_integral_toReal_smul₀
        (Measure.measurable_rnDeriv ν.μ μ.μ).aemeasurable
        ((Measure.rnDeriv_ne_top ν.μ μ.μ).mono
          fun _ h ↦ lt_top_iff_ne_top.mpr h) r).symm
    _ = ∫ z, r z ∂ν.μ := by rw [Measure.withDensity_rnDeriv_eq ν.μ μ.μ hνμ]
    _ = ∫ z, q z * (star (F z) * G z) ∂ν.μ := rfl

theorem vectorDensityMeasure_fourier_eq_cross (μ : CircleMeasureData)
    (F : Lp ℂ 2 μ.μ) (n : ℕ) :
    circleFourierCoefficient (CyclicMeasureType.vectorDensityMeasure F) n =
      ∫ z, (z : ℂ) ^ n * (star (F z) * F z) ∂μ.μ := by
  rw [circleFourierCoefficient]
  change (∫ z : Circle, (z : ℂ) ^ (n : ℤ)
      ∂μ.μ.withDensity (CyclicMeasureType.spectralDensity F)) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (CyclicMeasureType.spectralDensity_aemeasurable F)
    (by simp [CyclicMeasureType.spectralDensity])]
  apply integral_congr_ae
  filter_upwards with z
  simp only [CyclicMeasureType.spectralDensity,
    ENNReal.toReal_ofReal (sq_nonneg _), zpow_natCast, Complex.real_smul]
  rw [show star (F z) * F z = F z * star (F z) by ring,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ring

/-- RN transfer preserves the vector-density spectral measure. -/
theorem vectorDensityMeasure_transfer (μ ν : CircleMeasureData)
    (hνμ : ν.μ ≪ μ.μ) (F : Lp ℂ 2 ν.μ) :
    CyclicMeasureType.vectorDensityMeasure (transfer μ ν hνμ F) =
      CyclicMeasureType.vectorDensityMeasure F := by
  apply SpectralMeasure.eq_of_nat_moments
  intro n
  rw [vectorDensityMeasure_fourier_eq_cross μ,
    vectorDensityMeasure_fourier_eq_cross ν]
  exact integral_transfer_cross μ ν hνμ (fun z ↦ (z : ℂ) ^ n) F F

theorem ae_imp_of_ae_rnDeriv_ne_zero (μ ν : CircleMeasureData)
    (hνμ : ν.μ ≪ μ.μ) {p : Circle → Prop} (hp : ∀ᵐ z ∂ν.μ, p z) :
    ∀ᵐ z ∂μ.μ, ν.μ.rnDeriv μ.μ z ≠ 0 → p z := by
  have ht := hp
  rw [← Measure.withDensity_rnDeriv_eq ν.μ μ.μ hνμ] at ht
  exact (ae_withDensity_iff (Measure.measurable_rnDeriv ν.μ μ.μ)).1 ht

theorem transfer_add (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (F G : Lp ℂ 2 ν.μ) :
    transfer μ ν hνμ (F + G) = transfer μ ν hνμ F + transfer μ ν hνμ G := by
  apply Lp.ext
  have hFG := ae_imp_of_ae_rnDeriv_ne_zero μ ν hνμ (Lp.coeFn_add F G)
  filter_upwards [transfer_coe μ ν hνμ (F + G),
    transfer_coe μ ν hνμ F, transfer_coe μ ν hνμ G,
    Lp.coeFn_add (transfer μ ν hνμ F) (transfer μ ν hνμ G), hFG]
      with z hsum hF hG houtAdd hFG
  rw [hsum, houtAdd]
  change transferRaw μ ν (F + G) z =
    transfer μ ν hνμ F z + transfer μ ν hνμ G z
  rw [hF, hG]
  by_cases hd : ν.μ.rnDeriv μ.μ z = 0
  · simp [transferRaw, hd]
  · unfold transferRaw
    rw [hFG hd]
    simp only [Pi.add_apply, mul_add]

theorem transfer_smul (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (c : ℂ) (F : Lp ℂ 2 ν.μ) :
    transfer μ ν hνμ (c • F) = c • transfer μ ν hνμ F := by
  apply Lp.ext
  have hcF' := ae_imp_of_ae_rnDeriv_ne_zero μ ν hνμ (Lp.coeFn_smul c F)
  filter_upwards [transfer_coe μ ν hνμ (c • F),
    transfer_coe μ ν hνμ F, Lp.coeFn_smul c (transfer μ ν hνμ F), hcF']
      with z hcF hF houtSmul hsmul
  rw [hcF, houtSmul]
  change transferRaw μ ν (c • F) z = c * transfer μ ν hνμ F z
  rw [hF]
  by_cases hd : ν.μ.rnDeriv μ.μ z = 0
  · simp [transferRaw, hd]
  · unfold transferRaw
    rw [hsmul hd]
    change (Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) *
      (c * F z) = c *
        ((Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) * F z)
    ring

theorem transfer_inner (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (F G : Lp ℂ 2 ν.μ) :
    @inner ℂ (Lp ℂ 2 μ.μ) _ (transfer μ ν hνμ F) (transfer μ ν hνμ G) =
      @inner ℂ (Lp ℂ 2 ν.μ) _ F G := by
  rw [L2.inner_def, L2.inner_def]
  have h := integral_transfer_cross μ ν hνμ (fun _ ↦ 1) F G
  simpa [mul_comm] using h

theorem transfer_norm (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (F : Lp ℂ 2 ν.μ) : ‖transfer μ ν hνμ F‖ = ‖F‖ := by
  have hsq : ‖transfer μ ν hνμ F‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), transfer_inner]
  nlinarith [norm_nonneg (transfer μ ν hνμ F), norm_nonneg F]

def transferLinearIsometry (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ) :
    Lp ℂ 2 ν.μ →ₗᵢ[ℂ] Lp ℂ 2 μ.μ where
  toFun := transfer μ ν hνμ
  map_add' := transfer_add μ ν hνμ
  map_smul' := transfer_smul μ ν hνμ
  norm_map' := transfer_norm μ ν hνμ

theorem transfer_coordinate (μ ν : CircleMeasureData) (hνμ : ν.μ ≪ μ.μ)
    (F : Lp ℂ 2 ν.μ) :
    transfer μ ν hνμ (CyclicSpectralModel.coordinateLinear ν F) =
      CyclicSpectralModel.coordinateLinear μ (transfer μ ν hνμ F) := by
  apply Lp.ext
  have hcoordF' := ae_imp_of_ae_rnDeriv_ne_zero μ ν hνμ
    (CyclicSpectralModel.coordinateLp_coe ν F)
  filter_upwards [transfer_coe μ ν hνμ
      (CyclicSpectralModel.coordinateLinear ν F),
    transfer_coe μ ν hνμ F,
    hcoordF',
    CyclicSpectralModel.coordinateLp_coe μ (transfer μ ν hνμ F)]
      with z hleft hF hcoordF hcoordT
  rw [hleft]
  change transferRaw μ ν (CyclicSpectralModel.coordinateLp ν F) z =
    CyclicSpectralModel.coordinateLp μ (transfer μ ν hνμ F) z
  rw [hcoordT]
  rw [hF]
  by_cases hd : ν.μ.rnDeriv μ.μ z = 0
  · simp [transferRaw, hd]
  · unfold transferRaw
    rw [hcoordF hd]
    ring

theorem transfer_reverse (μ ν : CircleMeasureData)
    (hνμ : ν.μ ≪ μ.μ) (hμν : μ.μ ≪ ν.μ) (F : Lp ℂ 2 μ.μ) :
    transfer μ ν hνμ (transfer ν μ hμν F) = F := by
  apply Lp.ext
  have hinnerCoeν := transfer_coe ν μ hμν F
  have hinnerCoe : (fun z ↦ transfer ν μ hμν F z) =ᵐ[μ.μ]
      transferRaw ν μ F := hμν.ae_le hinnerCoeν
  have hprod := Measure.rnDeriv_mul_rnDeriv hμν
    (κ := μ.μ)
  filter_upwards [transfer_coe μ ν hνμ (transfer ν μ hμν F),
    hinnerCoe, hprod, hμν.ae_le (Measure.rnDeriv_ne_top μ.μ ν.μ),
    Measure.rnDeriv_ne_top ν.μ μ.μ, Measure.rnDeriv_self μ.μ]
      with z hout hin hprod htop1 htop2 hself
  rw [hout]
  unfold transferRaw
  rw [hin]
  unfold transferRaw
  have hrealprod : (μ.μ.rnDeriv ν.μ z).toReal *
      (ν.μ.rnDeriv μ.μ z).toReal = 1 := by
    change μ.μ.rnDeriv ν.μ z * ν.μ.rnDeriv μ.μ z =
      μ.μ.rnDeriv μ.μ z at hprod
    rw [← ENNReal.toReal_mul, hprod, hself]
    simp
  have hsquare1 : Real.sqrt ((μ.μ.rnDeriv ν.μ z).toReal) ^ 2 =
      (μ.μ.rnDeriv ν.μ z).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hsquare2 : Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) ^ 2 =
      (ν.μ.rnDeriv μ.μ z).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hsqrtprod : Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) *
      Real.sqrt ((μ.μ.rnDeriv ν.μ z).toReal) = 1 := by
    have hnonneg : 0 ≤ Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) *
        Real.sqrt ((μ.μ.rnDeriv ν.μ z).toReal) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  rw [← mul_assoc]
  have hsqrtComplex :
      (Real.sqrt ((ν.μ.rnDeriv μ.μ z).toReal) : ℂ) *
        (Real.sqrt ((μ.μ.rnDeriv ν.μ z).toReal) : ℂ) = 1 := by
    exact_mod_cast hsqrtprod
  rw [hsqrtComplex, one_mul]

def transferEquiv (μ ν : CircleMeasureData)
    (hνμ : ν.μ ≪ μ.μ) (hμν : μ.μ ≪ ν.μ) :
    Lp ℂ 2 ν.μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ.μ :=
  LinearIsometryEquiv.ofSurjective (transferLinearIsometry μ ν hνμ) (by
    intro F
    exact ⟨transfer ν μ hμν F, transfer_reverse μ ν hνμ hμν F⟩)

end Chapter02.RadonNikodymTransfer
