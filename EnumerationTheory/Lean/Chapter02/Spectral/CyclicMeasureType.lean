import Chapter02.Spectral.CyclicSpectralModel

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.CyclicMeasureType

def spectralDensity {μ : CircleMeasureData} (F : Lp ℂ 2 μ.μ) (z : Circle) : ℝ≥0∞ :=
  ENNReal.ofReal (‖F z‖ ^ 2)

theorem spectralDensity_aemeasurable {μ : CircleMeasureData} (F : Lp ℂ 2 μ.μ) :
    AEMeasurable (spectralDensity F) μ.μ := by
  exact ((Lp.memLp F).1.norm.pow 2).aemeasurable.ennreal_ofReal

theorem spectralDensity_lintegral_lt_top {μ : CircleMeasureData} (F : Lp ℂ 2 μ.μ) :
    ∫⁻ z, spectralDensity F z ∂μ.μ < ∞ := by
  have hnorm : MemLp (fun z => ‖F z‖) 2 μ.μ := (Lp.memLp F).norm
  have hint : Integrable (fun z => ‖F z‖ * ‖F z‖) μ.μ :=
    hnorm.integrable_mul hnorm
  have hfin := (hasFiniteIntegral_def _ μ.μ).mp hint.hasFiniteIntegral
  convert hfin using 1
  apply lintegral_congr
  intro z
  rw [spectralDensity, Real.enorm_eq_ofReal]
  simp [pow_two]
  positivity

noncomputable def vectorDensityMeasure {μ : CircleMeasureData} (F : Lp ℂ 2 μ.μ) :
    CircleMeasureData where
  μ := μ.μ.withDensity (spectralDensity F)
  isFinite := isFiniteMeasure_withDensity (spectralDensity_lintegral_lt_top F).ne

theorem vectorDensityMeasure_absolutelyContinuous {μ : CircleMeasureData}
    (F : Lp ℂ 2 μ.μ) :
    (vectorDensityMeasure F).μ ≪ μ.μ := by
  exact withDensity_absolutelyContinuous μ.μ _

theorem coordinateLinear_iterate_coe {μ : CircleMeasureData}
    (F : Lp ℂ 2 μ.μ) (n : ℕ) :
    (fun z => ((CyclicSpectralModel.coordinateLinear μ)^[n]) F z) =ᵐ[μ.μ]
      fun z => (z : ℂ) ^ n * F z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      filter_upwards [CyclicSpectralModel.coordinateLp_coe μ
        (((CyclicSpectralModel.coordinateLinear μ)^[n]) F), ih] with z hcoord hn
      change CyclicSpectralModel.coordinateLp μ
        (((CyclicSpectralModel.coordinateLinear μ)^[n]) F) z = _
      rw [hcoord, hn]
      rw [pow_succ']
      ring

theorem cyclicCLM_iterate (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (F : Lp ℂ 2 μ.μ) (n : ℕ) :
    (D.U^[n]) (CyclicSpectralModel.cyclicCLM D hD x μ F) =
      CyclicSpectralModel.cyclicCLM D hD x μ
        (((CyclicSpectralModel.coordinateLinear μ)^[n]) F) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ih]
      rw [CyclicSpectralModel.cyclicCLM_intertwines D hD x μ hμ]

theorem vectorDensityMeasure_moment (D : HilbertOperatorData) (hD : IsUnitary D)
    (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD x j)
    (F : Lp ℂ 2 μ.μ) (n : ℕ) :
    circleFourierCoefficient (vectorDensityMeasure F) n =
      @inner ℂ D.H _ (CyclicSpectralModel.cyclicCLM D hD x μ F)
        ((D.U^[n]) (CyclicSpectralModel.cyclicCLM D hD x μ F)) := by
  rw [cyclicCLM_iterate D hD x μ hμ F n]
  change circleFourierCoefficient (vectorDensityMeasure F) n =
    @inner ℂ D.H _
      (CyclicSpectralModel.cyclicIsometry D hD x μ hμ F)
      (CyclicSpectralModel.cyclicIsometry D hD x μ hμ
        (((CyclicSpectralModel.coordinateLinear μ)^[n]) F))
  rw [(CyclicSpectralModel.cyclicIsometry D hD x μ hμ).inner_map_map]
  rw [L2.inner_def]
  rw [circleFourierCoefficient]
  change (∫ z : Circle, (z : ℂ) ^ (n : ℤ)
      ∂μ.μ.withDensity (spectralDensity F)) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (spectralDensity_aemeasurable F) (by simp [spectralDensity])]
  apply integral_congr_ae
  filter_upwards [coordinateLinear_iterate_coe F n] with z hn
  rw [hn, RCLike.inner_apply]
  simp only [spectralDensity, ENNReal.toReal_ofReal (sq_nonneg _), zpow_natCast,
    Complex.real_smul]
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  ring

theorem cyclicSubspaceProperties (D : HilbertOperatorData) :
    CyclicSubspaceSpectralProperties D := by
  intro hD x y hxy
  obtain ⟨μx, hμx, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  obtain ⟨F, hF⟩ :=
    (CyclicSpectralModel.inCyclicSubspace_iff_range D hD x y μx hμx).mp hxy
  let μy : CircleMeasureData := vectorDensityMeasure F
  refine ⟨μx, μy, ?_, ?_, ?_⟩
  · intro n
    rw [hμx (n : ℤ)]
    exact congrArg (fun z : D.H => @inner ℂ D.H _ x z)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  · intro n
    change circleFourierCoefficient (vectorDensityMeasure F) n = _
    have hm := vectorDensityMeasure_moment D hD x μx hμx F n
    rw [hF] at hm
    exact hm
  · exact vectorDensityMeasure_absolutelyContinuous F

end Chapter02.CyclicMeasureType
