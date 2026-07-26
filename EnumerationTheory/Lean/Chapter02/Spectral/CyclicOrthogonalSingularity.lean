import Chapter02.Spectral.CircleFourierUniqueness
import Chapter02.Spectral.CyclicMeasureType

open Classical Filter Set MeasureTheory

noncomputable section

namespace Chapter02.CyclicOrthogonalSingularity

noncomputable def coordinateEquiv (μ : CircleMeasureData) :
    Lp ℂ 2 μ.μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ.μ :=
  LinearIsometryEquiv.ofSurjective (CyclicSpectralModel.coordinateIsometry μ)
    (CyclicSpectralModel.coordinateLinear_surjective μ)

@[simp] theorem coordinateEquiv_apply (μ : CircleMeasureData) (F : Lp ℂ 2 μ.μ) :
    coordinateEquiv μ F = CyclicSpectralModel.coordinateLinear μ F := rfl

theorem coordinateEquiv_symm_coe (μ : CircleMeasureData) (F : Lp ℂ 2 μ.μ) :
    (fun z ↦ (coordinateEquiv μ).symm F z) =ᵐ[μ.μ]
      fun z ↦ (z : ℂ)⁻¹ * F z := by
  let G := (coordinateEquiv μ).symm F
  have hmap : CyclicSpectralModel.coordinateLinear μ G = F := by
    change coordinateEquiv μ G = F
    exact (coordinateEquiv μ).apply_symm_apply F
  have hmapPoint : ∀ᵐ z ∂μ.μ,
      CyclicSpectralModel.coordinateLinear μ G z = F z :=
    Filter.Eventually.of_forall fun z ↦ congrFun
      (congrArg (fun H : Lp ℂ 2 μ.μ ↦ (fun w ↦ H w)) hmap) z
  filter_upwards [CyclicSpectralModel.coordinateLp_coe μ G,
    hmapPoint] with z hz hEq
  change G z = (z : ℂ)⁻¹ * F z
  change CyclicSpectralModel.coordinateLp μ G z = F z at hEq
  have hcoord : (z : ℂ) * G z = F z := hz.symm.trans hEq
  rw [← hcoord]
  field_simp

theorem coordinateEquiv_zpow_coe (μ : CircleMeasureData)
    (F : Lp ℂ 2 μ.μ) (j : ℤ) :
    (fun z ↦ ((coordinateEquiv μ) ^ j) F z) =ᵐ[μ.μ]
      fun z ↦ (z : ℂ) ^ j * F z := by
  induction j using Int.induction_on with
  | zero => simp
  | @succ j hj =>
      have hcoord := CyclicSpectralModel.coordinateLp_coe μ
        (((coordinateEquiv μ) ^ (j : ℤ)) F)
      filter_upwards [hcoord, hj] with z hz hjz
      rw [zpow_add_one₀ (Circle.coe_ne_zero z)]
      change ((coordinateEquiv μ) ^ ((j : ℤ) + 1)) F z = _
      rw [show (j : ℤ) + 1 = 1 + (j : ℤ) by ring, zpow_add]
      change coordinateEquiv μ (((coordinateEquiv μ) ^ (j : ℤ)) F) z = _
      rw [coordinateEquiv_apply]
      change CyclicSpectralModel.coordinateLinear μ
        (((coordinateEquiv μ) ^ (j : ℤ)) F) z = _ at hz
      rw [hz, hjz]
      ring
  | @pred j hj =>
      have hinv := coordinateEquiv_symm_coe μ
        (((coordinateEquiv μ) ^ (-(j : ℤ))) F)
      filter_upwards [hinv, hj] with z hz hjz
      rw [zpow_sub_one₀ (Circle.coe_ne_zero z)]
      change ((coordinateEquiv μ) ^ (-(j : ℤ) - 1)) F z = _
      rw [show -(j : ℤ) - 1 = (-1 : ℤ) + -(j : ℤ) by ring, zpow_add]
      change (coordinateEquiv μ).symm
        (((coordinateEquiv μ) ^ (-(j : ℤ))) F) z = _
      rw [hz, hjz]
      ring

theorem cyclicCLM_coordinateEquiv_zpow (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (a : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD a j)
    (F : Lp ℂ 2 μ.μ) (j : ℤ) :
    CyclicSpectralModel.cyclicCLM D hD a μ (((coordinateEquiv μ) ^ j) F) =
      ((SpectralMeasure.unitaryEquiv D hD) ^ j)
        (CyclicSpectralModel.cyclicCLM D hD a μ F) := by
  induction j using Int.induction_on with
  | zero => simp
  | @succ j hj =>
      rw [show (j : ℤ) + 1 = 1 + (j : ℤ) by ring, zpow_add, zpow_add]
      change CyclicSpectralModel.cyclicCLM D hD a μ
          (coordinateEquiv μ (((coordinateEquiv μ) ^ (j : ℤ)) F)) =
        D.U (((SpectralMeasure.unitaryEquiv D hD) ^ (j : ℤ))
          (CyclicSpectralModel.cyclicCLM D hD a μ F))
      rw [coordinateEquiv_apply,
        CyclicSpectralModel.cyclicCLM_intertwines D hD a μ hμ, hj]
  | @pred j hj =>
      rw [show -(j : ℤ) - 1 = (-1 : ℤ) + -(j : ℤ) by ring,
        zpow_add, zpow_add]
      let A := ((coordinateEquiv μ) ^ (-(j : ℤ))) F
      apply (SpectralMeasure.unitaryEquiv D hD).injective
      change D.U (CyclicSpectralModel.cyclicCLM D hD a μ
          ((coordinateEquiv μ).symm A)) =
        D.U ((SpectralMeasure.unitaryEquiv D hD).symm
          (((SpectralMeasure.unitaryEquiv D hD) ^ (-(j : ℤ)))
            (CyclicSpectralModel.cyclicCLM D hD a μ F)))
      rw [← CyclicSpectralModel.cyclicCLM_intertwines D hD a μ hμ]
      change CyclicSpectralModel.cyclicCLM D hD a μ
          (coordinateEquiv μ ((coordinateEquiv μ).symm A)) = _
      rw [(coordinateEquiv μ).apply_symm_apply]
      dsimp [A]
      rw [hj]
      exact ((SpectralMeasure.unitaryEquiv D hD).apply_symm_apply _).symm

theorem integral_zpow_cross_eq_inner (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (a : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD a j)
    (F G : Lp ℂ 2 μ.μ) (n : ℤ) :
    (∫ z, (z : ℂ) ^ n * (star (F z) * G z) ∂μ.μ) =
      @inner ℂ D.H _
        (((SpectralMeasure.unitaryEquiv D hD) ^ (-n))
          (CyclicSpectralModel.cyclicCLM D hD a μ F))
        (CyclicSpectralModel.cyclicCLM D hD a μ G) := by
  calc
    (∫ z, (z : ℂ) ^ n * (star (F z) * G z) ∂μ.μ) =
        ∫ z, @inner ℂ ℂ _ ((((coordinateEquiv μ) ^ (-n)) F) z) (G z)
          ∂μ.μ := by
      apply integral_congr_ae
      filter_upwards [coordinateEquiv_zpow_coe μ F (-n)] with z hz
      rw [RCLike.inner_apply, hz]
      have hstar : (starRingEnd ℂ) ((z : ℂ) ^ (-n)) = (z : ℂ) ^ n := by
        rw [map_zpow₀]
        have hzstar : (starRingEnd ℂ) (z : ℂ) = (z : ℂ)⁻¹ := by
          apply Complex.ext <;> simp [Complex.inv_def]
        rw [hzstar, inv_zpow]
        simp
      rw [map_mul, hstar]
      simp only [Complex.star_def]
      ring
    _ = @inner ℂ (Lp ℂ 2 μ.μ) _ (((coordinateEquiv μ) ^ (-n)) F) G := by
      rw [L2.inner_def]
    _ = @inner ℂ D.H _
        (CyclicSpectralModel.cyclicCLM D hD a μ
          (((coordinateEquiv μ) ^ (-n)) F))
        (CyclicSpectralModel.cyclicCLM D hD a μ G) :=
      (CyclicSpectralModel.cyclicIsometry D hD a μ hμ).inner_map_map _ _ |>.symm
    _ = _ := by rw [cyclicCLM_coordinateEquiv_zpow D hD a μ hμ]

/-- Vanishing of all Laurent moments of the cross-density forces the two
`L²` coordinates to be pointwise orthogonal almost everywhere. -/
theorem crossDensity_ae_zero_of_laurent_moments (μ : CircleMeasureData)
    (F G : Lp ℂ 2 μ.μ)
    (hmom : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z * (star (F z) * G z) ∂μ.μ = 0) :
    (fun z ↦ star (F z) * G z) =ᵐ[μ.μ] 0 := by
  have hint : Integrable (fun z ↦ star (F z) * G z) μ.μ :=
    ((Lp.memLp F).congr_norm (Lp.memLp F).1.star
      (Filter.Eventually.of_forall fun z ↦ (norm_star (F z)).symm)).integrable_mul
      (Lp.memLp G)
  exact CircleFourierUniqueness.complex_ae_zero_of_laurent_moments μ hint hmom

/-- If two `L²` coordinates have zero cross-density almost everywhere, their
vector-density spectral measures are mutually singular. -/
theorem vectorDensityMeasure_mutuallySingular_of_crossDensity_ae_zero
    {μ : CircleMeasureData} (F G : Lp ℂ 2 μ.μ)
    (hcross : (fun z ↦ star (F z) * G z) =ᵐ[μ.μ] 0) :
    Measure.MutuallySingular
      (CyclicMeasureType.vectorDensityMeasure F).μ
      (CyclicMeasureType.vectorDensityMeasure G).μ := by
  let E : Set Circle := {z | star (F z) * G z ≠ 0}
  have hE : μ.μ E = 0 := by
    exact measure_eq_zero_iff_ae_notMem.mpr (by
      filter_upwards [hcross] with z hz
      change ¬ star (F z) * G z ≠ 0
      exact fun hne ↦ hne hz)
  let s : Set Circle := {z | F z = 0} ∪ E
  let t : Set Circle := {z | G z = 0}
  refine Measure.MutuallySingular.mk (s := s) (t := t) ?_ ?_ ?_
  · apply (withDensity_apply_eq_zero'
      (CyclicMeasureType.spectralDensity_aemeasurable F)).2
    apply measure_mono_null (t := E)
    · intro z hz
      rcases hz.2 with hzF | hzE
      · exfalso
        apply hz.1
        simp [CyclicMeasureType.spectralDensity, show F z = 0 from hzF]
      · exact hzE
    · exact hE
  · apply (withDensity_apply_eq_zero'
      (CyclicMeasureType.spectralDensity_aemeasurable G)).2
    have hempty : {z | CyclicMeasureType.spectralDensity G z ≠ 0} ∩ t = ∅ := by
      ext z
      simp [t, CyclicMeasureType.spectralDensity]
    rw [hempty, measure_empty]
  · intro z hz
    by_cases hzE : z ∈ E
    · exact Or.inl (Or.inr hzE)
    · have hzero : star (F z) * G z = 0 := not_ne_iff.mp hzE
      rcases mul_eq_zero.mp hzero with hF | hG
      · left
        left
        exact star_eq_zero.mp hF
      · right
        exact hG

theorem vectorDensityMeasure_mutuallySingular_of_laurent_moments
    {μ : CircleMeasureData} (F G : Lp ℂ 2 μ.μ)
    (hmom : ∀ q : C(Circle, ℂ), q ∈ CircleLaurent.span →
      ∫ z, q z * (star (F z) * G z) ∂μ.μ = 0) :
    Measure.MutuallySingular
      (CyclicMeasureType.vectorDensityMeasure F).μ
      (CyclicMeasureType.vectorDensityMeasure G).μ :=
  vectorDensityMeasure_mutuallySingular_of_crossDensity_ae_zero F G
    (crossDensity_ae_zero_of_laurent_moments μ F G hmom)

/-- Inside one cyclic spectral model, orthogonality of the generated cyclic
subspaces forces the two coordinates to have zero cross-density almost
everywhere. -/
theorem crossDensity_ae_zero_of_orthogonal_images
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (a : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD a j)
    (F G : Lp ℂ 2 μ.μ)
    (horth : OrthogonalCyclicSubspaces D
      (CyclicSpectralModel.cyclicCLM D hD a μ F)
      (CyclicSpectralModel.cyclicCLM D hD a μ G)) :
    (fun z ↦ star (F z) * G z) =ᵐ[μ.μ] 0 := by
  let p := CyclicSpectralModel.cyclicCLM D hD a μ F
  let q := CyclicSpectralModel.cyclicCLM D hD a μ G
  have hinner (j : ℤ) :
      @inner ℂ (Lp ℂ 2 μ.μ) _ (((coordinateEquiv μ) ^ j) F) G = 0 := by
    have hpcyc : InCyclicSubspace D p
        (CyclicSpectralModel.cyclicCLM D hD a μ
          (((coordinateEquiv μ) ^ j) F)) := by
      intro K hK hpK
      rw [cyclicCLM_coordinateEquiv_zpow D hD a μ hμ]
      exact CyclicSpectralModel.zpow_orbit_mem_reducing D hD p K hK hpK j
    have hqcyc : InCyclicSubspace D q q := fun K hK hqK ↦ hqK
    have himage := horth _ _ hpcyc hqcyc
    have hisom := (CyclicSpectralModel.cyclicIsometry D hD a μ hμ).inner_map_map
      (((coordinateEquiv μ) ^ j) F) G
    exact hisom.symm.trans himage
  have hchar (n : ℤ) :
      ∫ z, (z : ℂ) ^ n * (star (F z) * G z) ∂μ.μ = 0 := by
    have hi := hinner (-n)
    rw [L2.inner_def] at hi
    calc
      (∫ z, (z : ℂ) ^ n * (star (F z) * G z) ∂μ.μ) =
          ∫ z, @inner ℂ ℂ _ ((((coordinateEquiv μ) ^ (-n)) F) z) (G z)
            ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards [coordinateEquiv_zpow_coe μ F (-n)] with z hz
        rw [RCLike.inner_apply, hz]
        have hstar : (starRingEnd ℂ) ((z : ℂ) ^ (-n)) = (z : ℂ) ^ n := by
          rw [map_zpow₀]
          have hzstar : (starRingEnd ℂ) (z : ℂ) = (z : ℂ)⁻¹ := by
            apply Complex.ext <;> simp [Complex.inv_def]
          rw [hzstar, inv_zpow]
          simp
        rw [map_mul, hstar]
        simp only [Complex.star_def]
        ring
      _ = 0 := hi
  have hcrossInt : Integrable (fun z ↦ star (F z) * G z) μ.μ :=
    ((Lp.memLp F).congr_norm (Lp.memLp F).1.star
      (Filter.Eventually.of_forall fun z ↦ (norm_star (F z)).symm)).integrable_mul
      (Lp.memLp G)
  have hmom : ∀ r : C(Circle, ℂ), r ∈ CircleLaurent.span →
      ∫ z, r z * (star (F z) * G z) ∂μ.μ = 0 := by
    intro r hr
    refine Submodule.span_induction (p := fun r _ ↦
      ∫ z, r z * (star (F z) * G z) ∂μ.μ = 0) ?_ ?_ ?_ ?_ hr
    · rintro r ⟨n, rfl⟩
      exact hchar n
    · simp
    · intro r s hr hs hir his
      have hirInt : Integrable (fun z ↦ r z * (star (F z) * G z)) μ.μ :=
        hcrossInt.bdd_mul r.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z ↦ r.norm_coe_le_norm z)
      have hisInt : Integrable (fun z ↦ s z * (star (F z) * G z)) μ.μ :=
        hcrossInt.bdd_mul s.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z ↦ s.norm_coe_le_norm z)
      simp only [ContinuousMap.add_apply, add_mul]
      rw [integral_add hirInt hisInt, hir, his, add_zero]
    · intro c r hr hir
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, hir, mul_zero]
  exact crossDensity_ae_zero_of_laurent_moments μ F G hmom

/-- Inside one cyclic spectral model, two coordinates which generate
orthogonal cyclic subspaces necessarily have mutually singular spectral
density measures. -/
theorem vectorDensityMeasure_mutuallySingular_of_orthogonal_images
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (a : D.H) (μ : CircleMeasureData)
    (hμ : ∀ j : ℤ, circleFourierCoefficient μ j =
      SpectralMeasure.vectorCorrelation D hD a j)
    (F G : Lp ℂ 2 μ.μ)
    (horth : OrthogonalCyclicSubspaces D
      (CyclicSpectralModel.cyclicCLM D hD a μ F)
      (CyclicSpectralModel.cyclicCLM D hD a μ G)) :
    Measure.MutuallySingular
      (CyclicMeasureType.vectorDensityMeasure F).μ
      (CyclicMeasureType.vectorDensityMeasure G).μ := by
  exact vectorDensityMeasure_mutuallySingular_of_crossDensity_ae_zero F G
    (crossDensity_ae_zero_of_orthogonal_images D hD a μ hμ F G horth)

end Chapter02.CyclicOrthogonalSingularity
