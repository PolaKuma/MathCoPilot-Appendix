import Chapter02.Spectral.CyclicMeasureType

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.SpectralRelations

noncomputable def addCircleMeasure (μ ν : CircleMeasureData) : CircleMeasureData where
  μ := μ.μ + ν.μ
  isFinite := inferInstance

lemma self_mem_cyclic (D : HilbertOperatorData) (x : D.H) :
    InCyclicSubspace D x x := by
  intro K hK hx
  exact hx

lemma iterate_mem_cyclic (D : HilbertOperatorData) (x : D.H) (n : ℕ) :
    InCyclicSubspace D x ((D.U^[n]) x) := by
  intro K hK hx
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hK.2.2.2 _).mp ih

lemma iterate_add (D : HilbertOperatorData) (x y : D.H) (n : ℕ) :
    (D.U^[n]) (x + y) = (D.U^[n]) x + (D.U^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

lemma orthogonal_reducing (D : HilbertOperatorData) (hD : IsUnitary D)
    (S : Submodule ℂ D.H)
    (hS : IsClosedReducingSubspace D (S : Set D.H)) :
    IsClosedReducingSubspace D (Sᗮ : Set D.H) := by
  refine ⟨(Sᗮ).zero_mem, ?_, ?_, ?_⟩
  · intro x hx y hy a b
    exact (Sᗮ).add_mem ((Sᗮ).smul_mem a hx) ((Sᗮ).smul_mem b hy)
  · intro seq hseq z hz
    exact (Submodule.isClosed_orthogonal S).isSeqClosed hseq hz
  · intro v
    change v ∈ Sᗮ ↔ D.U v ∈ Sᗮ
    rw [Submodule.mem_orthogonal, Submodule.mem_orthogonal]
    constructor
    · intro hv a ha
      obtain ⟨b, hb⟩ := hD.1 a
      have hbS : b ∈ S := (hS.2.2.2 b).2 (by simpa [hb] using ha)
      have hz := hv b hbS
      rw [← hb]
      simpa using (SpectralMeasure.unitaryEquiv D hD).inner_map_map b v |>.trans hz
    · intro hv a ha
      have hUa : D.U a ∈ S := (hS.2.2.2 a).1 ha
      have hz := hv (D.U a) hUa
      simpa using (SpectralMeasure.unitaryEquiv D hD).inner_map_map a v |>.symm.trans hz

lemma cyclic_subspaces_orthogonal_of_mem (D : HilbertOperatorData)
    (S : Submodule ℂ D.H) (p r : D.H)
    (hS : IsClosedReducingSubspace D (S : Set D.H))
    (hSorth : IsClosedReducingSubspace D (Sᗮ : Set D.H))
    (hp : p ∈ S) (hr : r ∈ Sᗮ) :
    OrthogonalCyclicSubspaces D p r := by
  intro a b ha hb
  have haS : a ∈ S := ha S hS hp
  have hbS : b ∈ Sᗮ := hb Sᗮ hSorth hr
  exact Submodule.inner_right_of_mem_orthogonal haS hbS

theorem orthogonal_sum_spectral_measure (D : HilbertOperatorData)
    (x y : D.H) (μx μy μsum : CircleMeasureData)
    (horth : OrthogonalCyclicSubspaces D x y)
    (hμx : HasSpectralMeasure D x μx)
    (hμy : HasSpectralMeasure D y μy)
    (hμsum : HasSpectralMeasure D (x + y) μsum) :
    μsum.μ = μx.μ + μy.μ := by
  let μadd := addCircleMeasure μx μy
  have hμadd : HasSpectralMeasure D (x + y) μadd := by
    intro n
    have hintx : Integrable (fun z : Circle => (z : ℂ) ^ (n : ℤ)) μx.μ :=
      Continuous.integrable_of_hasCompactSupport (by fun_prop)
        (HasCompactSupport.of_compactSpace _)
    have hinty : Integrable (fun z : Circle => (z : ℂ) ^ (n : ℤ)) μy.μ :=
      Continuous.integrable_of_hasCompactSupport (by fun_prop)
        (HasCompactSupport.of_compactSpace _)
    rw [circleFourierCoefficient]
    change (∫ z : Circle, (z : ℂ) ^ (n : ℤ) ∂(μx.μ + μy.μ)) = _
    rw [MeasureTheory.integral_add_measure hintx hinty]
    rw [← circleFourierCoefficient, ← circleFourierCoefficient, hμx n, hμy n]
    rw [iterate_add]
    rw [inner_add_left, inner_add_right, inner_add_right]
    have hxy : @inner ℂ D.H _ x ((D.U^[n]) y) = 0 :=
      horth x ((D.U^[n]) y) (self_mem_cyclic D x) (iterate_mem_cyclic D y n)
    have hyx : @inner ℂ D.H _ y ((D.U^[n]) x) = 0 :=
      by
        rw [← inner_conj_symm]
        simp [horth ((D.U^[n]) x) y (iterate_mem_cyclic D x n)
          (self_mem_cyclic D y)]
    rw [hxy, hyx]
    simp [add_comm]
  have heq : μsum = μadd := SpectralMeasure.eq_of_nat_moments μsum μadd
    (fun n => (hμsum n).trans (hμadd n).symm)
  exact congrArg CircleMeasureData.μ heq

theorem exists_cyclic_vector_with_ac_measure (D : HilbertOperatorData)
    (hD : IsUnitary D) (x : D.H) (μ ν : CircleMeasureData)
    (hμ : HasSpectralMeasure D x μ) (hνμ : ν.μ ≪ μ.μ) :
    ∃ y : D.H, InCyclicSubspace D x y ∧ HasSpectralMeasure D y ν := by
  obtain ⟨μ₀, hμ₀, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  have hμ₀spec : HasSpectralMeasure D x μ₀ := by
    intro n
    rw [hμ₀ (n : ℤ)]
    exact congrArg (fun z : D.H => @inner ℂ D.H _ x z)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  have hμeq : μ₀ = μ := SpectralMeasure.eq_of_nat_moments μ₀ μ
    (fun n => (hμ₀spec n).trans (hμ n).symm)
  subst μ₀
  let d : Circle → ℝ := fun z => (ν.μ.rnDeriv μ.μ z).toReal
  let f : Circle → ℂ := fun z => (Real.sqrt (d z) : ℂ)
  have hdmeas : Measurable d :=
    (Measure.measurable_rnDeriv ν.μ μ.μ).ennreal_toReal
  have hfmeas : AEStronglyMeasurable f μ.μ := by
    exact (Complex.continuous_ofReal.measurable.comp hdmeas.sqrt).aestronglyMeasurable
  have hdint : Integrable d μ.μ := Measure.integrable_toReal_rnDeriv
  have hsqint : Integrable (fun z => ‖f z‖ ^ 2) μ.μ := by
    apply hdint.congr
    filter_upwards [] with z
    simp [f, d, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (ENNReal.toReal_nonneg)]
  have hf : MemLp f 2 μ.μ :=
    (memLp_two_iff_integrable_sq_norm hfmeas).2 hsqint
  let F : Lp ℂ 2 μ.μ := hf.toLp f
  let y : D.H := CyclicSpectralModel.cyclicCLM D hD x μ F
  have hycyc : InCyclicSubspace D x y :=
    (CyclicSpectralModel.inCyclicSubspace_iff_range D hD x y μ hμ₀).2 ⟨F, rfl⟩
  have hdens : CyclicMeasureType.spectralDensity F =ᵐ[μ.μ] ν.μ.rnDeriv μ.μ := by
    filter_upwards [hf.coeFn_toLp, Measure.rnDeriv_ne_top ν.μ μ.μ] with z hFz htop
    rw [CyclicMeasureType.spectralDensity, hFz]
    simp only [f, d, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (ENNReal.toReal_nonneg)]
    exact ENNReal.ofReal_toReal htop
  have hmeasure : (CyclicMeasureType.vectorDensityMeasure F).μ = ν.μ := by
    change μ.μ.withDensity (CyclicMeasureType.spectralDensity F) = ν.μ
    rw [withDensity_congr_ae hdens]
    exact Measure.withDensity_rnDeriv_eq ν.μ μ.μ hνμ
  refine ⟨y, hycyc, ?_⟩
  intro n
  change (∫ z : Circle, (z : ℂ) ^ (n : ℤ) ∂ν.μ) = _
  rw [← hmeasure]
  simpa [y] using
    (CyclicMeasureType.vectorDensityMeasure_moment D hD x μ hμ₀ F n)

theorem singular_spectral_measures_orthogonal (D : HilbertOperatorData)
    (hD : IsUnitary D) (x y : D.H) (μx μy : CircleMeasureData)
    (hμx : HasSpectralMeasure D x μx) (hμy : HasSpectralMeasure D y μy)
    (hsing : Measure.MutuallySingular μx.μ μy.μ) :
    OrthogonalCyclicSubspaces D x y := by
  obtain ⟨μ₀, hμ₀, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  have hμ₀spec : HasSpectralMeasure D x μ₀ := by
    intro n
    rw [hμ₀ (n : ℤ)]
    exact congrArg (fun z : D.H => @inner ℂ D.H _ x z)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  have hμ₀eq : μ₀ = μx := SpectralMeasure.eq_of_nat_moments μ₀ μx
    (fun n => (hμ₀spec n).trans (hμx n).symm)
  let T := CyclicSpectralModel.cyclicCLM D hD x μ₀
  let S : Submodule ℂ D.H := T.range
  have hSclosed : IsClosed (S : Set D.H) := by
    change IsClosed (CyclicSpectralModel.cyclicRange D hD x μ₀)
    exact CyclicSpectralModel.cyclicRange_isClosed D hD x μ₀ hμ₀
  letI : CompleteSpace S := hSclosed.completeSpace_coe
  letI : S.HasOrthogonalProjection := inferInstance
  have hSred : IsClosedReducingSubspace D (S : Set D.H) := by
    change IsClosedReducingSubspace D (CyclicSpectralModel.cyclicRange D hD x μ₀)
    exact CyclicSpectralModel.cyclicRange_reducing D hD x μ₀ hμ₀
  have hSored : IsClosedReducingSubspace D (Sᗮ : Set D.H) :=
    orthogonal_reducing D hD S hSred
  let p : D.H := S.starProjection y
  let r : D.H := y - p
  have hpS : p ∈ S := S.starProjection_apply_mem y
  have hrS : r ∈ Sᗮ := S.sub_starProjection_mem_orthogonal y
  have hpx : InCyclicSubspace D x p := by
    rw [CyclicSpectralModel.inCyclicSubspace_iff_range D hD x p μ₀ hμ₀]
    exact hpS
  obtain ⟨μbase, μp, hμbase, hμp, hpbase⟩ :=
    CyclicMeasureType.cyclicSubspaceProperties D hD x p hpx
  have hbaseeq : μbase = μx := SpectralMeasure.eq_of_nat_moments μbase μx
    (fun n => (hμbase n).trans (hμx n).symm)
  have hpacx : μp.μ ≪ μx.μ := by simpa [hbaseeq] using hpbase
  obtain ⟨_, μr, _, hμr, _⟩ := CyclicMeasureType.cyclicSubspaceProperties
    D hD r r (self_mem_cyclic D r)
  have hprorth : OrthogonalCyclicSubspaces D p r :=
    cyclic_subspaces_orthogonal_of_mem D S p r hSred hSored hpS hrS
  have hμsum : μy.μ = μp.μ + μr.μ := by
    have hypr : p + r = y := by simp [r]
    rw [← hypr] at hμy
    exact orthogonal_sum_spectral_measure D p r μp μr μy hprorth hμp hμr hμy
  have hpacy : μp.μ ≪ μy.μ := by
    rw [hμsum]
    exact Measure.AbsolutelyContinuous.rfl.add_right μr.μ
  have hpSingY : Measure.MutuallySingular μp.μ μy.μ :=
    hsing.mono_ac hpacx Measure.AbsolutelyContinuous.rfl
  have hpzero : μp.μ = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hpacy hpSingY
  have hp0 : p = 0 := by
    have hm := hμp 0
    simpa [circleFourierCoefficient, hpzero] using hm.symm
  have hxS : x ∈ S := by
    change x ∈ CyclicSpectralModel.cyclicRange D hD x μ₀
    exact CyclicSpectralModel.x_mem_cyclicRange D hD x μ₀ hμ₀
  have hyS : y ∈ Sᗮ := by simpa [r, hp0] using hrS
  exact cyclic_subspaces_orthogonal_of_mem D S x y hSred hSored hxS hyS

theorem spectralRelations (D : HilbertOperatorData) :
    SpectralMeasureAbsoluteContinuityAndOrthogonality D := by
  intro hD
  refine ⟨?_, ?_, ?_⟩
  · intro x μ ν hμ hνμ
    exact exists_cyclic_vector_with_ac_measure D hD x μ ν hμ hνμ
  · intro x y μx μy μsum horth hμx hμy hμsum
    exact orthogonal_sum_spectral_measure D x y μx μy μsum horth hμx hμy hμsum
  · intro x y μx μy hμx hμy hsing
    exact singular_spectral_measures_orthogonal D hD x y μx μy hμx hμy hsing

end Chapter02.SpectralRelations
