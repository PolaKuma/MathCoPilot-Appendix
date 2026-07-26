import Chapter02.Common
import Chapter02.Ergodic.DenseExtension
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace Chapter02
namespace CircleFourier

lemma fourierCoeff_neg_nat_tendsto_zero_of_memLp_two
    {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ)
    (hf : MemLp f 2 AddCircle.haarAddCircle) :
    Tendsto (fun n : ℕ => fourierCoeff f (-(n : ℤ))) atTop (nhds 0) := by
  let F : Lp ℂ 2 AddCircle.haarAddCircle := hf.toLp f
  have hs : Summable (fun i : ℤ => ‖fourierCoeff (F : AddCircle T → ℂ) i‖ ^ 2) :=
    (hasSum_sq_fourierCoeff F).summable
  have hcoe : fourierCoeff (F : AddCircle T → ℂ) = fourierCoeff f :=
    fourierCoeff_congr_ae hf.coeFn_toLp
  rw [hcoe] at hs
  have hinj : Function.Injective (fun n : ℕ => -(n : ℤ)) := by
    intro m n h
    have h' : (m : ℤ) = (n : ℤ) := neg_injective h
    exact_mod_cast h'
  have hsum : Summable (fun n : ℕ => ‖fourierCoeff f (-(n : ℤ))‖ ^ 2) := by
    simpa [Function.comp_def] using hs.comp_injective hinj
  have hsq := hsum.tendsto_atTop_zero
  have hnorm : Tendsto (fun n : ℕ => ‖fourierCoeff f (-(n : ℤ))‖) atTop
      (nhds 0) := by
    have hsqrt := hsq.sqrt
    convert hsqrt using 1
    · funext n
      rw [Real.sqrt_sq (norm_nonneg _)]
    · simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hnorm) ε hε
  filter_upwards [hev] with n hn
  simpa [dist_zero_right, Real.dist_eq, abs_of_nonneg] using hn

lemma fourierCoeff_lipschitz {T : ℝ} [Fact (0 < T)]
    (F G : Lp ℂ 1 AddCircle.haarAddCircle) (n : ℤ) :
    dist (fourierCoeff (F : AddCircle T → ℂ) n)
      (fourierCoeff (G : AddCircle T → ℂ) n) ≤ dist F G := by
  rw [dist_eq_norm, dist_eq_norm]
  have hFi : Integrable (F : AddCircle T → ℂ) AddCircle.haarAddCircle :=
    (Lp.memLp F).integrable (by norm_num)
  have hGi : Integrable (G : AddCircle T → ℂ) AddCircle.haarAddCircle :=
    (Lp.memLp G).integrable (by norm_num)
  have hsubae : ((F - G : Lp ℂ 1 AddCircle.haarAddCircle) :
      AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
        fun x => F x - G x := Lp.coeFn_sub F G
  rw [fourierCoeff, fourierCoeff, ← integral_sub
    (hFi.fourier_smul _) (hGi.fourier_smul _)]
  simp_rw [← smul_sub]
  calc
    ‖∫ t : AddCircle T, fourier (-n) t • (F t - G t) ∂AddCircle.haarAddCircle‖ ≤
        ∫ t : AddCircle T, ‖fourier (-n) t • (F t - G t)‖
          ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ = ∫ t : AddCircle T, ‖F t - G t‖ ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_smul, show ‖(fourier (-n) t : ℂ)‖ = 1 by
        simp [fourier_apply], one_mul]
    _ = ‖F - G‖ := by
      rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
      rw [← integral_norm_eq_lintegral_enorm (Lp.memLp (F - G)).aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [hsubae] with t ht
      rw [ht]

lemma fourierCoeff_neg_nat_tendsto_zero {T : ℝ} [hT : Fact (0 < T)]
    (F : Lp ℂ 1 AddCircle.haarAddCircle) :
    Tendsto (fun n : ℕ => fourierCoeff (F : AddCircle T → ℂ) (-(n : ℤ)))
      atTop (nhds 0) := by
  let H := Lp ℂ 1 (@AddCircle.haarAddCircle T hT)
  have hdense : Dense (Lp.simpleFunc ℂ 1
      (@AddCircle.haarAddCircle T hT) : Set H) :=
    Lp.simpleFunc.dense (by norm_num)
  apply DenseExtension.tendsto_of_dense_of_uniform_dist hdense
    (fun (n : ℕ) F => fourierCoeff (F : AddCircle T → ℂ) (-(n : ℤ)))
    (fun _ => 0) 1 (by norm_num)
  · intro n x y
    simpa [H] using fourierCoeff_lipschitz (T := T) x y (-(n : ℤ))
  · intro x y
    simp
  · intro x hx
    let xs : Lp.simpleFunc ℂ 1 AddCircle.haarAddCircle := ⟨x, hx⟩
    let g : AddCircle T → ℂ := Lp.simpleFunc.toSimpleFunc xs
    have hg2 : MemLp g 2 AddCircle.haarAddCircle := by
      exact ((Lp.simpleFunc.toSimpleFunc xs).memLp_top
        AddCircle.haarAddCircle).mono_exponent (by norm_num)
    have hfourier : fourierCoeff g = fourierCoeff (x : AddCircle T → ℂ) := by
      apply fourierCoeff_congr_ae
      simpa [g, xs] using Lp.simpleFunc.toSimpleFunc_eq_toFun xs
    have hlim := fourierCoeff_neg_nat_tendsto_zero_of_memLp_two g hg2
    rw [hfourier] at hlim
    simpa [H] using hlim

noncomputable local instance circlePeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The probability Haar measure obtained by pushing normalized additive-circle Haar
measure through the exponential parametrization. -/
noncomputable def normalizedCircleHaar : Measure Circle :=
  Measure.map (fun x : AddCircle (2 * Real.pi) => x.toCircle)
    AddCircle.haarAddCircle

noncomputable local instance : IsProbabilityMeasure normalizedCircleHaar := by
  constructor
  rw [normalizedCircleHaar,
    Measure.map_apply AddCircle.continuous_toCircle.measurable MeasurableSet.univ]
  simp

noncomputable local instance : normalizedCircleHaar.IsHaarMeasure where
  lt_top_of_isCompact := by
    intro K hK
    exact measure_lt_top _ _
  map_mul_left_eq_self := by
    intro z
    obtain ⟨a, rfl⟩ :=
      (AddCircle.homeomorphCircle (by positivity : (2 * Real.pi) ≠ 0)).surjective z
    rw [AddCircle.homeomorphCircle_apply]
    calc
      Measure.map (fun y : Circle => (a.toCircle : Circle) * y) normalizedCircleHaar =
          Measure.map ((fun y : Circle => (a.toCircle : Circle) * y) ∘
            fun x : AddCircle (2 * Real.pi) => x.toCircle)
            AddCircle.haarAddCircle := by
              rw [normalizedCircleHaar, Measure.map_map]
              · exact (continuous_const.mul continuous_id).measurable
              · exact AddCircle.continuous_toCircle.measurable
      _ = Measure.map ((fun x : AddCircle (2 * Real.pi) => x.toCircle) ∘
            fun x => a + x) AddCircle.haarAddCircle := by
              congr 1
              funext x
              exact (AddCircle.toCircle_add a x).symm
      _ = Measure.map (fun x : AddCircle (2 * Real.pi) => x.toCircle)
            (Measure.map (fun x => a + x) AddCircle.haarAddCircle) := by
              rw [Measure.map_map]
              · exact AddCircle.continuous_toCircle.measurable
              · exact (continuous_const.add continuous_id).measurable
      _ = normalizedCircleHaar := by
              rw [MeasureTheory.map_add_left_eq_self]
              rfl
  open_pos := by
    intro U hU hUne
    rw [normalizedCircleHaar,
      Measure.map_apply AddCircle.continuous_toCircle.measurable hU.measurableSet]
    apply Measure.IsOpenPosMeasure.open_pos
    · exact hU.preimage AddCircle.continuous_toCircle
    · rcases hUne with ⟨z, hz⟩
      obtain ⟨x, hx⟩ :=
        (AddCircle.homeomorphCircle (by positivity : (2 * Real.pi) ≠ 0)).surjective z
      have hxc : x.toCircle = z := by
        simpa only [AddCircle.homeomorphCircle_apply] using hx
      exact ⟨x, by simpa only [Set.mem_preimage, hxc] using hz⟩

lemma normalizedCircleHaar_eq_smul_haar :
    normalizedCircleHaar = normalizedCircleHaar.haarScalarFactor Measure.haar •
      Measure.haar := by
  exact Measure.isMulInvariant_eq_smul_of_compactSpace _ _

lemma normalizedCircleHaar_factor_ne_zero :
    normalizedCircleHaar.haarScalarFactor Measure.haar ≠ 0 := by
  intro hc
  have huniv : normalizedCircleHaar Set.univ = 1 := measure_univ
  rw [normalizedCircleHaar_eq_smul_haar, hc, zero_smul] at huniv
  simp at huniv

lemma absolutelyContinuous_normalizedCircleHaar (μ : Measure Circle)
    (hμ : μ ≪ Measure.haar) : μ ≪ normalizedCircleHaar := by
  rw [normalizedCircleHaar_eq_smul_haar]
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  apply hμ
  rw [Measure.smul_apply] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left
    (ENNReal.coe_ne_zero.mpr normalizedCircleHaar_factor_ne_zero)

noncomputable def radonNikodymDensityNN
    (μ : CircleMeasureData) (z : Circle) : NNReal :=
  (μ.μ.rnDeriv normalizedCircleHaar z).toNNReal

lemma radonNikodymDensityNN_measurable (μ : CircleMeasureData) :
    Measurable (radonNikodymDensityNN μ) :=
  ENNReal.measurable_toNNReal.comp (Measure.measurable_rnDeriv _ _)

lemma radonNikodymDensityNN_ae (μ : CircleMeasureData) :
    (fun z => ((radonNikodymDensityNN μ z : NNReal) : ENNReal))
      =ᵐ[normalizedCircleHaar] μ.μ.rnDeriv normalizedCircleHaar := by
  filter_upwards [Measure.rnDeriv_ne_top μ.μ normalizedCircleHaar] with z hz
  exact ENNReal.coe_toNNReal hz

lemma withDensity_radonNikodymDensityNN (μ : CircleMeasureData)
    (hμ : μ.μ ≪ normalizedCircleHaar) :
    normalizedCircleHaar.withDensity
      (fun z => (radonNikodymDensityNN μ z : ENNReal)) = μ.μ := by
  rw [withDensity_congr_ae (radonNikodymDensityNN_ae μ)]
  exact Measure.withDensity_rnDeriv_eq _ _ hμ

lemma radonNikodymDensityComplex_integrable (μ : CircleMeasureData) :
    Integrable
      (fun z : Circle => ((μ.μ.rnDeriv normalizedCircleHaar z).toReal : ℂ))
      normalizedCircleHaar := by
  apply Integrable.ofReal
  simpa only [integrableOn_univ] using
    (Measure.integrableOn_toReal_rnDeriv
      (ν := normalizedCircleHaar) (s := Set.univ) (measure_ne_top μ.μ Set.univ))

noncomputable def toCircleMeasurePreserving :
    MeasurePreserving (fun x : AddCircle (2 * Real.pi) => x.toCircle)
      AddCircle.haarAddCircle normalizedCircleHaar := by
  refine MeasurePreserving.mk AddCircle.continuous_toCircle.measurable ?_
  rfl

lemma toCircle_measurableEmbedding : MeasurableEmbedding
    (fun x : AddCircle (2 * Real.pi) => x.toCircle) := by
  let e := AddCircle.homeomorphCircle
    (by positivity : (2 * Real.pi) ≠ 0)
  have heq : (fun x : AddCircle (2 * Real.pi) => x.toCircle) = e := by
    funext x
    exact (AddCircle.homeomorphCircle_apply _ x).symm
  rw [heq]
  exact e.measurableEmbedding

lemma radonNikodymDensityComplex_comp_memLp_one (μ : CircleMeasureData) :
    MemLp (fun x : AddCircle (2 * Real.pi) =>
      ((μ.μ.rnDeriv normalizedCircleHaar x.toCircle).toReal : ℂ))
      1 AddCircle.haarAddCircle := by
  rw [memLp_one_iff_integrable]
  have hcomp := (toCircleMeasurePreserving.integrable_comp_emb
    toCircle_measurableEmbedding).mpr (radonNikodymDensityComplex_integrable μ)
  simpa only [Function.comp_apply] using hcomp

lemma circleFourierCoefficient_eq_addCircleFourierCoeff
    (μ : CircleMeasureData) (hμ : μ.μ ≪ Measure.haar) (n : ℕ) :
    circleFourierCoefficient μ n = fourierCoeff
      (fun x : AddCircle (2 * Real.pi) =>
        ((μ.μ.rnDeriv normalizedCircleHaar x.toCircle).toReal : ℂ))
      (-(n : ℤ)) := by
  have hac : μ.μ ≪ normalizedCircleHaar :=
    absolutelyContinuous_normalizedCircleHaar μ.μ hμ
  rw [circleFourierCoefficient]
  nth_rewrite 1 [← withDensity_radonNikodymDensityNN μ hac]
  rw [integral_withDensity_eq_integral_smul
    (radonNikodymDensityNN_measurable μ)]
  rw [← toCircleMeasurePreserving.integral_comp toCircle_measurableEmbedding]
  rw [fourierCoeff]
  apply integral_congr_ae
  filter_upwards with x
  simp only [fourier_apply, radonNikodymDensityNN, ENNReal.toReal, neg_neg]
  rw [AddCircle.toCircle_zsmul]
  simp only [zpow_natCast]
  change (((μ.μ.rnDeriv normalizedCircleHaar x.toCircle).toNNReal : ℝ) : ℂ) *
      (x.toCircle : ℂ) ^ n =
    (x.toCircle : ℂ) ^ n *
      (((μ.μ.rnDeriv normalizedCircleHaar x.toCircle).toNNReal : ℝ) : ℂ)
  exact mul_comm _ _

/-- Riemann--Lebesgue for finite circle measures absolutely continuous with respect
to the Haar measure used in the chapter. -/
theorem riemannLebesgue : RiemannLebesgueStatement := by
  intro μ hμ
  let f : AddCircle (2 * Real.pi) → ℂ := fun x =>
    ((μ.μ.rnDeriv normalizedCircleHaar x.toCircle).toReal : ℂ)
  have hf : MemLp f 1 AddCircle.haarAddCircle := by
    simpa [f] using radonNikodymDensityComplex_comp_memLp_one μ
  let F : Lp ℂ 1 AddCircle.haarAddCircle := hf.toLp f
  have hlim := fourierCoeff_neg_nat_tendsto_zero F
  have hfourier : fourierCoeff (F : AddCircle (2 * Real.pi) → ℂ) =
      fourierCoeff f := fourierCoeff_congr_ae hf.coeFn_toLp
  rw [hfourier] at hlim
  convert hlim using 1
  funext n
  exact circleFourierCoefficient_eq_addCircleFourierCoeff μ hμ n

end CircleFourier
end Chapter02
