import Chapter02.Spectral.DirectSumSpectralModel
import Chapter02.Spectral.RadonNikodymTransfer

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.HilbertDirectSum

universe u v

theorem two_toReal_pos : 0 < (2 : ENNReal).toReal := by norm_num

def coordinatewiseEquiv
    {E F : ℕ → Type*}
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℂ (F n)]
    (e : ∀ n, E n ≃ₗᵢ[ℂ] F n) : lp E 2 ≃ₗᵢ[ℂ] lp F 2 :=
  LinearIsometryEquiv.ofSurjective
    ({ toFun := fun x ↦ ⟨fun n ↦ e n (x n), by
          apply memℓp_gen
          simpa only [LinearIsometryEquiv.norm_map] using
            (lp.memℓp x).summable two_toReal_pos⟩
       map_add' := by
         intro x y
         apply lp.ext
         funext n
         exact (e n).map_add (x n) (y n)
       map_smul' := by
         intro c x
         apply lp.ext
         funext n
         exact (e n).map_smul c (x n)
       norm_map' := by
         intro x
         rw [lp.norm_eq_tsum_rpow two_toReal_pos,
           lp.norm_eq_tsum_rpow two_toReal_pos]
         apply congrArg (fun t : ℝ ↦ t ^ (1 / (2 : ENNReal).toReal))
         apply tsum_congr
         intro n
         change ‖e n (x n)‖ ^ (2 : ENNReal).toReal =
           ‖x n‖ ^ (2 : ENNReal).toReal
         rw [(e n).norm_map] } : lp E 2 →ₗᵢ[ℂ] lp F 2) (by
      intro y
      let x : lp E 2 := ⟨fun n ↦ (e n).symm (y n), by
        apply memℓp_gen
        simpa only [LinearIsometryEquiv.norm_map] using
          (lp.memℓp y).summable two_toReal_pos⟩
      refine ⟨x, ?_⟩
      apply lp.ext
      funext n
      exact (e n).apply_symm_apply (y n))

@[simp] theorem coordinatewiseEquiv_apply
    {E F : ℕ → Type*}
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℂ (E n)]
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℂ (F n)]
    (e : ∀ n, E n ≃ₗᵢ[ℂ] F n) (x : lp E 2) (n : ℕ) :
    coordinatewiseEquiv e x n = e n (x n) := rfl

set_option linter.unusedVariables false in
def component
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) (n : ℕ) : D.H :=
  CyclicSpectralModel.cyclicCLM D hD (x n) (μ n) (F n)

def model
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) : D.H :=
  ∑' n, component D hD x μ hμ F n

theorem component_norm
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) (n : ℕ) :
    ‖component D hD x μ hμ F n‖ = ‖F n‖ := by
  exact CyclicSpectralModel.cyclicCLM_norm D hD (x n) (μ n)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
    (F n)

theorem component_pairwise_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    SpectralDecomposition.PairwiseOrthogonalVectors (component D hD x μ hμ F) := by
  intro i j hij
  apply horth i j hij
  · rw [CyclicSpectralModel.inCyclicSubspace_iff_range D hD (x i)
        (component D hD x μ hμ F i) (μ i)
        (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
          (x i) (μ i) (hμ i))]
    exact ⟨F i, rfl⟩
  · rw [CyclicSpectralModel.inCyclicSubspace_iff_range D hD (x j)
        (component D hD x μ hμ F j) (μ j)
        (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
          (x j) (μ j) (hμ j))]
    exact ⟨F j, rfl⟩

theorem component_summable
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    Summable (component D hD x μ hμ F) := by
  apply SpectralDecomposition.summable_of_pairwise_orthogonal_of_summable_norm_sq
    (component D hD x μ hμ F)
    (component_pairwise_orthogonal D hD x μ hμ horth F)
  simpa only [component_norm D hD x μ hμ F,
    show (2 : ENNReal).toReal = 2 by norm_num, Real.rpow_two] using
    (lp.memℓp F).summable two_toReal_pos

theorem model_norm_sq
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    ‖model D hD x μ hμ F‖ ^ 2 = ‖F‖ ^ 2 := by
  rw [model, SpectralDecomposition.norm_tsum_sq_of_pairwise_orthogonal
    (component D hD x μ hμ F)
    (component_pairwise_orthogonal D hD x μ hμ horth F)]
  · simp_rw [component_norm]
    simpa only [show (2 : ENNReal).toReal = 2 by norm_num, Real.rpow_two] using
      (lp.hasSum_norm two_toReal_pos F).tsum_eq
  · simpa only [component_norm D hD x μ hμ F,
      show (2 : ENNReal).toReal = 2 by norm_num, Real.rpow_two] using
      (lp.memℓp F).summable two_toReal_pos

theorem model_norm
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    ‖model D hD x μ hμ F‖ = ‖F‖ := by
  have hs := model_norm_sq D hD x μ hμ horth F
  nlinarith [norm_nonneg (model D hD x μ hμ F), norm_nonneg F]

theorem model_add
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (F G : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    model D hD x μ hμ (F + G) =
      model D hD x μ hμ F + model D hD x μ hμ G := by
  unfold model
  have hF := component_summable D hD x μ hμ horth F
  have hG := component_summable D hD x μ hμ horth G
  rw [show component D hD x μ hμ (F + G) =
      fun n ↦ component D hD x μ hμ F n + component D hD x μ hμ G n by
    funext n
    simp [component]]
  exact hF.tsum_add hG

theorem model_smul
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (c : ℂ) (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    model D hD x μ hμ (c • F) = c • model D hD x μ hμ F := by
  unfold model
  have hF := component_summable D hD x μ hμ horth F
  rw [show component D hD x μ hμ (c • F) =
      fun n ↦ c • component D hD x μ hμ F n by
    funext n
    simp [component]]
  exact hF.tsum_const_smul c

theorem model_surjective
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x) :
    Function.Surjective (model D hD x μ hμ) := by
  intro y
  let F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2 :=
    ⟨fun n ↦ DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y n, by
      apply memℓp_gen
      have hraw := DirectSumSpectralModel.projectionRawFunction_mem
        D hD x μ hμ hdec.1 y
      simpa only [show (2 : ENNReal).toReal = 2 by norm_num, Real.rpow_two,
        ← MeasureTheory.Lp.norm_def] using hraw.2⟩
  refine ⟨F, ?_⟩
  unfold model
  have hcomp : component D hD x μ hμ F =
      SpectralDecomposition.cyclicProjectionFamily D x y := by
    funext n
    exact DirectSumSpectralModel.projectionCoordinate_spec D hD x μ hμ y n
  rw [hcomp]
  exact SpectralDecomposition.tsum_cyclicProjectionFamily_eq D x hdec y

def modelEquiv
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x) :
    lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2 ≃ₗᵢ[ℂ] D.H :=
  LinearIsometryEquiv.ofSurjective
    ({ toFun := model D hD x μ hμ
       map_add' := model_add D hD x μ hμ hdec.1
       map_smul' := model_smul D hD x μ hμ hdec.1
       norm_map' := model_norm D hD x μ hμ hdec.1 } :
      lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2 →ₗᵢ[ℂ] D.H)
    (model_surjective D hD x μ hμ hdec)

@[simp] theorem modelEquiv_apply
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    modelEquiv D hD x μ hμ hdec F = model D hD x μ hμ F := rfl

def coordinate (μ : ℕ → CircleMeasureData)
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2 :=
  ⟨fun n ↦ CyclicSpectralModel.coordinateLinear (μ n) (F n), by
    apply memℓp_gen
    simpa only [CyclicSpectralModel.coordinateLinear_norm] using
      (lp.memℓp F).summable two_toReal_pos⟩

@[simp] theorem coordinate_apply (μ : ℕ → CircleMeasureData)
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) (n : ℕ) :
    coordinate μ F n = CyclicSpectralModel.coordinateLinear (μ n) (F n) := rfl

theorem model_coordinate
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (F : lp (fun n ↦ Lp ℂ 2 (μ n).μ) 2) :
    model D hD x μ hμ (coordinate μ F) =
      D.U (model D hD x μ hμ F) := by
  unfold model
  have hsum := component_summable D hD x μ hμ hdec.1 F
  rw [show component D hD x μ hμ (coordinate μ F) =
      fun n ↦ D.U (component D hD x μ hμ F n) by
    funext n
    exact CyclicSpectralModel.cyclicCLM_intertwines D hD (x n) (μ n)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
        (x n) (μ n) (hμ n)) (F n)]
  exact (D.U.map_tsum hsum).symm

theorem modelEquiv_symm_operator
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x) (y : D.H) :
    (modelEquiv D hD x μ hμ hdec).symm (D.U y) =
      coordinate μ ((modelEquiv D hD x μ hμ hdec).symm y) := by
  apply (modelEquiv D hD x μ hμ hdec).injective
  rw [(modelEquiv D hD x μ hμ hdec).apply_symm_apply]
  change D.U y = model D hD x μ hμ
    (coordinate μ ((modelEquiv D hD x μ hμ hdec).symm y))
  rw [model_coordinate D hD x μ hμ hdec]
  congr 1
  change y = (modelEquiv D hD x μ hμ hdec)
    ((modelEquiv D hD x μ hμ hdec).symm y)
  exact ((modelEquiv D hD x μ hμ hdec).apply_symm_apply y).symm

end Chapter02.HilbertDirectSum
