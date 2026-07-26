import Chapter02.Spectral.OrthogonalCyclicDecomposition
import Chapter02.Spectral.SpectralMeasure
import Chapter02.Spectral.SpectralPointMass

open Classical Filter Set

noncomputable section

namespace Chapter02.MaximalSpectralType

universe u

def spectralCoefficient (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (n : ℕ) : ℂ :=
  (((1 / 2 : ℝ) ^ n / (1 + ‖x n‖) : ℝ) : ℂ)

theorem spectralCoefficient_ne_zero (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (n : ℕ) : spectralCoefficient D x n ≠ 0 := by
  unfold spectralCoefficient
  norm_cast
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

theorem norm_spectralCoefficient_smul_le (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (n : ℕ) :
    ‖spectralCoefficient D x n • x n‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [norm_smul]
  unfold spectralCoefficient
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  have hden : 0 < 1 + ‖x n‖ := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  nlinarith [norm_nonneg (x n)]

theorem summable_spectralCoefficient_smul (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) : Summable (fun n ↦ spectralCoefficient D x n • x n) := by
  exact Summable.of_norm_bounded summable_geometric_two
    (norm_spectralCoefficient_smul_le D x)

theorem summable_norm_sq_spectralCoefficient_smul
    (D : HilbertOperatorData.{u}) (x : ℕ → D.H) :
    Summable (fun n ↦ ‖spectralCoefficient D x n • x n‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ sq_nonneg ‖spectralCoefficient D x n • x n‖)
    (fun n ↦ ?_) summable_geometric_two
  have hle := norm_spectralCoefficient_smul_le D x n
  have hgeom_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hgeom_le_one : (1 / 2 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [norm_nonneg (spectralCoefficient D x n • x n)]

/-- A single vector whose spectral measure will dominate all measures in an
orthogonal cyclic decomposition. -/
def maximalTypeVector (D : HilbertOperatorData.{u}) (x : ℕ → D.H) : D.H :=
  ∑' n, spectralCoefficient D x n • x n

theorem hasSum_maximalTypeVector (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) :
    HasSum (fun n ↦ spectralCoefficient D x n • x n)
      (maximalTypeVector D x) :=
  (summable_spectralCoefficient_smul D x).hasSum

theorem spectralMeasure_univ (D : HilbertOperatorData.{u}) (x : D.H)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ) :
    μ.μ Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hm := SpectralPointMass.spectral_mass D x μ hμ
  rw [← hm]
  exact (ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top μ.μ Set.univ)).symm

def weightedComponentMeasure (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData) (n : ℕ) :
    MeasureTheory.Measure Circle :=
  ENNReal.ofReal (‖spectralCoefficient D x n‖ ^ 2) • (μ n).μ

def weightedComponentCircleMeasure (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData) (n : ℕ) :
    CircleMeasureData where
  μ := weightedComponentMeasure D x μ n
  isFinite := by
    refine ⟨?_⟩
    rw [weightedComponentMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (MeasureTheory.measure_lt_top (μ n).μ Set.univ)

theorem weightedComponentMeasure_univ (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n)) (n : ℕ) :
    weightedComponentMeasure D x μ n Set.univ =
      ENNReal.ofReal (‖spectralCoefficient D x n • x n‖ ^ 2) := by
  rw [weightedComponentMeasure, MeasureTheory.Measure.smul_apply,
    spectralMeasure_univ D (x n) (μ n) (hμ n)]
  rw [smul_eq_mul, ← ENNReal.ofReal_mul (sq_nonneg _)]
  apply congrArg ENNReal.ofReal
  rw [norm_smul]
  ring

/-- The countable positive sum of the weighted component spectral measures. -/
def maximalTypeMeasure (D : HilbertOperatorData.{u})
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n)) : CircleMeasureData where
  μ := MeasureTheory.Measure.sum (weightedComponentMeasure D x μ)
  isFinite := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.sum_apply _ MeasurableSet.univ]
    simp_rw [weightedComponentMeasure_univ D x μ hμ]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ sq_nonneg ‖spectralCoefficient D x n • x n‖)
      (summable_norm_sq_spectralCoefficient_smul D x)]
    exact ENNReal.ofReal_lt_top

theorem iterate_smul (D : HilbertOperatorData.{u}) (c : ℂ)
    (y : D.H) (n : ℕ) : (D.U^[n]) (c • y) = c • (D.U^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        map_smul]

theorem weightedComponentMeasure_isSpectral
    (D : HilbertOperatorData.{u}) (x : ℕ → D.H)
    (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n)) (i : ℕ) :
    HasSpectralMeasure D (spectralCoefficient D x i • x i)
      (weightedComponentCircleMeasure D x μ i) := by
  intro n
  rw [circleFourierCoefficient]
  change (∫ z : Circle, (z : ℂ) ^ (n : ℤ)
      ∂weightedComponentMeasure D x μ i) = _
  rw [weightedComponentMeasure, MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  change (‖spectralCoefficient D x i‖ ^ 2 : ℝ) •
      circleFourierCoefficient (μ i) n = _
  rw [hμ i n, iterate_smul, inner_smul_left, inner_smul_right]
  rw [Complex.real_smul]
  rw [show ((‖spectralCoefficient D x i‖ ^ 2 : ℝ) : ℂ) =
      star (spectralCoefficient D x i) * spectralCoefficient D x i by
    rw [← Complex.normSq_eq_norm_sq]
    exact Complex.normSq_eq_conj_mul_self]
  rw [mul_assoc]
  rw [starRingEnd_apply]

theorem scaledComponents_pairwise_orthogonal
    (D : HilbertOperatorData.{u}) (x : ℕ → D.H)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j)) :
    ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D
      (spectralCoefficient D x i • x i)
      (spectralCoefficient D x j • x j) := by
  intro i j hij a b ha hb
  apply horth i j hij a b
  · exact ha _ (SpectralDecomposition.cyclicSubmodule_reducing D (x i))
      ((SpectralDecomposition.cyclicSubmodule D (x i)).smul_mem _
        (SpectralDecomposition.generator_mem_cyclicSubmodule D (x i)))
  · exact hb _ (SpectralDecomposition.cyclicSubmodule_reducing D (x j))
      ((SpectralDecomposition.cyclicSubmodule D (x j)).smul_mem _
        (SpectralDecomposition.generator_mem_cyclicSubmodule D (x j)))

theorem iterate_finset_sum (D : HilbertOperatorData.{u})
    (z : ℕ → D.H) (s : Finset ℕ) (n : ℕ) :
    (D.U^[n]) (∑ i ∈ s, z i) = ∑ i ∈ s, (D.U^[n]) (z i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        SpectralRelations.iterate_add, ih]

theorem finite_scaled_correlation
    (D : HilbertOperatorData.{u}) (x : ℕ → D.H)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (s : Finset ℕ) (n : ℕ) :
    @inner ℂ D.H _
      (∑ i ∈ s, spectralCoefficient D x i • x i)
      ((D.U^[n]) (∑ i ∈ s, spectralCoefficient D x i • x i)) =
    ∑ i ∈ s, @inner ℂ D.H _
      (spectralCoefficient D x i • x i)
      ((D.U^[n]) (spectralCoefficient D x i • x i)) := by
  rw [iterate_finset_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · intro j hj hji
    exact scaledComponents_pairwise_orthogonal D x horth i j hji.symm
      (spectralCoefficient D x i • x i)
      ((D.U^[n]) (spectralCoefficient D x j • x j))
      (SpectralRelations.self_mem_cyclic D _)
      (SpectralRelations.iterate_mem_cyclic D _ n)
  · intro hnot
    exact (hnot hi).elim

theorem unitary_iterate_norm (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (y : D.H) (n : ℕ) :
    ‖(D.U^[n]) y‖ = ‖y‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', hD.2, ih]

theorem summable_scaled_correlations (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (n : ℕ) :
    Summable (fun i ↦ @inner ℂ D.H _
      (spectralCoefficient D x i • x i)
      ((D.U^[n]) (spectralCoefficient D x i • x i))) := by
  apply Summable.of_norm_bounded
    (summable_norm_sq_spectralCoefficient_smul D x)
  intro i
  calc
    ‖@inner ℂ D.H _ (spectralCoefficient D x i • x i)
        ((D.U^[n]) (spectralCoefficient D x i • x i))‖ ≤
        ‖spectralCoefficient D x i • x i‖ *
          ‖(D.U^[n]) (spectralCoefficient D x i • x i)‖ :=
      norm_inner_le_norm _ _
    _ = ‖spectralCoefficient D x i • x i‖ ^ 2 := by
      rw [unitary_iterate_norm D hD]
      ring

theorem maximalTypeVector_correlation (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (n : ℕ) :
    @inner ℂ D.H _ (maximalTypeVector D x)
      ((D.U^[n]) (maximalTypeVector D x)) =
    ∑' i, @inner ℂ D.H _ (spectralCoefficient D x i • x i)
      ((D.U^[n]) (spectralCoefficient D x i • x i)) := by
  let p : ℕ → D.H := fun N ↦
    ∑ i ∈ Finset.range N, spectralCoefficient D x i • x i
  have hp : Tendsto p atTop (nhds (maximalTypeVector D x)) :=
    (hasSum_maximalTypeVector D x).tendsto_sum_nat
  have hUp : Tendsto (fun N ↦ (D.U^[n]) (p N)) atTop
      (nhds ((D.U^[n]) (maximalTypeVector D x))) := by
    have hpow (y : D.H) : (D.U ^ n) y = (D.U^[n]) y := by
      rw [ContinuousLinearMap.coe_pow]
    simp_rw [← hpow]
    exact (D.U ^ n).continuous.continuousAt.tendsto.comp hp
  have hinner := hp.inner (𝕜 := ℂ) hUp
  have hfun : (fun N ↦ @inner ℂ D.H _ (p N) ((D.U^[n]) (p N))) =
      (fun N ↦ ∑ i ∈ Finset.range N, @inner ℂ D.H _
        (spectralCoefficient D x i • x i)
        ((D.U^[n]) (spectralCoefficient D x i • x i))) := by
    funext N
    exact finite_scaled_correlation D x horth (Finset.range N) n
  rw [hfun] at hinner
  exact tendsto_nhds_unique hinner
    (summable_scaled_correlations D hD x n).hasSum.tendsto_sum_nat

theorem maximalTypeMeasure_isSpectral (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (μ : ℕ → CircleMeasureData)
    (hμ : ∀ i, HasSpectralMeasure D (x i) (μ i)) :
    HasSpectralMeasure D (maximalTypeVector D x)
      (maximalTypeMeasure D x μ hμ) := by
  intro n
  have hint : MeasureTheory.Integrable (fun z : Circle => (z : ℂ) ^ (n : ℤ))
      (maximalTypeMeasure D x μ hμ).μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)
  rw [circleFourierCoefficient]
  change (∫ z : Circle, (z : ℂ) ^ (n : ℤ)
      ∂MeasureTheory.Measure.sum (weightedComponentMeasure D x μ)) = _
  rw [MeasureTheory.integral_sum_measure hint]
  change (∑' i, circleFourierCoefficient
    (weightedComponentCircleMeasure D x μ i) n) = _
  have hterm : (fun i ↦ circleFourierCoefficient
      (weightedComponentCircleMeasure D x μ i) n) =
      (fun i ↦ @inner ℂ D.H _ (spectralCoefficient D x i • x i)
        ((D.U^[n]) (spectralCoefficient D x i • x i))) := by
    funext i
    exact weightedComponentMeasure_isSpectral D x μ hμ i n
  rw [hterm]
  exact (maximalTypeVector_correlation D hD x horth n).symm

theorem componentMeasure_absolutelyContinuous_maximalTypeMeasure
    (D : HilbertOperatorData.{u}) (x : ℕ → D.H)
    (μ : ℕ → CircleMeasureData)
    (hμ : ∀ i, HasSpectralMeasure D (x i) (μ i)) (i : ℕ) :
    MeasureTheory.Measure.AbsolutelyContinuous (μ i).μ
      (maximalTypeMeasure D x μ hμ).μ := by
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  have hle := MeasureTheory.Measure.le_sum
    (weightedComponentMeasure D x μ) i s
  have hwzero : weightedComponentMeasure D x μ i s = 0 := by
    change (MeasureTheory.Measure.sum (weightedComponentMeasure D x μ)) s = 0
      at hzero
    exact nonpos_iff_eq_zero.mp (hle.trans_eq hzero)
  rw [weightedComponentMeasure, MeasureTheory.Measure.smul_apply,
    smul_eq_mul] at hwzero
  exact (mul_eq_zero.mp hwzero).resolve_left
    (ENNReal.ofReal_ne_zero_iff.2 (sq_pos_of_pos
      (norm_pos_iff.mpr (spectralCoefficient_ne_zero D x i))))

/-- The sum of the spectral measures of a square-summable orthogonal family. -/
def spectralSumMeasure (D : HilbertOperatorData.{u}) (z : ℕ → D.H)
    (ν : ℕ → CircleMeasureData)
    (hν : ∀ i, HasSpectralMeasure D (z i) (ν i))
    (hsq : Summable (fun i ↦ ‖z i‖ ^ 2)) : CircleMeasureData where
  μ := MeasureTheory.Measure.sum (fun i ↦ (ν i).μ)
  isFinite := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.sum_apply _ MeasurableSet.univ]
    simp_rw [spectralMeasure_univ D (z _) (ν _) (hν _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ sq_nonneg ‖z i‖) hsq]
    exact ENNReal.ofReal_lt_top

theorem finite_correlation_of_pairwise_orthogonal
    (D : HilbertOperatorData.{u}) (z : ℕ → D.H)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (z i) (z j))
    (s : Finset ℕ) (n : ℕ) :
    @inner ℂ D.H _ (∑ i ∈ s, z i) ((D.U^[n]) (∑ i ∈ s, z i)) =
      ∑ i ∈ s, @inner ℂ D.H _ (z i) ((D.U^[n]) (z i)) := by
  rw [iterate_finset_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · intro j hj hji
    exact horth i j hji.symm (z i) ((D.U^[n]) (z j))
      (SpectralRelations.self_mem_cyclic D _)
      (SpectralRelations.iterate_mem_cyclic D _ n)
  · intro hnot
    exact (hnot hi).elim

theorem summable_correlations_of_summable_norm_sq
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (z : ℕ → D.H)
    (hsq : Summable (fun i ↦ ‖z i‖ ^ 2)) (n : ℕ) :
    Summable (fun i ↦ @inner ℂ D.H _ (z i) ((D.U^[n]) (z i))) := by
  apply Summable.of_norm_bounded hsq
  intro i
  calc
    ‖@inner ℂ D.H _ (z i) ((D.U^[n]) (z i))‖ ≤
        ‖z i‖ * ‖(D.U^[n]) (z i)‖ := norm_inner_le_norm _ _
    _ = ‖z i‖ ^ 2 := by rw [unitary_iterate_norm D hD]; ring

theorem hasSum_correlation_of_orthogonal_family
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (z : ℕ → D.H) (y : D.H) (hzsum : HasSum z y)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (z i) (z j))
    (hsq : Summable (fun i ↦ ‖z i‖ ^ 2)) (n : ℕ) :
    @inner ℂ D.H _ y ((D.U^[n]) y) =
      ∑' i, @inner ℂ D.H _ (z i) ((D.U^[n]) (z i)) := by
  have hp : Tendsto (fun N ↦ ∑ i ∈ Finset.range N, z i) atTop (nhds y) :=
    hzsum.tendsto_sum_nat
  have hUp : Tendsto
      (fun N ↦ (D.U^[n]) (∑ i ∈ Finset.range N, z i)) atTop
      (nhds ((D.U^[n]) y)) := by
    have hpow (w : D.H) : (D.U ^ n) w = (D.U^[n]) w := by
      rw [ContinuousLinearMap.coe_pow]
    simp_rw [← hpow]
    exact (D.U ^ n).continuous.continuousAt.tendsto.comp hp
  have hinner := hp.inner (𝕜 := ℂ) hUp
  have hfun : (fun N ↦ @inner ℂ D.H _
      (∑ i ∈ Finset.range N, z i)
      ((D.U^[n]) (∑ i ∈ Finset.range N, z i))) =
      (fun N ↦ ∑ i ∈ Finset.range N,
        @inner ℂ D.H _ (z i) ((D.U^[n]) (z i))) := by
    funext N
    exact finite_correlation_of_pairwise_orthogonal D z horth _ n
  rw [hfun] at hinner
  exact tendsto_nhds_unique hinner
    (summable_correlations_of_summable_norm_sq D hD z hsq n).hasSum.tendsto_sum_nat

theorem spectralSumMeasure_isSpectral
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (z : ℕ → D.H) (y : D.H) (hzsum : HasSum z y)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (z i) (z j))
    (ν : ℕ → CircleMeasureData)
    (hν : ∀ i, HasSpectralMeasure D (z i) (ν i))
    (hsq : Summable (fun i ↦ ‖z i‖ ^ 2)) :
    HasSpectralMeasure D y (spectralSumMeasure D z ν hν hsq) := by
  intro n
  have hint : MeasureTheory.Integrable (fun w : Circle => (w : ℂ) ^ (n : ℤ))
      (spectralSumMeasure D z ν hν hsq).μ :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)
  rw [circleFourierCoefficient]
  change (∫ w : Circle, (w : ℂ) ^ (n : ℤ)
      ∂MeasureTheory.Measure.sum (fun i ↦ (ν i).μ)) = _
  rw [MeasureTheory.integral_sum_measure hint]
  change (∑' i, circleFourierCoefficient (ν i) n) = _
  have hterm : (fun i ↦ circleFourierCoefficient (ν i) n) =
      (fun i ↦ @inner ℂ D.H _ (z i) ((D.U^[n]) (z i))) := by
    funext i
    exact hν i n
  rw [hterm]
  exact (hasSum_correlation_of_orthogonal_family D hD z y hzsum horth hsq n).symm

theorem cyclicProjectionFamily_pairwise_cyclic_orthogonal
    (D : HilbertOperatorData.{u}) (x : ℕ → D.H)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (y : D.H) :
    ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D
      (SpectralDecomposition.cyclicProjectionFamily D x y i)
      (SpectralDecomposition.cyclicProjectionFamily D x y j) := by
  intro i j hij a b ha hb
  apply horth i j hij a b
  · exact ha _ (SpectralDecomposition.cyclicSubmodule_reducing D (x i))
      (SpectralDecomposition.cyclicProjectionFamily_mem D x y i)
  · exact hb _ (SpectralDecomposition.cyclicSubmodule_reducing D (x j))
      (SpectralDecomposition.cyclicProjectionFamily_mem D x y j)

theorem exists_projection_spectralMeasure_ac
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ i, HasSpectralMeasure D (x i) (μ i))
    (y : D.H) (i : ℕ) :
    ∃ ν : CircleMeasureData,
      HasSpectralMeasure D
        (SpectralDecomposition.cyclicProjectionFamily D x y i) ν ∧
      MeasureTheory.Measure.AbsolutelyContinuous ν.μ (μ i).μ := by
  obtain ⟨μx, ν, hμx, hν, hac⟩ :=
    CyclicMeasureType.cyclicSubspaceProperties D hD (x i)
      (SpectralDecomposition.cyclicProjectionFamily D x y i)
      (SpectralDecomposition.cyclicProjectionFamily_mem D x y i)
  have heq : μx = μ i := SpectralMeasure.eq_of_nat_moments μx (μ i)
    (fun n ↦ (hμx n).trans (hμ i n).symm)
  subst μx
  exact ⟨ν, hν, hac⟩

theorem maximalTypeVector_mem_submodule
    (D : HilbertOperatorData.{u}) (S : Submodule ℂ D.H)
    (hS : IsClosedReducingSubspace D (S : Set D.H))
    (x : ℕ → D.H) (hxS : ∀ n, x n ∈ S) :
    maximalTypeVector D x ∈ S := by
  apply hS.2.2.1
    (fun N ↦ ∑ n ∈ Finset.range N, spectralCoefficient D x n • x n)
    (fun N ↦ by
      apply Submodule.sum_mem
      intro n hn
      exact S.smul_mem _ (hxS n))
    (maximalTypeVector D x)
    (hasSum_maximalTypeVector D x).tendsto_sum_nat

theorem maximalTypeVector_dominates_on_submodule
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (S : Submodule ℂ D.H) (x : ℕ → D.H)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (hcomplete : ∀ y : D.H, y ∈ S →
      ∑' n, SpectralDecomposition.cyclicProjectionFamily D x y n = y)
    (μ : ℕ → CircleMeasureData)
    (hμ : ∀ i, HasSpectralMeasure D (x i) (μ i))
    (y : D.H) (hyS : y ∈ S) :
    SpectralMeasureDominatesVector D (maximalTypeVector D x) y := by
  intro μmax μy hμmax hμy
  let z : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D x y
  choose ν hν hac using fun i ↦
    exists_projection_spectralMeasure_ac D hD x μ hμ y i
  have hzsum : HasSum z y := by
    have hsum := SpectralDecomposition.cyclicProjectionFamily_summable
      D x horth y
    exact (hcomplete y hyS) ▸ hsum.hasSum
  have hzorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (z i) (z j) :=
    cyclicProjectionFamily_pairwise_cyclic_orthogonal D x horth y
  have hzsq : Summable (fun i ↦ ‖z i‖ ^ 2) :=
    SpectralDecomposition.cyclicProjectionFamily_norm_sq_summable D x horth y
  let νsum := spectralSumMeasure D z ν hν hzsq
  have hνsum : HasSpectralMeasure D y νsum :=
    spectralSumMeasure_isSpectral D hD z y hzsum hzorth ν hν hzsq
  have hmaxCanonical : HasSpectralMeasure D (maximalTypeVector D x)
      (maximalTypeMeasure D x μ hμ) :=
    maximalTypeMeasure_isSpectral D hD x horth μ hμ
  have heqmax : μmax = maximalTypeMeasure D x μ hμ :=
    SpectralMeasure.eq_of_nat_moments _ _
      (fun n ↦ (hμmax n).trans (hmaxCanonical n).symm)
  have heqy : μy = νsum := SpectralMeasure.eq_of_nat_moments _ _
    (fun n ↦ (hμy n).trans (hνsum n).symm)
  subst μmax
  subst μy
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  change (MeasureTheory.Measure.sum (fun i ↦ (ν i).μ)) s = 0
  rw [MeasureTheory.Measure.sum_apply _ hs]
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  exact (hac i |>.trans
    (componentMeasure_absolutelyContinuous_maximalTypeMeasure D x μ hμ i)) hzero

theorem maximalTypeVector_dominates_every_vector
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (hdec : IsOrthogonalCyclicDecomposition D x)
    (μ : ℕ → CircleMeasureData)
    (hμ : ∀ i, HasSpectralMeasure D (x i) (μ i)) (y : D.H) :
    SpectralMeasureDominatesVector D (maximalTypeVector D x) y := by
  intro μmax μy hμmax hμy
  let z : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D x y
  choose ν hν hac using fun i ↦
    exists_projection_spectralMeasure_ac D hD x μ hμ y i
  have hzsum : HasSum z y := by
    have hsum := SpectralDecomposition.cyclicProjectionFamily_summable
      D x hdec.1 y
    exact (SpectralDecomposition.tsum_cyclicProjectionFamily_eq D x hdec y) ▸
      hsum.hasSum
  have hzorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (z i) (z j) :=
    cyclicProjectionFamily_pairwise_cyclic_orthogonal D x hdec.1 y
  have hzsq : Summable (fun i ↦ ‖z i‖ ^ 2) :=
    SpectralDecomposition.cyclicProjectionFamily_norm_sq_summable D x hdec.1 y
  let νsum := spectralSumMeasure D z ν hν hzsq
  have hνsum : HasSpectralMeasure D y νsum :=
    spectralSumMeasure_isSpectral D hD z y hzsum hzorth ν hν hzsq
  have hmaxCanonical : HasSpectralMeasure D (maximalTypeVector D x)
      (maximalTypeMeasure D x μ hμ) :=
    maximalTypeMeasure_isSpectral D hD x hdec.1 μ hμ
  have heqmax : μmax = maximalTypeMeasure D x μ hμ :=
    SpectralMeasure.eq_of_nat_moments _ _
      (fun n ↦ (hμmax n).trans (hmaxCanonical n).symm)
  have heqy : μy = νsum := SpectralMeasure.eq_of_nat_moments _ _
    (fun n ↦ (hμy n).trans (hνsum n).symm)
  subst μmax
  subst μy
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  change (MeasureTheory.Measure.sum (fun i ↦ (ν i).μ)) s = 0
  rw [MeasureTheory.Measure.sum_apply _ hs]
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  exact (hac i |>.trans
    (componentMeasure_absolutelyContinuous_maximalTypeMeasure D x μ hμ i)) hzero

theorem maximalTypeMeasure_isMaximal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (hdec : IsOrthogonalCyclicDecomposition D x)
    (μ : ℕ → CircleMeasureData)
    (hμ : ∀ i, HasSpectralMeasure D (x i) (μ i)) :
    IsMaximalSpectralMeasure D (maximalTypeMeasure D x μ hμ) := by
  refine ⟨hD, ⟨maximalTypeVector D x,
    maximalTypeMeasure_isSpectral D hD x hdec.1 μ hμ⟩, ?_⟩
  intro y
  obtain ⟨μy, hμy, _⟩ := SpectralMeasure.spectralMeasure D hD y
  refine ⟨μy, hμy, ?_⟩
  exact maximalTypeVector_dominates_every_vector D hD x hdec μ hμ y
    (maximalTypeMeasure D x μ hμ) μy
    (maximalTypeMeasure_isSpectral D hD x hdec.1 μ hμ) hμy

theorem exists_maximalSpectralMeasure
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D) :
    ∃ μ : CircleMeasureData, IsMaximalSpectralMeasure D μ := by
  obtain ⟨x, hdec⟩ :=
    OrthogonalCyclicDecomposition.exists_orthogonalCyclicDecomposition D hsep hD
  choose μ hμ _huniq using fun i ↦ SpectralMeasure.spectralMeasure D hD (x i)
  exact ⟨maximalTypeMeasure D x μ hμ,
    maximalTypeMeasure_isMaximal D hD x hdec μ hμ⟩

end Chapter02.MaximalSpectralType
