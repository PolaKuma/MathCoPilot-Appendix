import Chapter02.Spectral.DirectSumSpectralModel
import Chapter02.Spectral.MaximalSpectralType
import Chapter02.Spectral.RadonNikodymTransfer
import Chapter02.Spectral.OrderedSpectralDecomposition

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.DirectSumMeasureCoordinates

universe u

def projectionDensityMeasure (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (y : D.H) (n : ℕ) : CircleMeasureData :=
  CyclicMeasureType.vectorDensityMeasure
    (DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y n)

theorem projectionDensityMeasure_isSpectral
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (y : D.H) (n : ℕ) :
    HasSpectralMeasure D
      (SpectralDecomposition.cyclicProjectionFamily D x y n)
      (projectionDensityMeasure D hD x μ hμ y n) := by
  let F := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y n
  have hm := CyclicMeasureType.vectorDensityMeasure_moment D hD (x n) (μ n)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
    F
  intro k
  change circleFourierCoefficient (CyclicMeasureType.vectorDensityMeasure F) k = _
  rw [hm]
  rw [DirectSumSpectralModel.projectionCoordinate_spec]

theorem projectionDensityMeasure_absolutelyContinuous
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (y : D.H) (n : ℕ) :
    (projectionDensityMeasure D hD x μ hμ y n).μ ≪ (μ n).μ :=
  CyclicMeasureType.vectorDensityMeasure_absolutelyContinuous _

/-- The spectral measure of a vector is the countable sum of the density
measures of its coordinates in an orthogonal cyclic decomposition. -/
theorem spectralMeasure_eq_sum_projectionDensityMeasure
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (y : D.H) (ν : CircleMeasureData) (hν : HasSpectralMeasure D y ν) :
    ν.μ = Measure.sum
      (fun n ↦ (projectionDensityMeasure D hD x μ hμ y n).μ) := by
  let z : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D x y
  let ρ : ℕ → CircleMeasureData :=
    fun n ↦ projectionDensityMeasure D hD x μ hμ y n
  have hρ : ∀ n, HasSpectralMeasure D (z n) (ρ n) :=
    projectionDensityMeasure_isSpectral D hD x μ hμ y
  have hzsum : HasSum z y := by
    have hs := SpectralDecomposition.cyclicProjectionFamily_summable
      D x hdec.1 y
    exact (SpectralDecomposition.tsum_cyclicProjectionFamily_eq D x hdec y) ▸
      hs.hasSum
  have hzorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (z i) (z j) :=
    MaximalSpectralType.cyclicProjectionFamily_pairwise_cyclic_orthogonal
      D x hdec.1 y
  have hzsq : Summable (fun i ↦ ‖z i‖ ^ 2) :=
    SpectralDecomposition.cyclicProjectionFamily_norm_sq_summable D x hdec.1 y
  have hsum : HasSpectralMeasure D y
      (MaximalSpectralType.spectralSumMeasure D z ρ hρ hzsq) :=
    MaximalSpectralType.spectralSumMeasure_isSpectral
      D hD z y hzsum hzorth ρ hρ hzsq
  have heq : ν = MaximalSpectralType.spectralSumMeasure D z ρ hρ hzsq :=
    SpectralMeasure.eq_of_nat_moments _ _
      (fun k ↦ (hν k).trans (hsum k).symm)
  exact congrArg CircleMeasureData.μ heq

theorem projectionDensityMeasure_le_spectralMeasure
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (y : D.H) (ν : CircleMeasureData) (hν : HasSpectralMeasure D y ν)
    (j : ℕ) :
    (projectionDensityMeasure D hD x μ hμ y j).μ ≤ ν.μ := by
  rw [spectralMeasure_eq_sum_projectionDensityMeasure D hD x μ hμ hdec y ν hν]
  exact Measure.le_sum _ j

/-- A coordinate vanishes when the vector spectral measure and the base
coordinate measure are supported on disjoint sides of a measurable cut. -/
theorem projectionCoordinate_eq_zero_of_support
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (y : D.H) (ν : CircleMeasureData) (hν : HasSpectralMeasure D y ν)
    (B : Set Circle) (hνBc : ν.μ Bᶜ = 0) (j : ℕ)
    (hμjB : (μ j).μ B = 0) :
    DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y j = 0 := by
  let ρ := projectionDensityMeasure D hD x μ hμ y j
  have hρB : ρ.μ B = 0 :=
    projectionDensityMeasure_absolutelyContinuous D hD x μ hμ y j hμjB
  have hρBc : ρ.μ Bᶜ = 0 := by
    exact nonpos_iff_eq_zero.mp
      ((projectionDensityMeasure_le_spectralMeasure
        D hD x μ hμ hdec y ν hν j Bᶜ).trans_eq hνBc)
  have hρuniv : ρ.μ Set.univ = 0 := by
    apply le_antisymm
    · calc
        ρ.μ Set.univ = ρ.μ (B ∪ Bᶜ) := by congr 1; ext z; simp
        _ ≤ ρ.μ B + ρ.μ Bᶜ := measure_union_le _ _
        _ = 0 := by rw [hρB, hρBc, add_zero]
    · exact bot_le
  let z := SpectralDecomposition.cyclicProjectionFamily D x y j
  have hzspec : HasSpectralMeasure D z ρ :=
    projectionDensityMeasure_isSpectral D hD x μ hμ y j
  have hznorm : ‖z‖ ^ 2 = 0 := by
    have hm := MaximalSpectralType.spectralMeasure_univ D z ρ hzspec
    rw [hρuniv] at hm
    have hle := ENNReal.ofReal_eq_zero.mp hm.symm
    nlinarith [sq_nonneg ‖z‖]
  have hz0 : z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hznorm)
  let F := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y j
  have heq : CyclicSpectralModel.cyclicIsometry D hD (x j) (μ j)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x j) (μ j) (hμ j)) F =
      CyclicSpectralModel.cyclicIsometry D hD (x j) (μ j)
        (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x j) (μ j) (hμ j)) 0 := by
    rw [map_zero]
    change CyclicSpectralModel.cyclicCLM D hD (x j) (μ j) F = 0
    rw [DirectSumSpectralModel.projectionCoordinate_spec]
    exact hz0
  exact (CyclicSpectralModel.cyclicIsometry D hD (x j) (μ j)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x j) (μ j) (hμ j))).injective heq

/-- If a vector's spectral measure is supported on `B`, while every cyclic
coordinate from `n` onward has base measure zero on `B`, all those tail
coordinates vanish. -/
theorem projectionCoordinate_eq_zero_of_tail
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (y : D.H) (ν : CircleMeasureData) (hν : HasSpectralMeasure D y ν)
    (B : Set Circle) (hνBc : ν.μ Bᶜ = 0) (n j : ℕ)
    (hμB : (μ n).μ B = 0) (hnj : n ≤ j) :
    DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y j = 0 := by
  let ρ := projectionDensityMeasure D hD x μ hμ y j
  have hμjB : (μ j).μ B = 0 := by
    have hac := OrderedSpectralDecomposition.component_dominates_later
      D hD x hord.2 hnj
    exact hac (μ n) (μ j) (hμ n) (hμ j) hμB
  have hρB : ρ.μ B = 0 :=
    projectionDensityMeasure_absolutelyContinuous D hD x μ hμ y j hμjB
  have hρBc : ρ.μ Bᶜ = 0 := by
    exact nonpos_iff_eq_zero.mp
      ((projectionDensityMeasure_le_spectralMeasure
        D hD x μ hμ hord.1 y ν hν j Bᶜ).trans_eq hνBc)
  have hρuniv : ρ.μ Set.univ = 0 := by
    apply le_antisymm
    · calc
        ρ.μ Set.univ = ρ.μ (B ∪ Bᶜ) := by congr 1; ext z; simp
        _ ≤ ρ.μ B + ρ.μ Bᶜ := measure_union_le _ _
        _ = 0 := by rw [hρB, hρBc, add_zero]
    · exact bot_le
  let z := SpectralDecomposition.cyclicProjectionFamily D x y j
  have hzspec : HasSpectralMeasure D z ρ :=
    projectionDensityMeasure_isSpectral D hD x μ hμ y j
  have hznorm : ‖z‖ ^ 2 = 0 := by
    have hm := MaximalSpectralType.spectralMeasure_univ D z ρ hzspec
    rw [hρuniv] at hm
    have hle := ENNReal.ofReal_eq_zero.mp hm.symm
    nlinarith [sq_nonneg ‖z‖]
  have hz0 : z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hznorm)
  let F := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y j
  have heq : CyclicSpectralModel.cyclicIsometry D hD (x j) (μ j)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x j) (μ j) (hμ j)) F =
      CyclicSpectralModel.cyclicIsometry D hD (x j) (μ j)
        (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x j) (μ j) (hμ j)) 0 := by
    rw [map_zero]
    change CyclicSpectralModel.cyclicCLM D hD (x j) (μ j) F = 0
    rw [DirectSumSpectralModel.projectionCoordinate_spec]
    exact hz0
  exact (CyclicSpectralModel.cyclicIsometry D hD (x j) (μ j)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x j) (μ j) (hμ j))).injective heq

theorem eq_finset_sum_projection_of_tail_coordinates_zero
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (y : D.H) (n : ℕ)
    (htail : ∀ j, n ≤ j →
      DirectSumSpectralModel.projectionCoordinate D hD x μ hμ y j = 0) :
    y = ∑ j ∈ Finset.range n,
      SpectralDecomposition.cyclicProjectionFamily D x y j := by
  let z : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D x y
  have hztail : ∀ j ∉ Finset.range n, z j = 0 := by
    intro j hj
    have hnj : n ≤ j := Nat.le_of_not_gt (by simpa using hj)
    have hspec := DirectSumSpectralModel.projectionCoordinate_spec
      D hD x μ hμ y j
    rw [htail j hnj, map_zero] at hspec
    exact hspec.symm
  have hsum := SpectralDecomposition.tsum_cyclicProjectionFamily_eq D x hdec y
  calc
    y = ∑' j, z j := hsum.symm
    _ = ∑ j ∈ Finset.range n, z j := tsum_eq_sum hztail

end Chapter02.DirectSumMeasureCoordinates
