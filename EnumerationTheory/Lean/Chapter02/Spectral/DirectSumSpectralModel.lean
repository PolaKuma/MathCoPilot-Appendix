import Chapter02.Spectral.SpectralDecomposition

open Classical MeasureTheory Filter Set
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.DirectSumSpectralModel

universe u

def componentVector (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (f : ℕ → Circle → ℂ) (n : ℕ) : D.H :=
  CyclicSpectralModel.rawW D hD (x n) (μ n)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
    (f n)

def directSumW (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (f : ℕ → Circle → ℂ) : D.H :=
  ∑' n, componentVector D hD x μ hμ f n

theorem componentVector_ae (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    {f g : ℕ → Circle → ℂ} (hfg : ∀ n, f n =ᵐ[(μ n).μ] g n) (n : ℕ) :
    componentVector D hD x μ hμ f n = componentVector D hD x μ hμ g n := by
  exact CyclicSpectralModel.rawW_ae D hD (x n) (μ n)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
    (hfg n)

theorem directSumW_ae (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    {f g : ℕ → Circle → ℂ} (hfg : ∀ n, f n =ᵐ[(μ n).μ] g n) :
    directSumW D hD x μ hμ f = directSumW D hD x μ hμ g := by
  unfold directSumW
  congr 1
  funext n
  exact componentVector_ae D hD x μ hμ hfg n

theorem componentVector_norm (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (f : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f) (n : ℕ) :
    ‖componentVector D hD x μ hμ f n‖ =
      (eLpNorm (f n) 2 (μ n).μ).toReal := by
  exact CyclicSpectralModel.rawW_norm D hD (x n) (μ n)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
    (f n) (hf.1 n)

theorem componentVector_mem_cyclic (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (f : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f) (n : ℕ) :
    InCyclicSubspace D (x n) (componentVector D hD x μ hμ f n) := by
  let hmom := SpectralMeasure.full_moment_of_hasSpectralMeasure
    D hD (x n) (μ n) (hμ n)
  rw [CyclicSpectralModel.inCyclicSubspace_iff_range D hD (x n)
    (componentVector D hD x μ hμ f n) (μ n) hmom]
  refine ⟨(hf.1 n).toLp (f n), ?_⟩
  simpa [componentVector] using
    (CyclicSpectralModel.rawW_toLp D hD (x n) (μ n) hmom
      (f n) (hf.1 n)).symm

theorem componentVector_pairwise_orthogonal (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (f : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f) :
    SpectralDecomposition.PairwiseOrthogonalVectors
      (componentVector D hD x μ hμ f) := by
  intro i j hij
  exact horth i j hij _ _
    (componentVector_mem_cyclic D hD x μ hμ f hf i)
    (componentVector_mem_cyclic D hD x μ hμ f hf j)

theorem componentVector_summable (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (f : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f) :
    Summable (componentVector D hD x μ hμ f) := by
  apply SpectralDecomposition.summable_of_pairwise_orthogonal_of_summable_norm_sq
    (componentVector D hD x μ hμ f)
    (componentVector_pairwise_orthogonal D hD x μ hμ horth f hf)
  simpa only [componentVector_norm D hD x μ hμ f hf] using hf.2

theorem directSumW_norm_sq (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (f : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f) :
    ‖directSumW D hD x μ hμ f‖ ^ 2 =
      ∑' n, (eLpNorm (f n) 2 (μ n).μ).toReal ^ 2 := by
  unfold directSumW
  rw [SpectralDecomposition.norm_tsum_sq_of_pairwise_orthogonal
    (componentVector D hD x μ hμ f)
    (componentVector_pairwise_orthogonal D hD x μ hμ horth f hf)]
  · congr 1
    funext n
    rw [componentVector_norm D hD x μ hμ f hf n]
  · simpa only [componentVector_norm D hD x μ hμ f hf] using hf.2

theorem directSumW_add (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (f g : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f)
    (hg : InCircleL2DirectSum μ g) :
    directSumW D hD x μ hμ (fun n z ↦ f n z + g n z) =
      directSumW D hD x μ hμ f + directSumW D hD x μ hμ g := by
  let vf := componentVector D hD x μ hμ f
  let vg := componentVector D hD x μ hμ g
  have hvf : Summable vf := componentVector_summable D hD x μ hμ horth f hf
  have hvg : Summable vg := componentVector_summable D hD x μ hμ horth g hg
  have hcomp : componentVector D hD x μ hμ (fun n z ↦ f n z + g n z) =
      fun n ↦ vf n + vg n := by
    funext n
    exact CyclicSpectralModel.rawW_add D hD (x n) (μ n)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
      (f n) (g n)
  unfold directSumW
  rw [hcomp]
  exact hvf.tsum_add hvg

theorem directSumW_smul (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (c : ℂ) (f : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f) :
    directSumW D hD x μ hμ (fun n z ↦ c * f n z) =
      c • directSumW D hD x μ hμ f := by
  let vf := componentVector D hD x μ hμ f
  have hvf : Summable vf := componentVector_summable D hD x μ hμ horth f hf
  have hcomp : componentVector D hD x μ hμ (fun n z ↦ c * f n z) =
      fun n ↦ c • vf n := by
    funext n
    exact CyclicSpectralModel.rawW_smul D hD (x n) (μ n)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
      c (f n)
  unfold directSumW
  rw [hcomp]
  exact hvf.tsum_const_smul c

theorem directSumW_intertwines (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (f : ℕ → Circle → ℂ) (hf : InCircleL2DirectSum μ f) :
    directSumW D hD x μ hμ (fun n z ↦ (z : ℂ) * f n z) =
      D.U (directSumW D hD x μ hμ f) := by
  let vf := componentVector D hD x μ hμ f
  have hvf : Summable vf := componentVector_summable D hD x μ hμ horth f hf
  have hcomp : componentVector D hD x μ hμ
      (fun n z ↦ (z : ℂ) * f n z) = fun n ↦ D.U (vf n) := by
    funext n
    exact CyclicSpectralModel.rawW_intertwines D hD (x n) (μ n)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x n) (μ n) (hμ n))
      (f n) (hf.1 n)
  unfold directSumW
  rw [hcomp]
  exact (D.U.map_tsum hvf).symm

theorem directSumW_basis (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n)) (n : ℕ) :
    directSumW D hD x μ hμ
      (fun j _ ↦ if j = n then (1 : ℂ) else 0) = x n := by
  unfold directSumW
  rw [tsum_eq_single n]
  · simpa [componentVector] using
      (CyclicSpectralModel.rawW_one D hD (x n) (μ n)
        (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
          (x n) (μ n) (hμ n)))
  · intro j hj
    simpa [componentVector, hj] using
      (CyclicSpectralModel.rawW_smul D hD (x j) (μ j)
        (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
          (x j) (μ j) (hμ j)) 0 (fun _ ↦ (1 : ℂ)))

noncomputable def projectionCoordinate (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (y : D.H) (n : ℕ) : Lp ℂ 2 (μ n).μ :=
  Classical.choose ((CyclicSpectralModel.inCyclicSubspace_iff_range D hD
    (x n) (SpectralDecomposition.cyclicProjectionFamily D x y n) (μ n)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
      (x n) (μ n) (hμ n))).mp
    (SpectralDecomposition.cyclicProjectionFamily_mem D x y n))

theorem projectionCoordinate_spec (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (y : D.H) (n : ℕ) :
    CyclicSpectralModel.cyclicCLM D hD (x n) (μ n)
      (projectionCoordinate D hD x μ hμ y n) =
        SpectralDecomposition.cyclicProjectionFamily D x y n :=
  Classical.choose_spec ((CyclicSpectralModel.inCyclicSubspace_iff_range D hD
    (x n) (SpectralDecomposition.cyclicProjectionFamily D x y n) (μ n)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
      (x n) (μ n) (hμ n))).mp
    (SpectralDecomposition.cyclicProjectionFamily_mem D x y n))

def projectionRawFunction (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (y : D.H) : ℕ → Circle → ℂ :=
  fun n z ↦ projectionCoordinate D hD x μ hμ y n z

theorem projectionRawFunction_mem (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (x i) (x j))
    (y : D.H) : InCircleL2DirectSum μ
      (projectionRawFunction D hD x μ hμ y) := by
  constructor
  · intro n
    exact Lp.memLp (projectionCoordinate D hD x μ hμ y n)
  · have hs := SpectralDecomposition.cyclicProjectionFamily_norm_sq_summable
      D x horth y
    convert hs using 1
    funext n
    change (eLpNorm (fun z ↦ projectionCoordinate D hD x μ hμ y n z)
      2 (μ n).μ).toReal ^ 2 = _
    rw [← MeasureTheory.Lp.norm_def]
    rw [← CyclicSpectralModel.cyclicCLM_norm D hD (x n) (μ n)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
        (x n) (μ n) (hμ n))]
    rw [projectionCoordinate_spec]

theorem componentVector_projectionRawFunction (D : HilbertOperatorData.{u})
    (hD : IsUnitary D) (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (y : D.H) (n : ℕ) :
    componentVector D hD x μ hμ (projectionRawFunction D hD x μ hμ y) n =
      SpectralDecomposition.cyclicProjectionFamily D x y n := by
  let F := projectionCoordinate D hD x μ hμ y n
  let hmom := SpectralMeasure.full_moment_of_hasSpectralMeasure
    D hD (x n) (μ n) (hμ n)
  have hraw := CyclicSpectralModel.rawW_toLp D hD (x n) (μ n) hmom
    (fun z ↦ F z) (Lp.memLp F)
  have htoLp : (Lp.memLp F).toLp (fun z ↦ F z) = F := by
    apply Lp.ext
    filter_upwards [(Lp.memLp F).coeFn_toLp] with z hz
    exact hz
  rw [htoLp] at hraw
  exact hraw.trans (projectionCoordinate_spec D hD x μ hμ y n)

theorem directSumW_surjective_of_decomposition
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x) :
    ∀ y : D.H, ∃ f : ℕ → Circle → ℂ,
      InCircleL2DirectSum μ f ∧ directSumW D hD x μ hμ f = y := by
  intro y
  refine ⟨projectionRawFunction D hD x μ hμ y,
    projectionRawFunction_mem D hD x μ hμ hdec.1 y, ?_⟩
  unfold directSumW
  have hfun : componentVector D hD x μ hμ
      (projectionRawFunction D hD x μ hμ y) =
      SpectralDecomposition.cyclicProjectionFamily D x y := by
    funext n
    exact componentVector_projectionRawFunction D hD x μ hμ y n
  rw [hfun]
  exact SpectralDecomposition.tsum_cyclicProjectionFamily_eq D x hdec y

theorem directSumModel_of_orthogonal_decomposition
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x) :
    IsDirectSumMultiplicationModel D μ (directSumW D hD x μ hμ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hfg
    exact directSumW_ae D hD x μ hμ hfg
  · intro f g hf hg
    exact directSumW_add D hD x μ hμ hdec.1 f g hf hg
  · intro c f hf
    exact directSumW_smul D hD x μ hμ hdec.1 c f hf
  · intro f hf
    exact directSumW_norm_sq D hD x μ hμ hdec.1 f hf
  · exact directSumW_surjective_of_decomposition D hD x μ hμ hdec
  · intro f hf
    exact directSumW_intertwines D hD x μ hμ hdec.1 f hf

/-- An ordered cyclic spectral decomposition yields the concrete direct-sum
multiplication model. -/
theorem directSumStatement_of_spectralDecompositionFormOne
    (D : HilbertOperatorData.{u})
    (hform : SpectralDecompositionFormOne D) :
    DirectSumOfCyclicMultiplicationModelsStatement D := by
  intro hsep hD
  obtain ⟨x, hxord, _huniq⟩ := hform hsep hD
  choose μ hμ _hμuniq using fun n ↦ SpectralMeasure.spectralMeasure D hD (x n)
  let W := directSumW D hD x μ hμ
  refine ⟨x, μ, W, hxord, hμ, ?_, ?_⟩
  · exact directSumModel_of_orthogonal_decomposition D hD x μ hμ hxord.1
  · intro n
    exact directSumW_basis D hD x μ hμ n

end Chapter02.DirectSumSpectralModel
