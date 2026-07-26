import Chapter02.Spectral.OrderedMultiplicitySupports
import Chapter02.Spectral.DirectSumSpectralModel
import Chapter02.Spectral.CyclicOrthogonalSingularity

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.OrderedMultiplicityVectors

universe u

def stratumIndicator (μ : ℕ → CircleMeasureData) (n : ℕ) : Circle → ℂ :=
  (OrderedMultiplicitySupports.multiplicityStratum μ n).indicator (fun _ ↦ 1)

theorem stratumIndicator_memLp (μ : ℕ → CircleMeasureData) (n k : ℕ) :
    MemLp (stratumIndicator μ n) 2 (μ k).μ := by
  exact memLp_indicator_const 2
    (OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n) 1
    (Or.inr (measure_ne_top (μ k).μ _))

def stratumLp (μ : ℕ → CircleMeasureData) (n k : ℕ) : Lp ℂ 2 (μ k).μ :=
  (stratumIndicator_memLp μ n k).toLp (stratumIndicator μ n)

theorem stratumLp_coe (μ : ℕ → CircleMeasureData) (n k : ℕ) :
    (fun z ↦ stratumLp μ n k z) =ᵐ[(μ k).μ] stratumIndicator μ n :=
  (stratumIndicator_memLp μ n k).coeFn_toLp

noncomputable def canonicalStratumVector
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (n k : ℕ) : D.H :=
  let _hmom := SpectralMeasure.full_moment_of_hasSpectralMeasure
    D hD (x k) (μ k) (hμ k)
  CyclicSpectralModel.cyclicCLM D hD (x k) (μ k) (stratumLp μ n k)

noncomputable def activeVector
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (n k : ℕ) : D.H :=
  canonicalStratumVector D hD x μ hμ n k

theorem activeVector_mem_cyclic
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n)) (n k : ℕ) :
    InCyclicSubspace D (x k) (activeVector D hD x μ hμ n k) :=
  by
    rw [CyclicSpectralModel.inCyclicSubspace_iff_range D hD (x k)
      (activeVector D hD x μ hμ n k) (μ k)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x k) (μ k) (hμ k))]
    exact ⟨stratumLp μ n k, rfl⟩

theorem activeVector_hasSpectralMeasure
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n)) (n k : ℕ) :
    HasSpectralMeasure D (activeVector D hD x μ hμ n k)
      (OrderedMultiplicitySupports.restrictedComponentMeasure μ n k) := by
  intro r
  let B := OrderedMultiplicitySupports.multiplicityStratum μ n
  have hB : MeasurableSet B :=
    OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n
  have hm := CyclicMeasureType.vectorDensityMeasure_moment D hD (x k) (μ k)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD (x k) (μ k) (hμ k))
    (stratumLp μ n k) r
  change circleFourierCoefficient
      (OrderedMultiplicitySupports.restrictedComponentMeasure μ n k) r = _
  simp only [activeVector, canonicalStratumVector]
  rw [← hm]
  rw [circleFourierCoefficient, circleFourierCoefficient]
  change (∫ z, (z : ℂ) ^ (r : ℤ) ∂(μ k).μ.restrict B) =
    ∫ z, (z : ℂ) ^ (r : ℤ)
      ∂(μ k).μ.withDensity (CyclicMeasureType.spectralDensity (stratumLp μ n k))
  rw [← integral_indicator hB]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (CyclicMeasureType.spectralDensity_aemeasurable (stratumLp μ n k))
    (by simp [CyclicMeasureType.spectralDensity])]
  apply integral_congr_ae
  filter_upwards [stratumLp_coe μ n k] with z hz
  by_cases hzB : z ∈ B
  · simp [CyclicMeasureType.spectralDensity, stratumIndicator, B, hz, hzB]
  · simp [CyclicMeasureType.spectralDensity, stratumIndicator, B, hz, hzB]

def multiplicityVector
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (n k : ℕ) : D.H :=
  if IsActiveMultiplicityIndex n k then activeVector D hD x μ hμ n k else 0

def multiplicityMeasure (μ : ℕ → CircleMeasureData) (n k : ℕ) :
    CircleMeasureData :=
  OrderedMultiplicitySupports.restrictedComponentMeasure μ n k

theorem multiplicityVector_eq_zero_of_inactive
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (n k : ℕ) (hinactive : ¬ IsActiveMultiplicityIndex n k) :
    multiplicityVector D hD x μ hμ n k = 0 := by
  simp [multiplicityVector, hinactive]

theorem multiplicityVector_active_spec
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (n k : ℕ) (hactive : IsActiveMultiplicityIndex n k) :
    HasSpectralMeasure D (multiplicityVector D hD x μ hμ n k)
        (multiplicityMeasure μ n k) ∧
      (multiplicityMeasure μ n k).μ
        (OrderedMultiplicitySupports.multiplicityStratum μ n)ᶜ = 0 := by
  constructor
  · simpa [multiplicityVector, multiplicityMeasure, hactive] using
      activeVector_hasSpectralMeasure D hD x μ hμ n k
  · change (μ k).μ.restrict (OrderedMultiplicitySupports.multiplicityStratum μ n)
      (OrderedMultiplicitySupports.multiplicityStratum μ n)ᶜ = 0
    rw [Measure.restrict_apply
      (OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n).compl]
    rw [show (OrderedMultiplicitySupports.multiplicityStratum μ n)ᶜ ∩
        OrderedMultiplicitySupports.multiplicityStratum μ n = ∅ by ext z; simp]
    exact measure_empty

theorem spectralTypeDefinition_eq_of_mutual_ac
    (α β : CircleMeasureData) (hαβ : α.μ ≪ β.μ) (hβα : β.μ ≪ α.μ) :
    SpectralTypeDefinition α = SpectralTypeDefinition β := by
  ext γ
  constructor
  · intro h
    exact ⟨h.1.trans hαβ, hβα.trans h.2⟩
  · intro h
    exact ⟨h.1.trans hβα, hαβ.trans h.2⟩

theorem active_multiplicityMeasure_spectralType_eq
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    (n i j : ℕ) (hi : IsActiveMultiplicityIndex n i)
    (hj : IsActiveMultiplicityIndex n j) :
    SpectralTypeDefinition (multiplicityMeasure μ n i) =
      SpectralTypeDefinition (multiplicityMeasure μ n j) := by
  obtain ⟨hi0, h0i⟩ := OrderedMultiplicitySupports.active_restrictedMeasure_equivalent_base
    D hD x μ hμ hord n i hi
  obtain ⟨hj0, h0j⟩ := OrderedMultiplicitySupports.active_restrictedMeasure_equivalent_base
    D hD x μ hμ hord n j hj
  exact spectralTypeDefinition_eq_of_mutual_ac _ _ (hi0.trans h0j) (hj0.trans h0i)

theorem restrictedMeasures_mutuallySingular_of_strata_ne
    (μ : ℕ → CircleMeasureData) {n m i j : ℕ} (hnm : n ≠ m) :
    Measure.MutuallySingular (multiplicityMeasure μ n i).μ
      (multiplicityMeasure μ m j).μ := by
  let B := OrderedMultiplicitySupports.multiplicityStratum μ n
  let C := OrderedMultiplicitySupports.multiplicityStratum μ m
  have hdisj := OrderedMultiplicitySupports.multiplicityStrata_pairwise_disjoint μ n m hnm
  refine Measure.MutuallySingular.mk (s := Bᶜ) (t := B) ?_ ?_ ?_
  · change (μ i).μ.restrict B Bᶜ = 0
    rw [Measure.restrict_apply
      (OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n).compl]
    rw [show Bᶜ ∩ B = ∅ by ext z; simp]
    exact measure_empty
  · change (μ j).μ.restrict C B = 0
    rw [Measure.restrict_apply
      (OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n)]
    rw [show B ∩ C = ∅ by
      ext z
      constructor
      · intro hz
        exact (Set.disjoint_left.1 hdisj hz.1 hz.2).elim
      · simp]
    exact measure_empty
  · intro z
    simp

theorem active_multiplicityVectors_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    {n i m j : ℕ} (hne : (n, i) ≠ (m, j))
    (hni : IsActiveMultiplicityIndex n i)
    (hmj : IsActiveMultiplicityIndex m j) :
    OrthogonalCyclicSubspaces D
      (multiplicityVector D hD x μ hμ n i)
      (multiplicityVector D hD x μ hμ m j) := by
  simp only [multiplicityVector, if_pos hni, if_pos hmj]
  by_cases hij : i = j
  · subst j
    have hnm : n ≠ m := fun h ↦ hne (Prod.ext h rfl)
    exact SpectralRelations.singular_spectral_measures_orthogonal D hD _ _ _ _
      (activeVector_hasSpectralMeasure D hD x μ hμ n i)
      (activeVector_hasSpectralMeasure D hD x μ hμ m i)
      (restrictedMeasures_mutuallySingular_of_strata_ne μ hnm)
  · intro a b ha hb
    apply hdec.1 i j hij
    · intro K hK hxi
      exact ha K hK (activeVector_mem_cyclic D hD x μ hμ n i K hK hxi)
    · intro K hK hxj
      exact hb K hK (activeVector_mem_cyclic D hD x μ hμ m j K hK hxj)

/-- If a vector is orthogonal to the cyclic subspace generated by an active
multiplicity vector, then its coordinate in the original `k`-th cyclic model
vanishes on the corresponding multiplicity stratum. -/
theorem projectionCoordinate_zero_on_activeStratum
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (n k : ℕ) (hactive : IsActiveMultiplicityIndex n k)
    (r : D.H)
    (hr : r ∈ (SpectralDecomposition.cyclicSubmodule D
      (multiplicityVector D hD x μ hμ n k))ᗮ) :
    (OrderedMultiplicitySupports.multiplicityStratum μ n).indicator
        (fun z ↦ DirectSumSpectralModel.projectionCoordinate D hD x μ hμ r k z)
      =ᵐ[(μ k).μ] 0 := by
  let p := multiplicityVector D hD x μ hμ n k
  let K := SpectralDecomposition.cyclicSubmodule D (x k)
  let q := SpectralDecomposition.cyclicProjectionFamily D x r k
  let F := stratumLp μ n k
  let G := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ r k
  have hpK : p ∈ K := by
    simp only [p, multiplicityVector, if_pos hactive]
    exact activeVector_mem_cyclic D hD x μ hμ n k
  have hqOrth : q ∈ (SpectralDecomposition.cyclicSubmodule D p)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro b hb
    have hbK : b ∈ K :=
      hb K (SpectralDecomposition.cyclicSubmodule_reducing D (x k)) hpK
    have hbr : @inner ℂ D.H _ b r = 0 := by
      rw [Submodule.mem_orthogonal] at hr
      exact hr b hb
    calc
      @inner ℂ D.H _ b q =
          @inner ℂ D.H _ (K.starProjection b) r := by
            exact (K.inner_starProjection_left_eq_right b r).symm
      _ = @inner ℂ D.H _ b r := by
            rw [K.starProjection_eq_self_iff.mpr hbK]
      _ = 0 := hbr
  have hpOrthq : OrthogonalCyclicSubspaces D p q :=
    SpectralRelations.cyclic_subspaces_orthogonal_of_mem D
      (SpectralDecomposition.cyclicSubmodule D p) p q
      (SpectralDecomposition.cyclicSubmodule_reducing D p)
      (SpectralRelations.orthogonal_reducing D hD
        (SpectralDecomposition.cyclicSubmodule D p)
        (SpectralDecomposition.cyclicSubmodule_reducing D p))
      (SpectralDecomposition.generator_mem_cyclicSubmodule D p) hqOrth
  have himage : OrthogonalCyclicSubspaces D
      (CyclicSpectralModel.cyclicCLM D hD (x k) (μ k) F)
      (CyclicSpectralModel.cyclicCLM D hD (x k) (μ k) G) := by
    simpa only [F, G, p, q, multiplicityVector, if_pos hactive,
      activeVector, canonicalStratumVector,
      DirectSumSpectralModel.projectionCoordinate_spec] using hpOrthq
  have hcross := CyclicOrthogonalSingularity.crossDensity_ae_zero_of_orthogonal_images
    D hD (x k) (μ k)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure
      D hD (x k) (μ k) (hμ k)) F G himage
  filter_upwards [hcross, stratumLp_coe μ n k] with z hzCross hzF
  by_cases hzB : z ∈ OrderedMultiplicitySupports.multiplicityStratum μ n
  · simpa [F, stratumIndicator, hzF, hzB] using hzCross
  · simp [hzB]

end Chapter02.OrderedMultiplicityVectors
