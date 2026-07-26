import Chapter02.Spectral.DirectSumMeasureCoordinates

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.FiniteDirectSumOrthogonality

universe u

noncomputable def transferredProjectionCoordinate
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (p : D.H) (n : ℕ) (j : Fin n) : Lp ℂ 2 (μ 0).μ :=
  RadonNikodymTransfer.transfer (μ 0) (μ j)
    (OrderedSpectralDecomposition.component_dominates_later D hD x hord.2
      (Nat.zero_le j) (μ 0) (μ j) (hμ 0) (hμ j))
    (DirectSumSpectralModel.projectionCoordinate D hD x μ hμ p j)

theorem transferredProjectionCoordinate_cross_integrable
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (p q : D.H) (n : ℕ) (i : Fin n) (m : ℤ) :
    Integrable (fun z : Circle ↦ (z : ℂ) ^ m *
      (star (transferredProjectionCoordinate D hD x μ hμ hord p n i z) *
        transferredProjectionCoordinate D hD x μ hμ hord q n i z)) (μ 0).μ := by
  let F := transferredProjectionCoordinate D hD x μ hμ hord p n i
  let G := transferredProjectionCoordinate D hD x μ hμ hord q n i
  have hcross : Integrable (fun z ↦ star (F z) * G z) (μ 0).μ :=
    ((Lp.memLp F).congr_norm (Lp.memLp F).1.star
      (Filter.Eventually.of_forall fun z ↦ (norm_star (F z)).symm)).integrable_mul
      (Lp.memLp G)
  let c : C(Circle, ℂ) :=
    ⟨fun z ↦ (z : ℂ) ^ m,
      (Continuous.zpow₀ (by fun_prop) m
        (fun z ↦ Or.inl (Circle.coe_ne_zero z)))⟩
  exact hcross.bdd_mul c.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ c.norm_coe_le_norm z)

/-- For vectors with no coordinates from `n` onward, the Laurent moments of
the pointwise finite-coordinate pairing equal the Hilbert-space correlations. -/
theorem integral_finiteDot_transferred_eq_inner
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (p q : D.H) (n : ℕ)
    (htailp : ∀ j, n ≤ j →
      DirectSumSpectralModel.projectionCoordinate D hD x μ hμ p j = 0)
    (htailq : ∀ j, n ≤ j →
      DirectSumSpectralModel.projectionCoordinate D hD x μ hμ q j = 0)
    (m : ℤ) :
    (∫ z, (z : ℂ) ^ m * FiniteSpectralRank.finiteDot
      (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord p n j z)
      (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord q n j z)
      ∂(μ 0).μ) =
      @inner ℂ D.H _
        (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) p) q := by
  let zp : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D x p
  let zq : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D x q
  have hp : p = ∑ j ∈ Finset.range n, zp j :=
    DirectSumMeasureCoordinates.eq_finset_sum_projection_of_tail_coordinates_zero
      D hD x μ hμ hord.1 p n htailp
  have hq : q = ∑ j ∈ Finset.range n, zq j :=
    DirectSumMeasureCoordinates.eq_finset_sum_projection_of_tail_coordinates_zero
      D hD x μ hμ hord.1 q n htailq
  have hpFin : p = ∑ j : Fin n, zp j := by
    rw [hp]
    calc
      (∑ j ∈ Finset.range n, zp j) =
          ∑ j ∈ Finset.range n, if h : j < n then zp (⟨j, h⟩ : Fin n) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [dif_pos (Finset.mem_range.mp hj)]
      _ = ∑ j : Fin n, zp j :=
        (Finset.sum_fin_eq_sum_range (fun j : Fin n ↦ zp j)).symm
  have hqFin : q = ∑ j : Fin n, zq j := by
    rw [hq]
    calc
      (∑ j ∈ Finset.range n, zq j) =
          ∑ j ∈ Finset.range n, if h : j < n then zq (⟨j, h⟩ : Fin n) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [dif_pos (Finset.mem_range.mp hj)]
      _ = ∑ j : Fin n, zq j :=
        (Finset.sum_fin_eq_sum_range (fun j : Fin n ↦ zq j)).symm
  have hfun : (fun z : Circle ↦ (z : ℂ) ^ m * FiniteSpectralRank.finiteDot
      (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord p n j z)
      (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord q n j z)) =
      fun z : Circle ↦ ∑ j : Fin n, (z : ℂ) ^ m *
        (star (transferredProjectionCoordinate D hD x μ hμ hord p n j z) *
          transferredProjectionCoordinate D hD x μ hμ hord q n j z) := by
    funext z
    rw [FiniteSpectralRank.finiteDot, Finset.mul_sum]
  rw [hfun, integral_finset_sum]
  · calc
      (∑ j : Fin n, ∫ z, (z : ℂ) ^ m *
          (star (transferredProjectionCoordinate D hD x μ hμ hord p n j z) *
            transferredProjectionCoordinate D hD x μ hμ hord q n j z) ∂(μ 0).μ) =
          ∑ j : Fin n, @inner ℂ D.H _
            (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) (zp j)) (zq j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        let hac : (μ j).μ ≪ (μ 0).μ :=
          OrderedSpectralDecomposition.component_dominates_later D hD x hord.2
            (Nat.zero_le j) (μ 0) (μ j) (hμ 0) (hμ j)
        let F := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ p j
        let G := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ q j
        change (∫ z, (z : ℂ) ^ m *
          (star (RadonNikodymTransfer.transfer (μ 0) (μ j) hac F z) *
            RadonNikodymTransfer.transfer (μ 0) (μ j) hac G z) ∂(μ 0).μ) = _
        rw [RadonNikodymTransfer.integral_transfer_cross (μ 0) (μ j) hac
          (fun z ↦ (z : ℂ) ^ m) F G]
        rw [CyclicOrthogonalSingularity.integral_zpow_cross_eq_inner
          D hD (x j) (μ j)
          (SpectralMeasure.full_moment_of_hasSpectralMeasure D hD
            (x j) (μ j) (hμ j))]
        rw [DirectSumSpectralModel.projectionCoordinate_spec,
          DirectSumSpectralModel.projectionCoordinate_spec]
      _ = @inner ℂ D.H _
          (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) p) q := by
        rw [hpFin, hqFin, map_sum, sum_inner]
        apply Finset.sum_congr rfl
        intro j hj
        change @inner ℂ D.H _
            (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) (zp j)) (zq j) =
          @inner ℂ D.H _
            (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) (zp j))
            (∑ k : Fin n, zq k)
        rw [inner_sum]
        rw [Finset.sum_eq_single j]
        · intro k hk hkj
          have hjk : (j : ℕ) ≠ (k : ℕ) := fun hv ↦ hkj (Fin.ext hv.symm)
          apply hord.1.1 j k hjk
          · intro K hK hxj
            have hzpj : zp j ∈ K :=
              (SpectralDecomposition.cyclicProjectionFamily_mem D x p j) K hK hxj
            exact CyclicSpectralModel.zpow_orbit_mem_reducing
              D hD (zp j) K hK hzpj (-m)
          · exact SpectralDecomposition.cyclicProjectionFamily_mem D x q k
        · intro hnot
          exact (hnot hj).elim
  · intro j hj
    exact transferredProjectionCoordinate_cross_integrable
      D hD x μ hμ hord p q n j m

/-- Orthogonality of two finitely supported vectors becomes pointwise
orthogonality of their transferred finite-coordinate fields. -/
theorem finiteDot_transferred_ae_zero_of_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (p q : D.H) (n : ℕ)
    (htailp : ∀ j, n ≤ j →
      DirectSumSpectralModel.projectionCoordinate D hD x μ hμ p j = 0)
    (htailq : ∀ j, n ≤ j →
      DirectSumSpectralModel.projectionCoordinate D hD x μ hμ q j = 0)
    (horth : OrthogonalCyclicSubspaces D p q) :
    (fun z ↦ FiniteSpectralRank.finiteDot
      (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord p n j z)
      (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord q n j z))
      =ᵐ[(μ 0).μ] 0 := by
  let f : Circle → ℂ := fun z ↦ FiniteSpectralRank.finiteDot
    (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord p n j z)
    (fun j : Fin n ↦ transferredProjectionCoordinate D hD x μ hμ hord q n j z)
  have hf : Integrable f (μ 0).μ := by
    have hterm : ∀ j : Fin n, Integrable (fun z ↦
        star (transferredProjectionCoordinate D hD x μ hμ hord p n j z) *
          transferredProjectionCoordinate D hD x μ hμ hord q n j z) (μ 0).μ := by
      intro j
      simpa using transferredProjectionCoordinate_cross_integrable
        D hD x μ hμ hord p q n j 0
    have hsum : Integrable (fun z ↦ ∑ j : Fin n,
        star (transferredProjectionCoordinate D hD x μ hμ hord p n j z) *
          transferredProjectionCoordinate D hD x μ hμ hord q n j z) (μ 0).μ :=
      integrable_finset_sum Finset.univ fun j _ ↦ hterm j
    exact hsum.congr (Filter.Eventually.of_forall fun z ↦ by
      simp [f, FiniteSpectralRank.finiteDot])
  have hchar (m : ℤ) :
      ∫ z, (z : ℂ) ^ m * f z ∂(μ 0).μ = 0 := by
    rw [show (∫ z, (z : ℂ) ^ m * f z ∂(μ 0).μ) =
        @inner ℂ D.H _ (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) p) q by
      exact integral_finiteDot_transferred_eq_inner
        D hD x μ hμ hord p q n htailp htailq m]
    apply horth
    · intro K hK hpK
      exact CyclicSpectralModel.zpow_orbit_mem_reducing D hD p K hK hpK (-m)
    · exact SpectralRelations.self_mem_cyclic D q
  have hmom : ∀ r : C(Circle, ℂ), r ∈ CircleLaurent.span →
      ∫ z, r z * f z ∂(μ 0).μ = 0 := by
    intro r hr
    refine Submodule.span_induction (p := fun r _ ↦
      ∫ z, r z * f z ∂(μ 0).μ = 0) ?_ ?_ ?_ ?_ hr
    · rintro r ⟨m, rfl⟩
      exact hchar m
    · simp
    · intro r s hr hs hir his
      have hirInt : Integrable (fun z ↦ r z * f z) (μ 0).μ :=
        hf.bdd_mul r.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z ↦ r.norm_coe_le_norm z)
      have hisInt : Integrable (fun z ↦ s z * f z) (μ 0).μ :=
        hf.bdd_mul s.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z ↦ s.norm_coe_le_norm z)
      simp only [ContinuousMap.add_apply, add_mul]
      rw [integral_add hirInt hisInt, hir, his, add_zero]
    · intro c r hr hir
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, hir, mul_zero]
  exact CircleFourierUniqueness.complex_ae_zero_of_laurent_moments (μ 0) hf hmom

/-- `n` ordered cyclic coordinates cannot contain `n+1` pairwise orthogonal
vectors carrying the same nonzero spectral measure. -/
theorem no_overfull_common_spectral_measure
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (n : ℕ) (p : Fin (n + 1) → D.H) (ν : CircleMeasureData)
    (hν : ∀ i, HasSpectralMeasure D (p i) ν)
    (hνnonzero : ν.μ Set.univ ≠ 0)
    (B : Set Circle) (hνBc : ν.μ Bᶜ = 0) (hμnB : (μ n).μ B = 0)
    (horth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (p i) (p j)) :
    False := by
  have htail (i : Fin (n + 1)) : ∀ j, n ≤ j →
      DirectSumSpectralModel.projectionCoordinate D hD x μ hμ (p i) j = 0 :=
    fun j hnj ↦ DirectSumMeasureCoordinates.projectionCoordinate_eq_zero_of_tail
      D hD x μ hμ hord (p i) ν (hν i) B hνBc n j hμnB hnj
  let V : Fin (n + 1) → Circle → Fin n → ℂ := fun i z j ↦
    transferredProjectionCoordinate D hD x μ hμ hord (p i) n j z
  have hVorth : ∀ i j, i ≠ j →
      ∀ᵐ z ∂(μ 0).μ, FiniteSpectralRank.finiteDot (V i z) (V j z) = 0 := by
    intro i j hij
    exact finiteDot_transferred_ae_zero_of_orthogonal
      D hD x μ hμ hord (p i) (p j) n (htail i) (htail j) (horth i j hij)
  have hrank : ∀ᵐ z ∂(μ 0).μ, ∃ i, V i z = 0 :=
    FiniteSpectralRank.ae_exists_zero_of_pairwise_finiteDot_zero
      (μ 0).μ n V hVorth
  have hνac : ν.μ ≪ (μ 0).μ :=
    OrderedSpectralDecomposition.firstVector_dominates_every_vector
      D hD x hord (p 0) (μ 0) ν (hμ 0) (hν 0)
  have hrankν : ∀ᵐ z ∂ν.μ, ∃ i, V i z = 0 := hνac.ae_le hrank
  let E : Fin (n + 1) → Set Circle := fun i ↦
    ⋂ j : Fin n, {z | V i z j = 0}
  have hEmeas (i : Fin (n + 1)) : MeasurableSet (E i) := by
    apply MeasurableSet.iInter
    intro j
    exact (Lp.stronglyMeasurable
      (transferredProjectionCoordinate D hD x μ hμ hord (p i) n j)).measurable
        (measurableSet_singleton (0 : ℂ))
  have hEzero (i : Fin (n + 1)) : ν.μ (E i) = 0 := by
    have hsum := DirectSumMeasureCoordinates.spectralMeasure_eq_sum_projectionDensityMeasure
      D hD x μ hμ hord.1 (p i) ν (hν i)
    rw [hsum, Measure.sum_apply _ (hEmeas i)]
    apply ENNReal.tsum_eq_zero.mpr
    intro j
    by_cases hj : j < n
    · let jf : Fin n := ⟨j, hj⟩
      let F := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ (p i) j
      let hac : (μ j).μ ≪ (μ 0).μ :=
        OrderedSpectralDecomposition.component_dominates_later D hD x hord.2
          (Nat.zero_le j) (μ 0) (μ j) (hμ 0) (hμ j)
      have hdensity : DirectSumMeasureCoordinates.projectionDensityMeasure
          D hD x μ hμ (p i) j =
          CyclicMeasureType.vectorDensityMeasure
            (transferredProjectionCoordinate D hD x μ hμ hord (p i) n jf) := by
        change CyclicMeasureType.vectorDensityMeasure F =
          CyclicMeasureType.vectorDensityMeasure
            (RadonNikodymTransfer.transfer (μ 0) (μ j) hac F)
        exact (RadonNikodymTransfer.vectorDensityMeasure_transfer
          (μ 0) (μ j) hac F).symm
      rw [hdensity]
      apply (withDensity_apply_eq_zero'
        (CyclicMeasureType.spectralDensity_aemeasurable _)).2
      have hempty : {z | CyclicMeasureType.spectralDensity
          (transferredProjectionCoordinate D hD x μ hμ hord (p i) n jf) z ≠ 0} ∩
          E i = ∅ := by
        ext z
        constructor
        · intro hz
          have hzcoord : V i z jf = 0 := by
            have hall := Set.mem_iInter.mp hz.2 jf
            exact hall
          exfalso
          apply hz.1
          simp [CyclicMeasureType.spectralDensity, V, hzcoord]
        · simp
      rw [hempty, measure_empty]
    · have hnj : n ≤ j := Nat.le_of_not_gt hj
      apply nonpos_iff_eq_zero.mp
      calc
        (DirectSumMeasureCoordinates.projectionDensityMeasure
            D hD x μ hμ (p i) j).μ (E i) ≤
            (DirectSumMeasureCoordinates.projectionDensityMeasure
              D hD x μ hμ (p i) j).μ Set.univ := measure_mono (Set.subset_univ _)
        _ = ENNReal.ofReal
            (‖SpectralDecomposition.cyclicProjectionFamily D x (p i) j‖ ^ 2) :=
          MaximalSpectralType.spectralMeasure_univ D _ _
            (DirectSumMeasureCoordinates.projectionDensityMeasure_isSpectral
              D hD x μ hμ (p i) j)
        _ = 0 := by
          have hs := DirectSumSpectralModel.projectionCoordinate_spec
            D hD x μ hμ (p i) j
          rw [htail i j hnj, map_zero] at hs
          rw [← hs]
          simp
  let U : Set Circle := ⋃ i, E i
  have hUzero : ν.μ U = 0 := measure_iUnion_null hEzero
  have hmemU : ∀ᵐ z ∂ν.μ, z ∈ U := by
    filter_upwards [hrankν] with z hz
    obtain ⟨i, hi⟩ := hz
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iInter.mpr fun j ↦ congrFun hi j⟩
  have hUfull : ν.μ U = ν.μ Set.univ := by
    apply measure_congr
    filter_upwards [hmemU] with z hz
    change (z ∈ U) = (z ∈ Set.univ)
    simp [hz]
  exact hνnonzero (hUfull.symm.trans hUzero)

end Chapter02.FiniteDirectSumOrthogonality
