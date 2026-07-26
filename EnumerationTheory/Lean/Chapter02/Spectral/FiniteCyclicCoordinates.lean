import Chapter02.Spectral.FiniteDirectSumOrthogonality
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.FiniteCyclicCoordinates

universe u

theorem finsetSumMeasure_apply
    {α ι : Type*} [MeasurableSpace α]
    (ρ : ι → Measure α) (s : Finset ι) (A : Set α) :
    (∑ i ∈ s, ρ i) A = ∑ i ∈ s, ρ i A := by simp

theorem integrable_finsetSumMeasure
    {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (f : α → E) (ρ : ι → Measure α) (s : Finset ι)
    (hf : ∀ i ∈ s, Integrable f (ρ i)) : Integrable f (∑ i ∈ s, ρ i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, integrable_add_measure]
      exact ⟨hf i (Finset.mem_insert_self i s),
        ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))⟩

theorem integral_finsetSumMeasure
    {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (f : α → E) (ρ : ι → Measure α) (s : Finset ι)
    (hf : ∀ i ∈ s, Integrable f (ρ i)) :
    (∫ x, f x ∂(∑ i ∈ s, ρ i)) = ∑ i ∈ s, ∫ x, f x ∂ρ i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        integral_add_measure (hf i (Finset.mem_insert_self i s))
          (integrable_finsetSumMeasure f ρ s
            (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

theorem iterate_fintype_sum
    (D : HilbertOperatorData.{u}) {ι : Type*} [Fintype ι]
    (z : ι → D.H) (r : ℕ) :
    (D.U^[r]) (∑ i, z i) = ∑ i, (D.U^[r]) (z i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      simp [Function.iterate_succ_apply', ih, map_sum]

def componentVector
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    {n : ℕ} (a : Fin n → D.H) (μ : Fin n → CircleMeasureData)
    (F : ∀ j, Lp ℂ 2 (μ j).μ) (j : Fin n) : D.H :=
  CyclicSpectralModel.cyclicCLM D hD (a j) (μ j) (F j)

def coordinateMeasure
    {n : ℕ} (μ : Fin n → CircleMeasureData)
    (F : ∀ j, Lp ℂ 2 (μ j).μ) : CircleMeasureData where
  μ := ∑ j, (CyclicMeasureType.vectorDensityMeasure (F j)).μ
  isFinite := by
    refine ⟨?_⟩
    rw [finsetSumMeasure_apply _ Finset.univ Set.univ]
    exact ENNReal.sum_lt_top.mpr fun j _ ↦ measure_lt_top _ _

theorem componentVector_mem_cyclic
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    {n : ℕ} (a : Fin n → D.H) (μ : Fin n → CircleMeasureData)
    (hμ : ∀ j, HasSpectralMeasure D (a j) (μ j))
    (F : ∀ j, Lp ℂ 2 (μ j).μ) (j : Fin n) :
    InCyclicSubspace D (a j) (componentVector D hD a μ F j) := by
  rw [CyclicSpectralModel.inCyclicSubspace_iff_range D hD (a j)
    (componentVector D hD a μ F j) (μ j)
    (SpectralMeasure.full_moment_of_hasSpectralMeasure
      D hD (a j) (μ j) (hμ j))]
  exact ⟨F j, rfl⟩

theorem componentVectors_pairwise_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    {n : ℕ} (a : Fin n → D.H) (μ : Fin n → CircleMeasureData)
    (hμ : ∀ j, HasSpectralMeasure D (a j) (μ j))
    (haorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (a i) (a j))
    (F : ∀ j, Lp ℂ 2 (μ j).μ) :
    ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D
      (componentVector D hD a μ F i)
      (componentVector D hD a μ F j) := by
  intro i j hij b c hb hc
  exact haorth i j hij b c
    (hb _ (SpectralDecomposition.cyclicSubmodule_reducing D (a i))
      (componentVector_mem_cyclic D hD a μ hμ F i))
    (hc _ (SpectralDecomposition.cyclicSubmodule_reducing D (a j))
      (componentVector_mem_cyclic D hD a μ hμ F j))

theorem coordinateMeasure_isSpectral
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    {n : ℕ} (a : Fin n → D.H) (μ : Fin n → CircleMeasureData)
    (hμ : ∀ j, HasSpectralMeasure D (a j) (μ j))
    (haorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (a i) (a j))
    (F : ∀ j, Lp ℂ 2 (μ j).μ) :
    HasSpectralMeasure D (∑ j, componentVector D hD a μ F j)
      (coordinateMeasure μ F) := by
  intro r
  rw [circleFourierCoefficient]
  change (∫ z, (z : ℂ) ^ (r : ℤ)
      ∂(∑ j, (CyclicMeasureType.vectorDensityMeasure (F j)).μ)) = _
  rw [integral_finsetSumMeasure]
  · change (∑ j, circleFourierCoefficient
        (CyclicMeasureType.vectorDensityMeasure (F j)) r) = _
    apply Eq.symm
    rw [iterate_fintype_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum, Finset.sum_eq_single i]
    · simpa [componentVector] using
        (CyclicMeasureType.vectorDensityMeasure_moment D hD
          (a i) (μ i)
          (SpectralMeasure.full_moment_of_hasSpectralMeasure
            D hD (a i) (μ i) (hμ i)) (F i) r).symm
    · intro j hj hji
      exact componentVectors_pairwise_orthogonal D hD a μ hμ haorth F i j hji.symm
        (componentVector D hD a μ F i)
        ((D.U^[r]) (componentVector D hD a μ F j))
        (SpectralRelations.self_mem_cyclic D _)
        (SpectralRelations.iterate_mem_cyclic D _ r)
    · intro hnot
      exact (hnot hi).elim
  · intro j hj
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)

def transferredCoordinate
    {n : ℕ} (hn : 0 < n) (μ : Fin n → CircleMeasureData)
    (hac : ∀ j, (μ j).μ ≪ (μ ⟨0, hn⟩).μ)
    (F : ∀ j, Lp ℂ 2 (μ j).μ) (j : Fin n) :
    Lp ℂ 2 (μ ⟨0, hn⟩).μ :=
  RadonNikodymTransfer.transfer (μ ⟨0, hn⟩) (μ j) (hac j) (F j)

theorem integral_finiteDot_transferred_eq_inner
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    {n : ℕ} (hn : 0 < n)
    (a : Fin n → D.H) (μ : Fin n → CircleMeasureData)
    (hμ : ∀ j, HasSpectralMeasure D (a j) (μ j))
    (haorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (a i) (a j))
    (hac : ∀ j, (μ j).μ ≪ (μ ⟨0, hn⟩).μ)
    (p q : D.H) (F G : ∀ j, Lp ℂ 2 (μ j).μ)
    (hp : p = ∑ j, componentVector D hD a μ F j)
    (hq : q = ∑ j, componentVector D hD a μ G j)
    (m : ℤ) :
    (∫ z, (z : ℂ) ^ m * FiniteSpectralRank.finiteDot
      (fun j ↦ transferredCoordinate hn μ hac F j z)
      (fun j ↦ transferredCoordinate hn μ hac G j z)
      ∂(μ ⟨0, hn⟩).μ) =
      @inner ℂ D.H _ (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) p) q := by
  simp only [FiniteSpectralRank.finiteDot, Finset.mul_sum]
  rw [integral_finset_sum]
  · calc
      (∑ j, ∫ z, (z : ℂ) ^ m *
          (star (transferredCoordinate hn μ hac F j z) *
            transferredCoordinate hn μ hac G j z) ∂(μ ⟨0, hn⟩).μ) =
          ∑ j, @inner ℂ D.H _
            (((SpectralMeasure.unitaryEquiv D hD) ^ (-m))
              (componentVector D hD a μ F j))
            (componentVector D hD a μ G j) := by
        apply Finset.sum_congr rfl
        intro j hj
        change (∫ z, (z : ℂ) ^ m *
          (star (RadonNikodymTransfer.transfer (μ ⟨0, hn⟩) (μ j)
            (hac j) (F j) z) *
            RadonNikodymTransfer.transfer (μ ⟨0, hn⟩) (μ j)
              (hac j) (G j) z) ∂(μ ⟨0, hn⟩).μ) = _
        rw [RadonNikodymTransfer.integral_transfer_cross
          (μ ⟨0, hn⟩) (μ j) (hac j) (fun z ↦ (z : ℂ) ^ m) (F j) (G j)]
        simpa [componentVector] using
          (CyclicOrthogonalSingularity.integral_zpow_cross_eq_inner
            D hD (a j) (μ j)
            (SpectralMeasure.full_moment_of_hasSpectralMeasure
              D hD (a j) (μ j) (hμ j)) (F j) (G j) m)
      _ = @inner ℂ D.H _
          (((SpectralMeasure.unitaryEquiv D hD) ^ (-m)) p) q := by
        rw [hp, hq, map_sum, sum_inner]
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_sum, Finset.sum_eq_single i]
        · intro j hj hji
          apply haorth i j hji.symm
          · intro K hK hai
            have hcomp : componentVector D hD a μ F i ∈ K :=
              componentVector_mem_cyclic D hD a μ hμ F i K hK hai
            exact CyclicSpectralModel.zpow_orbit_mem_reducing D hD
              (componentVector D hD a μ F i) K hK hcomp (-m)
          · exact componentVector_mem_cyclic D hD a μ hμ G j
        · intro hnot
          exact (hnot hi).elim
  · intro j hj
    let TF := transferredCoordinate hn μ hac F j
    let TG := transferredCoordinate hn μ hac G j
    have hcross : Integrable (fun z ↦ star (TF z) * TG z) (μ ⟨0, hn⟩).μ :=
      ((Lp.memLp TF).congr_norm (Lp.memLp TF).1.star
        (Filter.Eventually.of_forall fun z ↦ (norm_star (TF z)).symm)).integrable_mul
        (Lp.memLp TG)
    let c : C(Circle, ℂ) :=
      ⟨fun z ↦ (z : ℂ) ^ m,
        Continuous.zpow₀ (by fun_prop) m (fun z ↦ Or.inl (Circle.coe_ne_zero z))⟩
    exact hcross.bdd_mul c.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ c.norm_coe_le_norm z)

theorem finiteDot_transferred_ae_zero_of_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    {n : ℕ} (hn : 0 < n)
    (a : Fin n → D.H) (μ : Fin n → CircleMeasureData)
    (hμ : ∀ j, HasSpectralMeasure D (a j) (μ j))
    (haorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (a i) (a j))
    (hac : ∀ j, (μ j).μ ≪ (μ ⟨0, hn⟩).μ)
    (p q : D.H) (F G : ∀ j, Lp ℂ 2 (μ j).μ)
    (hp : p = ∑ j, componentVector D hD a μ F j)
    (hq : q = ∑ j, componentVector D hD a μ G j)
    (hpq : OrthogonalCyclicSubspaces D p q) :
    (fun z ↦ FiniteSpectralRank.finiteDot
      (fun j ↦ transferredCoordinate hn μ hac F j z)
      (fun j ↦ transferredCoordinate hn μ hac G j z))
      =ᵐ[(μ ⟨0, hn⟩).μ] 0 := by
  let f : Circle → ℂ := fun z ↦ FiniteSpectralRank.finiteDot
    (fun j ↦ transferredCoordinate hn μ hac F j z)
    (fun j ↦ transferredCoordinate hn μ hac G j z)
  have hf : Integrable f (μ ⟨0, hn⟩).μ := by
    have hterm : ∀ j : Fin n, Integrable (fun z ↦
        star (transferredCoordinate hn μ hac F j z) *
          transferredCoordinate hn μ hac G j z) (μ ⟨0, hn⟩).μ := by
      intro j
      let TF := transferredCoordinate hn μ hac F j
      let TG := transferredCoordinate hn μ hac G j
      exact ((Lp.memLp TF).congr_norm (Lp.memLp TF).1.star
        (Filter.Eventually.of_forall fun z ↦ (norm_star (TF z)).symm)).integrable_mul
        (Lp.memLp TG)
    exact (integrable_finset_sum Finset.univ fun j _ ↦ hterm j).congr
      (Filter.Eventually.of_forall fun z ↦ by simp [f, FiniteSpectralRank.finiteDot])
  have hchar (m : ℤ) :
      ∫ z, (z : ℂ) ^ m * f z ∂(μ ⟨0, hn⟩).μ = 0 := by
    rw [integral_finiteDot_transferred_eq_inner
      D hD hn a μ hμ haorth hac p q F G hp hq m]
    apply hpq
    · exact CyclicSpectralModel.zpow_orbit_mem_reducing D hD p _
        (SpectralDecomposition.cyclicSubmodule_reducing D p)
        (SpectralDecomposition.generator_mem_cyclicSubmodule D p) (-m)
    · exact SpectralRelations.self_mem_cyclic D q
  have hmom : ∀ r : C(Circle, ℂ), r ∈ CircleLaurent.span →
      ∫ z, r z * f z ∂(μ ⟨0, hn⟩).μ = 0 := by
    intro r hr
    refine Submodule.span_induction (p := fun r _ ↦
      ∫ z, r z * f z ∂(μ ⟨0, hn⟩).μ = 0) ?_ ?_ ?_ ?_ hr
    · rintro r ⟨m, rfl⟩
      exact hchar m
    · simp
    · intro r s hr hs hir his
      have hirInt := hf.bdd_mul r.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z ↦ r.norm_coe_le_norm z)
      have hisInt := hf.bdd_mul s.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z ↦ s.norm_coe_le_norm z)
      simp only [ContinuousMap.add_apply, add_mul]
      rw [integral_add hirInt hisInt, hir, his, add_zero]
    · intro c r hr hir
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, hir, mul_zero]
  exact CircleFourierUniqueness.complex_ae_zero_of_laurent_moments
    (μ ⟨0, hn⟩) hf hmom

/-- A common nonzero spectral measure cannot be carried by `n+1` pairwise
orthogonal vectors which all live in the sum of only `n` cyclic coordinates. -/
theorem no_overfull_finite_cyclic_coordinates
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    {n : ℕ} (hn : 0 < n)
    (a : Fin n → D.H) (μ : Fin n → CircleMeasureData)
    (hμ : ∀ j, HasSpectralMeasure D (a j) (μ j))
    (haorth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (a i) (a j))
    (hac : ∀ j, (μ j).μ ≪ (μ ⟨0, hn⟩).μ)
    (p : Fin (n + 1) → D.H) (ν : CircleMeasureData)
    (F : ∀ i j, Lp ℂ 2 (μ j).μ)
    (hp : ∀ i, p i = ∑ j, componentVector D hD a μ (F i) j)
    (hν : ∀ i, HasSpectralMeasure D (p i) ν)
    (hνnonzero : ν.μ Set.univ ≠ 0)
    (hνac : ν.μ ≪ (μ ⟨0, hn⟩).μ)
    (hporth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (p i) (p j)) :
    False := by
  let V : Fin (n + 1) → Circle → Fin n → ℂ := fun i z j ↦
    transferredCoordinate hn μ hac (F i) j z
  have hVorth : ∀ i j, i ≠ j →
      ∀ᵐ z ∂(μ ⟨0, hn⟩).μ,
        FiniteSpectralRank.finiteDot (V i z) (V j z) = 0 := by
    intro i j hij
    exact finiteDot_transferred_ae_zero_of_orthogonal
      D hD hn a μ hμ haorth hac (p i) (p j) (F i) (F j)
      (hp i) (hp j) (hporth i j hij)
  have hrank : ∀ᵐ z ∂(μ ⟨0, hn⟩).μ, ∃ i, V i z = 0 :=
    FiniteSpectralRank.ae_exists_zero_of_pairwise_finiteDot_zero
      (μ ⟨0, hn⟩).μ n V hVorth
  have hrankν : ∀ᵐ z ∂ν.μ, ∃ i, V i z = 0 := hνac.ae_le hrank
  let E : Fin (n + 1) → Set Circle := fun i ↦
    ⋂ j : Fin n, {z | V i z j = 0}
  have hEmeas (i : Fin (n + 1)) : MeasurableSet (E i) := by
    apply MeasurableSet.iInter
    intro j
    exact (Lp.stronglyMeasurable
      (transferredCoordinate hn μ hac (F i) j)).measurable
        (measurableSet_singleton (0 : ℂ))
  have hEzero (i : Fin (n + 1)) : ν.μ (E i) = 0 := by
    have hcoord := coordinateMeasure_isSpectral
      D hD a μ hμ haorth (F i)
    have hcoord' : HasSpectralMeasure D (p i) (coordinateMeasure μ (F i)) := by
      rw [hp i]
      exact hcoord
    have heq : ν = coordinateMeasure μ (F i) :=
      SpectralMeasure.eq_of_nat_moments _ _ fun r ↦
        (hν i r).trans (hcoord' r).symm
    rw [heq]
    change (∑ j, (CyclicMeasureType.vectorDensityMeasure (F i j)).μ) (E i) = 0
    rw [finsetSumMeasure_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hdensity : CyclicMeasureType.vectorDensityMeasure (F i j) =
        CyclicMeasureType.vectorDensityMeasure
          (transferredCoordinate hn μ hac (F i) j) := by
      exact (RadonNikodymTransfer.vectorDensityMeasure_transfer
        (μ ⟨0, hn⟩) (μ j) (hac j) (F i j)).symm
    rw [hdensity]
    apply (withDensity_apply_eq_zero'
      (CyclicMeasureType.spectralDensity_aemeasurable _)).2
    have hempty : {z | CyclicMeasureType.spectralDensity
        (transferredCoordinate hn μ hac (F i) j) z ≠ 0} ∩ E i = ∅ := by
      ext z
      constructor
      · intro hz
        have hzcoord : V i z j = 0 := Set.mem_iInter.mp hz.2 j
        exfalso
        apply hz.1
        simp [CyclicMeasureType.spectralDensity, V, hzcoord]
      · simp
    rw [hempty, measure_empty]
  let U : Set Circle := ⋃ i, E i
  have hUzero : ν.μ U = 0 := measure_iUnion_null hEzero
  have hmemU : ∀ᵐ z ∂ν.μ, z ∈ U := by
    filter_upwards [hrankν] with z hz
    obtain ⟨i, hi⟩ := hz
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iInter.mpr fun j ↦ congrFun hi j⟩
  have hUfull : ν.μ U = ν.μ Set.univ := by
    apply measure_congr
    filter_upwards [hmemU] with z hz
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      exact hz
  exact hνnonzero (hUfull.symm.trans hUzero)

end Chapter02.FiniteCyclicCoordinates
