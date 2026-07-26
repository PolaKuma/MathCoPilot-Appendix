import Chapter02.Spectral.OrderedMultiplicityVectors
import Chapter02.Spectral.MaximalSpectralType
import Chapter02.Spectral.FiniteCyclicCoordinates

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.OrderedMultiplicityDecomposition

universe u

open OrderedMultiplicityVectors

def encodedMultiplicityVector
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (q : ℕ) : D.H :=
  multiplicityVector D hD x μ hμ (Nat.unpair q).1 (Nat.unpair q).2

theorem inCyclicSubspace_zero_eq_zero
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (a : D.H)
    (ha : InCyclicSubspace D 0 a) : a = 0 := by
  let Z : Set D.H := {0}
  have hZ : IsClosedReducingSubspace D Z := by
    refine ⟨by simp [Z], ?_, ?_, ?_⟩
    · simp [Z]
    · intro v hv y hlim
      have hv0 : Tendsto v atTop (nhds 0) := by
        apply tendsto_const_nhds.congr'
        exact Filter.Eventually.of_forall fun n ↦ by simpa [Z] using (hv n).symm
      have : y = 0 := tendsto_nhds_unique hlim hv0
      simp [Z, this]
    · intro y
      constructor
      · intro hy
        simpa [Z] using congrArg D.U (show y = 0 by simpa [Z] using hy)
      · intro hUy
        have hnorm : ‖y‖ = 0 := by
          rw [← hD.2 y]
          simpa [Z] using hUy
        simpa [Z] using norm_eq_zero.mp hnorm
  have haZ := ha Z hZ (by simp [Z])
  simpa [Z] using haZ

theorem orthogonalCyclicSubspaces_zero_left
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (a : D.H) :
    OrthogonalCyclicSubspaces D 0 a := by
  intro b c hb _
  rw [inCyclicSubspace_zero_eq_zero D hD b hb]
  simp

theorem orthogonalCyclicSubspaces_zero_right
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D) (a : D.H) :
    OrthogonalCyclicSubspaces D a 0 := by
  intro b c _ hc
  rw [inCyclicSubspace_zero_eq_zero D hD c hc]
  simp

theorem encodedMultiplicityVector_pairwise_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x) :
    ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D
      (encodedMultiplicityVector D hD x μ hμ i)
      (encodedMultiplicityVector D hD x μ hμ j) := by
  intro i j hij
  let p := Nat.unpair i
  let q := Nat.unpair j
  have hpq : p ≠ q := by
    intro hpq
    apply hij
    calc
      i = Nat.pair p.1 p.2 := (Nat.pair_unpair i).symm
      _ = Nat.pair q.1 q.2 := congrArg (fun t : ℕ × ℕ ↦ Nat.pair t.1 t.2) hpq
      _ = j := Nat.pair_unpair j
  by_cases hpi : IsActiveMultiplicityIndex p.1 p.2
  · by_cases hqj : IsActiveMultiplicityIndex q.1 q.2
    · exact active_multiplicityVectors_orthogonal D hD x μ hμ hdec hpq hpi hqj
    · rw [show encodedMultiplicityVector D hD x μ hμ j = 0 by
        exact multiplicityVector_eq_zero_of_inactive D hD x μ hμ q.1 q.2 hqj]
      exact orthogonalCyclicSubspaces_zero_right D hD _
  · rw [show encodedMultiplicityVector D hD x μ hμ i = 0 by
      exact multiplicityVector_eq_zero_of_inactive D hD x μ hμ p.1 p.2 hpi]
    exact orthogonalCyclicSubspaces_zero_left D hD _

theorem projectionCoordinate_ae_zero_of_encoded_orthogonality
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    (r : D.H)
    (hr : ∀ q, r ∈ (SpectralDecomposition.cyclicSubmodule D
      (encodedMultiplicityVector D hD x μ hμ q))ᗮ)
    (k : ℕ) :
    (fun z ↦ DirectSumSpectralModel.projectionCoordinate D hD x μ hμ r k z)
      =ᵐ[(μ k).μ] 0 := by
  let G := DirectSumSpectralModel.projectionCoordinate D hD x μ hμ r k
  have hpiece : ∀ n, ∀ᵐ z ∂(μ k).μ,
      z ∈ OrderedMultiplicitySupports.multiplicityStratum μ n → G z = 0 := by
    intro n
    by_cases hactive : IsActiveMultiplicityIndex n k
    · have hrnk : r ∈ (SpectralDecomposition.cyclicSubmodule D
          (multiplicityVector D hD x μ hμ n k))ᗮ := by
        simpa [encodedMultiplicityVector, Nat.unpair_pair] using hr (Nat.pair n k)
      have hz := projectionCoordinate_zero_on_activeStratum
        D hD x μ hμ n k hactive r hrnk
      filter_upwards [hz] with z hz
      intro hzB
      simpa [G, Set.indicator_of_mem hzB] using hz
    · have hnull := OrderedMultiplicitySupports.inactiveStratum_componentMeasure_zero
        D hD x μ hμ hord n k hactive
      have haenot : ∀ᵐ z ∂(μ k).μ,
          z ∉ OrderedMultiplicitySupports.multiplicityStratum μ n :=
        measure_eq_zero_iff_ae_notMem.mp hnull
      exact haenot.mono fun z hznot hzmem ↦ (hznot hzmem).elim
  filter_upwards [ae_all_iff.mpr hpiece] with z hz
  have hzUnion : z ∈ ⋃ n, OrderedMultiplicitySupports.multiplicityStratum μ n := by
    rw [OrderedMultiplicitySupports.iUnion_multiplicityStratum μ]
    trivial
  obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hzUnion
  exact hz n hzn

theorem encodedMultiplicityVector_complete
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    (r : D.H)
    (hr : ∀ q, r ∈ (SpectralDecomposition.cyclicSubmodule D
      (encodedMultiplicityVector D hD x μ hμ q))ᗮ) : r = 0 := by
  apply SpectralDecomposition.orthogonal_to_all_cyclic_eq_zero D x hdec r
  intro k
  apply (SpectralDecomposition.cyclicSubmodule D (x k)).starProjection_apply_eq_zero_iff.mp
  change SpectralDecomposition.cyclicProjectionFamily D x r k = 0
  rw [← DirectSumSpectralModel.projectionCoordinate_spec D hD x μ hμ r k]
  have hG := projectionCoordinate_ae_zero_of_encoded_orthogonality
    D hD x μ hμ hord r hr k
  have hLp : DirectSumSpectralModel.projectionCoordinate D hD x μ hμ r k = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    exact hG
  rw [hLp]
  exact map_zero _

theorem encodedMultiplicityVector_decomposition
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1))) :
    IsOrthogonalCyclicDecomposition D
      (encodedMultiplicityVector D hD x μ hμ) := by
  exact SpectralDecomposition.orthogonalCyclicDecomposition_of_complete D _
    (encodedMultiplicityVector_pairwise_orthogonal D hD x μ hμ hdec)
    (encodedMultiplicityVector_complete D hD x μ hμ hdec hord)

theorem isMultiplicityDecomposition_of_ordered
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hdec : IsOrthogonalCyclicDecomposition D x)
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1))) :
    IsMultiplicityDecomposition D
      (OrderedMultiplicitySupports.multiplicityStratum μ)
      (multiplicityVector D hD x μ hμ)
      (multiplicityMeasure μ) := by
  let v := multiplicityVector D hD x μ hμ
  let ν := multiplicityMeasure μ
  have henc := encodedMultiplicityVector_decomposition D hD x μ hμ hdec hord
  refine ⟨OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ,
    OrderedMultiplicitySupports.multiplicityStrata_pairwise_disjoint μ,
    OrderedMultiplicitySupports.iUnion_multiplicityStratum μ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k hinactive
    exact multiplicityVector_eq_zero_of_inactive D hD x μ hμ n k hinactive
  · intro n k hactive
    exact multiplicityVector_active_spec D hD x μ hμ n k hactive
  · intro n i j hi hj
    exact active_multiplicityMeasure_spectralType_eq
      D hD x μ hμ hord n i j hi hj
  · intro n i m j hne hni hmj
    exact active_multiplicityVectors_orthogonal D hD x μ hμ hdec hne hni hmj
  · intro y ε hε
    obtain ⟨s, z, hz, hclose⟩ := henc.2 y ε hε
    let active : ℕ → Prop := fun q ↦
      IsActiveMultiplicityIndex (Nat.unpair q).1 (Nat.unpair q).2
    let sa := s.filter active
    let e : ℕ ↪ ℕ × ℕ := Nat.pairEquiv.symm.toEmbedding
    let sp : Finset (ℕ × ℕ) := sa.map e
    let w : ℕ × ℕ → D.H := fun p ↦ z (Nat.pair p.1 p.2)
    refine ⟨sp, w, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hqsa, hqp⟩ := Finset.mem_map.mp hp
      have hq : q ∈ s := (Finset.mem_filter.mp hqsa).1
      have hqactive : active q := (Finset.mem_filter.mp hqsa).2
      subst p
      constructor
      · simpa [active, e, Nat.pairEquiv] using hqactive
      · have hzq := hz q hq
        simpa [w, e, encodedMultiplicityVector, Nat.pairEquiv,
          Nat.pair_unpair] using hzq
    · have hsumFilter : ∑ q ∈ sa, z q = ∑ q ∈ s, z q := by
        apply Finset.sum_subset (Finset.filter_subset active s)
        intro q hqs hqnot
        have hqinactive : ¬ active q := by
          intro hqa
          exact hqnot (Finset.mem_filter.mpr ⟨hqs, hqa⟩)
        have hzq := hz q hqs
        have hzero : encodedMultiplicityVector D hD x μ hμ q = 0 := by
          exact multiplicityVector_eq_zero_of_inactive D hD x μ hμ
            (Nat.unpair q).1 (Nat.unpair q).2 hqinactive
        rw [hzero] at hzq
        exact inCyclicSubspace_zero_eq_zero D hD (z q) hzq
      have hsumMap : ∑ p ∈ sp, w p = ∑ q ∈ sa, z q := by
        simp [sp, w, e, Nat.pairEquiv, Nat.pair_unpair]
      rw [hsumMap, hsumFilter]
      exact hclose

def multiplicityValue (n : ℕ) : ENNReal :=
  if n = 0 then ⊤ else n

def orderedMultiplicityFunction (μ : ℕ → CircleMeasureData) (z : Circle) : ENNReal :=
  ∑' n, (OrderedMultiplicitySupports.multiplicityStratum μ n).indicator
    (fun _ ↦ multiplicityValue n) z

theorem measurable_orderedMultiplicityFunction (μ : ℕ → CircleMeasureData) :
    Measurable (orderedMultiplicityFunction μ) := by
  apply Measurable.ennreal_tsum
  intro n
  exact measurable_const.indicator
    (OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n)

theorem orderedMultiplicityFunction_on_stratum
    (μ : ℕ → CircleMeasureData) (n : ℕ) :
    ∀ z ∈ OrderedMultiplicitySupports.multiplicityStratum μ n,
      orderedMultiplicityFunction μ z = multiplicityValue n := by
  intro z hzn
  rw [orderedMultiplicityFunction, tsum_eq_single n]
  · simp [Set.indicator_of_mem hzn]
  · intro m hmn
    have hznot : z ∉ OrderedMultiplicitySupports.multiplicityStratum μ m := by
      intro hzm
      exact Set.disjoint_left.1
        (OrderedMultiplicitySupports.multiplicityStrata_pairwise_disjoint μ n m hmn.symm)
        hzn hzm
    simp [Set.indicator_of_notMem hznot]

theorem hasSpectralMultiplicityData_of_ordered
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x) :
    HasSpectralMultiplicityData D (μ 0) (orderedMultiplicityFunction μ) := by
  refine ⟨?_, measurable_orderedMultiplicityFunction μ,
    OrderedMultiplicitySupports.multiplicityStratum μ,
    multiplicityVector D hD x μ hμ, multiplicityMeasure μ, ?_, ?_⟩
  · refine ⟨hD, ⟨x 0, hμ 0⟩, ?_⟩
    intro y
    obtain ⟨ν, hν, _⟩ := SpectralMeasure.spectralMeasure D hD y
    refine ⟨ν, hν, ?_⟩
    exact OrderedSpectralDecomposition.firstVector_dominates_every_vector
      D hD x hord y (μ 0) ν (hμ 0) hν
  · exact isMultiplicityDecomposition_of_ordered
      D hD x μ hμ hord.1 hord.2
  · intro n
    filter_upwards [] with z hz
    exact orderedMultiplicityFunction_on_stratum μ n z hz

theorem exists_spectralMultiplicityData
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D) :
    ∃ μmax : CircleMeasureData, ∃ multiplicity : Circle → ENNReal,
      HasSpectralMultiplicityData D μmax multiplicity := by
  obtain ⟨x, hx⟩ :=
    OrderedSpectralDecomposition.exists_orderedSpectralDecomposition D hsep hD
  choose μ hμ _ using fun n ↦ SpectralMeasure.spectralMeasure D hD (x n)
  exact ⟨μ 0, orderedMultiplicityFunction μ,
    hasSpectralMultiplicityData_of_ordered D hD x μ hμ hx⟩

def encodedDecompositionVector
    (D : HilbertOperatorData.{u}) (y : ℕ → ℕ → D.H) (q : ℕ) : D.H :=
  y (Nat.unpair q).1 (Nat.unpair q).2

theorem encodedDecompositionVector_decomposition
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) :
    IsOrthogonalCyclicDecomposition D (encodedDecompositionVector D y) := by
  rcases hM with ⟨_hmeas, _hdisj, _hcover, hzero, _hspec,
    _htype, horth, hcomplete⟩
  constructor
  · intro i j hij
    let p := Nat.unpair i
    let q := Nat.unpair j
    have hpq : p ≠ q := by
      intro hpq
      apply hij
      calc
        i = Nat.pair p.1 p.2 := (Nat.pair_unpair i).symm
        _ = Nat.pair q.1 q.2 := congrArg (fun t : ℕ × ℕ ↦ Nat.pair t.1 t.2) hpq
        _ = j := Nat.pair_unpair j
    by_cases hp : IsActiveMultiplicityIndex p.1 p.2
    · by_cases hq : IsActiveMultiplicityIndex q.1 q.2
      · exact horth p.1 p.2 q.1 q.2 hpq hp hq
      · rw [show encodedDecompositionVector D y j = 0 by
          exact hzero q.1 q.2 hq]
        exact orthogonalCyclicSubspaces_zero_right D hD _
    · rw [show encodedDecompositionVector D y i = 0 by
        exact hzero p.1 p.2 hp]
      exact orthogonalCyclicSubspaces_zero_left D hD _
  · intro a ε hε
    obtain ⟨s, z, hz, hclose⟩ := hcomplete a ε hε
    let e : ℕ × ℕ ↪ ℕ := Nat.pairEquiv.toEmbedding
    let sn : Finset ℕ := s.map e
    let zn : ℕ → D.H := fun q ↦ z (Nat.unpair q)
    refine ⟨sn, zn, ?_, ?_⟩
    · intro q hq
      obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
      subst q
      have hzp := (hz p hp).2
      have hunpair : Nat.unpair (Function.uncurry Nat.pair p) = p := by
        apply Prod.ext <;> simp [Function.uncurry, Nat.unpair_pair]
      simpa [zn, e, encodedDecompositionVector, Nat.pairEquiv, hunpair] using hzp
    · have hsum : ∑ q ∈ sn, zn q = ∑ p ∈ s, z p := by
        rw [show ∑ q ∈ sn, zn q =
            ∑ p ∈ s, z (Nat.unpair (Function.uncurry Nat.pair p)) by
          simp [sn, zn, e, Nat.pairEquiv]]
        apply Finset.sum_congr rfl
        intro p hp
        congr 1
        apply Prod.ext <;> simp [Function.uncurry, Nat.unpair_pair]
      rw [hsum]
      exact hclose

def zeroCircleMeasure : CircleMeasureData where
  μ := 0
  isFinite := inferInstance

theorem zero_hasSpectralMeasure (D : HilbertOperatorData.{u}) :
    HasSpectralMeasure D 0 zeroCircleMeasure := by
  intro n
  simp [circleFourierCoefficient, zeroCircleMeasure]

def completedMultiplicityMeasure
    (ν : ℕ → ℕ → CircleMeasureData) (n k : ℕ) : CircleMeasureData :=
  if IsActiveMultiplicityIndex n k then ν n k else zeroCircleMeasure

theorem completedMultiplicityMeasure_isSpectral
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (n k : ℕ) :
    HasSpectralMeasure D (y n k) (completedMultiplicityMeasure ν n k) := by
  by_cases hactive : IsActiveMultiplicityIndex n k
  · simpa [completedMultiplicityMeasure, hactive] using (hM.2.2.2.2.1 n k hactive).1
  · rw [hM.2.2.2.1 n k hactive]
    simpa [completedMultiplicityMeasure, hactive] using zero_hasSpectralMeasure D

def multiplicityColumnVector
    (D : HilbertOperatorData.{u}) (y : ℕ → ℕ → D.H) (k : ℕ) : D.H :=
  MaximalSpectralType.maximalTypeVector D (fun n ↦ y n k)

def multiplicityColumnMeasure
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (k : ℕ) : CircleMeasureData :=
  MaximalSpectralType.maximalTypeMeasure D (fun n ↦ y n k)
    (fun n ↦ completedMultiplicityMeasure ν n k)
    (fun n ↦ completedMultiplicityMeasure_isSpectral D B y ν hM n k)

theorem multiplicityColumnFamily_pairwise_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (k : ℕ) :
    ∀ n m, n ≠ m → OrthogonalCyclicSubspaces D (y n k) (y m k) := by
  have henc := encodedDecompositionVector_decomposition D hD B y ν hM
  intro n m hnm
  have hp : Nat.pair n k ≠ Nat.pair m k := by
    intro hp
    have := congrArg Nat.unpair hp
    apply hnm
    simpa [Nat.unpair_pair] using congrArg Prod.fst this
  simpa [encodedDecompositionVector, Nat.unpair_pair] using
    henc.1 (Nat.pair n k) (Nat.pair m k) hp

theorem multiplicityColumn_hasSpectralMeasure
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (k : ℕ) :
    HasSpectralMeasure D (multiplicityColumnVector D y k)
      (multiplicityColumnMeasure D B y ν hM k) := by
  exact MaximalSpectralType.maximalTypeMeasure_isSpectral D hD
    (fun n ↦ y n k)
    (multiplicityColumnFamily_pairwise_orthogonal D hD B y ν hM k)
    (fun n ↦ completedMultiplicityMeasure ν n k)
    (fun n ↦ completedMultiplicityMeasure_isSpectral D B y ν hM n k)

theorem maximalTypeVector_mem_fixedCyclic_orthogonal
    (D : HilbertOperatorData.{u})
    (a : D.H) (z : ℕ → D.H)
    (horth : ∀ j, OrthogonalCyclicSubspaces D a (z j)) :
    MaximalSpectralType.maximalTypeVector D z ∈
      (SpectralDecomposition.cyclicSubmodule D a)ᗮ := by
  let v : ℕ → D.H := fun N ↦ ∑ j ∈ Finset.range N,
    MaximalSpectralType.spectralCoefficient D z j • z j
  have hv : ∀ N, v N ∈ (SpectralDecomposition.cyclicSubmodule D a)ᗮ := by
    intro N
    apply Submodule.sum_mem
    intro j hj
    rw [Submodule.mem_orthogonal]
    intro b hb
    exact horth j b _ hb
      ((SpectralDecomposition.cyclicSubmodule D (z j)).smul_mem _
        (SpectralDecomposition.generator_mem_cyclicSubmodule D (z j)))
  have hlim : Tendsto v atTop
      (nhds (MaximalSpectralType.maximalTypeVector D z)) :=
    (MaximalSpectralType.hasSum_maximalTypeVector D z).tendsto_sum_nat
  have hclosed : IsClosed
      ((SpectralDecomposition.cyclicSubmodule D a)ᗮ : Set D.H) :=
    Submodule.isClosed_orthogonal _
  rw [← isSeqClosed_iff_isClosed] at hclosed
  exact hclosed (x := v)
    (p := MaximalSpectralType.maximalTypeVector D z) hv hlim

theorem maximalTypeVectors_orthogonal_of_cross
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x y : ℕ → D.H)
    (hcross : ∀ i j, OrthogonalCyclicSubspaces D (x i) (y j)) :
    OrthogonalCyclicSubspaces D
      (MaximalSpectralType.maximalTypeVector D x)
      (MaximalSpectralType.maximalTypeVector D y) := by
  let Y := MaximalSpectralType.maximalTypeVector D y
  have hxiY (i : ℕ) : OrthogonalCyclicSubspaces D (x i) Y := by
    exact SpectralRelations.cyclic_subspaces_orthogonal_of_mem D
      (SpectralDecomposition.cyclicSubmodule D (x i)) (x i) Y
      (SpectralDecomposition.cyclicSubmodule_reducing D (x i))
      (SpectralRelations.orthogonal_reducing D hD
        (SpectralDecomposition.cyclicSubmodule D (x i))
        (SpectralDecomposition.cyclicSubmodule_reducing D (x i)))
      (SpectralDecomposition.generator_mem_cyclicSubmodule D (x i))
      (maximalTypeVector_mem_fixedCyclic_orthogonal D (x i) y (hcross i))
  have hXorth : MaximalSpectralType.maximalTypeVector D x ∈
      (SpectralDecomposition.cyclicSubmodule D Y)ᗮ := by
    apply maximalTypeVector_mem_fixedCyclic_orthogonal D Y x
    intro i
    exact OrthogonalCyclicDecomposition.orthogonalCyclicSubspaces_symm D (hxiY i)
  have hYX : OrthogonalCyclicSubspaces D Y
      (MaximalSpectralType.maximalTypeVector D x) :=
    SpectralRelations.cyclic_subspaces_orthogonal_of_mem D
      (SpectralDecomposition.cyclicSubmodule D Y) Y
      (MaximalSpectralType.maximalTypeVector D x)
      (SpectralDecomposition.cyclicSubmodule_reducing D Y)
      (SpectralRelations.orthogonal_reducing D hD
        (SpectralDecomposition.cyclicSubmodule D Y)
        (SpectralDecomposition.cyclicSubmodule_reducing D Y))
      (SpectralDecomposition.generator_mem_cyclicSubmodule D Y) hXorth
  exact OrthogonalCyclicDecomposition.orthogonalCyclicSubspaces_symm D hYX

theorem multiplicityColumns_pairwise_orthogonal
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) :
    ∀ k l, k ≠ l → OrthogonalCyclicSubspaces D
      (multiplicityColumnVector D y k) (multiplicityColumnVector D y l) := by
  have henc := encodedDecompositionVector_decomposition D hD B y ν hM
  intro k l hkl
  apply maximalTypeVectors_orthogonal_of_cross D hD
  intro n m
  have hp : Nat.pair n k ≠ Nat.pair m l := by
    intro hp
    have hu := congrArg Nat.unpair hp
    apply hkl
    simpa [Nat.unpair_pair] using congrArg Prod.snd hu
  simpa [encodedDecompositionVector, Nat.unpair_pair] using
    henc.1 (Nat.pair n k) (Nat.pair m l) hp

theorem completedMultiplicityMeasure_next_ac
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (n k : ℕ) :
    (completedMultiplicityMeasure ν n (k + 1)).μ ≪
      (completedMultiplicityMeasure ν n k).μ := by
  rcases hM with ⟨_hmeas, _hdisj, _hcover, _hzero, _hspec,
    htype, _horth, _hcomplete⟩
  by_cases hn : IsActiveMultiplicityIndex n (k + 1)
  · have hnk : IsActiveMultiplicityIndex n k := by
      rcases hn with hn0 | hlt
      · exact Or.inl hn0
      · exact Or.inr (lt_trans (Nat.lt_succ_self k) hlt)
    have heq := htype n k (k + 1) hnk hn
    have hmem : ν n (k + 1) ∈ SpectralTypeDefinition (ν n (k + 1)) :=
      ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
    have hmem' : ν n (k + 1) ∈ SpectralTypeDefinition (ν n k) := by
      rw [heq]
      exact hmem
    simpa [completedMultiplicityMeasure, hn, hnk] using hmem'.1
  · simp only [completedMultiplicityMeasure, if_neg hn, zeroCircleMeasure]
    exact Measure.AbsolutelyContinuous.mk (by simp)

theorem multiplicityColumnMeasure_next_ac
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (k : ℕ) :
    (multiplicityColumnMeasure D B y ν hM (k + 1)).μ ≪
      (multiplicityColumnMeasure D B y ν hM k).μ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  change Measure.sum
      (MaximalSpectralType.weightedComponentMeasure D
        (fun n ↦ y n (k + 1))
        (fun n ↦ completedMultiplicityMeasure ν n (k + 1))) s = 0
  rw [Measure.sum_apply _ hs]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  have hcurrent : (completedMultiplicityMeasure ν n k).μ s = 0 := by
    exact MaximalSpectralType.componentMeasure_absolutelyContinuous_maximalTypeMeasure
      D (fun n ↦ y n k) (fun n ↦ completedMultiplicityMeasure ν n k)
      (fun n ↦ completedMultiplicityMeasure_isSpectral D B y ν hM n k) n hzero
  have hnext : (completedMultiplicityMeasure ν n (k + 1)).μ s = 0 :=
    completedMultiplicityMeasure_next_ac D B y ν hM n k hcurrent
  rw [MaximalSpectralType.weightedComponentMeasure,
    Measure.smul_apply, smul_eq_mul, hnext, mul_zero]

theorem multiplicityColumn_dominates_next
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (k : ℕ) :
    SpectralMeasureDominatesVector D
      (multiplicityColumnVector D y k)
      (multiplicityColumnVector D y (k + 1)) := by
  intro μk μnext hμk hμnext
  have hkCanonical := multiplicityColumn_hasSpectralMeasure D hD B y ν hM k
  have hnextCanonical := multiplicityColumn_hasSpectralMeasure D hD B y ν hM (k + 1)
  have hek : μk = multiplicityColumnMeasure D B y ν hM k :=
    SpectralMeasure.eq_of_nat_moments _ _ fun n ↦
      (hμk n).trans (hkCanonical n).symm
  have henext : μnext = multiplicityColumnMeasure D B y ν hM (k + 1) :=
    SpectralMeasure.eq_of_nat_moments _ _ fun n ↦
      (hμnext n).trans (hnextCanonical n).symm
  subst μk
  subst μnext
  exact multiplicityColumnMeasure_next_ac D B y ν hM k

theorem active_multiplicity_component_ac_ordered_component
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k : ℕ) (hnk : IsActiveMultiplicityIndex n k) :
    (ν n k).μ ≪ (μ k).μ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hμA
  by_contra hνA
  let β := OrderedSpectralUniqueness.restrictedCircleMeasure (ν n k) A
  have hβacK : β.μ ≪ (ν n k).μ :=
    OrderedSpectralUniqueness.restrictedCircleMeasure_absolutelyContinuous _ _
  have hactive (i : Fin (k + 1)) : IsActiveMultiplicityIndex n i := by
    rcases hnk with hn0 | hkn
    · exact Or.inl hn0
    · exact Or.inr (by omega)
  have hβac (i : Fin (k + 1)) : β.μ ≪ (ν n i).μ := by
    have heq := hM.2.2.2.2.2.1 n k i hnk (hactive i)
    have hself : ν n k ∈ SpectralTypeDefinition (ν n k) :=
      ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
    have hki : (ν n k).μ ≪ (ν n i).μ := by
      have hm : ν n k ∈ SpectralTypeDefinition (ν n i) := by
        rw [← heq]
        exact hself
      exact hm.1
    exact hβacK.trans hki
  choose p hpcyc hpβ using fun i : Fin (k + 1) ↦
    SpectralRelations.exists_cyclic_vector_with_ac_measure
      D hD (y n i) (ν n i) β (hM.2.2.2.2.1 n i (hactive i)).1 (hβac i)
  have hpOrth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (p i) (p j) := by
    intro i j hij a b ha hb
    have hpairs : (n, (i : ℕ)) ≠ (n, (j : ℕ)) := by
      intro h
      exact hij (Fin.ext (congrArg Prod.snd h))
    have hyorth := hM.2.2.2.2.2.2.1 n i n j hpairs (hactive i) (hactive j)
    exact hyorth a b
      (ha _ (SpectralDecomposition.cyclicSubmodule_reducing D (y n i)) (hpcyc i))
      (hb _ (SpectralDecomposition.cyclicSubmodule_reducing D (y n j)) (hpcyc j))
  have hβuniv : β.μ Set.univ ≠ 0 := by
    change (ν n k).μ.restrict A Set.univ ≠ 0
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hνA
  have hβAc : β.μ Aᶜ = 0 := by
    change (ν n k).μ.restrict A Aᶜ = 0
    rw [Measure.restrict_apply hA.compl]
    simp
  exact FiniteDirectSumOrthogonality.no_overfull_common_spectral_measure
    D hD x μ hμ hord k p β hpβ hβuniv A hβAc hμA hpOrth

theorem multiplicityColumnMeasure_ac_ordered_component
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (k : ℕ) :
    (multiplicityColumnMeasure D B y ν hM k).μ ≪ (μ k).μ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hμA
  change Measure.sum
      (MaximalSpectralType.weightedComponentMeasure D
        (fun n ↦ y n k) (fun n ↦ completedMultiplicityMeasure ν n k)) A = 0
  rw [Measure.sum_apply _ hA]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  by_cases hactive : IsActiveMultiplicityIndex n k
  · have hνA := active_multiplicity_component_ac_ordered_component
      D hD x μ hμ hord B y ν hM n k hactive hμA
    rw [MaximalSpectralType.weightedComponentMeasure,
      completedMultiplicityMeasure, if_pos hactive,
      Measure.smul_apply, smul_eq_mul, hνA, mul_zero]
  · simp [MaximalSpectralType.weightedComponentMeasure,
      completedMultiplicityMeasure, hactive, zeroCircleMeasure]

theorem completedMultiplicityMeasure_otherStratum_zero
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (m r j : ℕ) (hother : r ≠ m ∨ ¬ IsActiveMultiplicityIndex r j) :
    (completedMultiplicityMeasure ν r j).μ (B m) = 0 := by
  by_cases hactive : IsActiveMultiplicityIndex r j
  · have hrm : r ≠ m := by
      rcases hother with hrm | hinactive
      · exact hrm
      · exact (hinactive hactive).elim
    have hsupp := (hM.2.2.2.2.1 r j hactive).2
    apply measure_mono_null (t := (B r)ᶜ)
    · intro z hzm hzr
      exact Set.disjoint_left.1 (hM.2.1 r m hrm) hzr hzm
    · simpa [completedMultiplicityMeasure, hactive] using hsupp
  · simp [completedMultiplicityMeasure, hactive, zeroCircleMeasure]

def encodedDecompositionMeasure
    (ν : ℕ → ℕ → CircleMeasureData) (q : ℕ) : CircleMeasureData :=
  completedMultiplicityMeasure ν (Nat.unpair q).1 (Nat.unpair q).2

theorem encodedDecompositionMeasure_isSpectral
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (q : ℕ) :
    HasSpectralMeasure D (encodedDecompositionVector D y q)
      (encodedDecompositionMeasure ν q) := by
  exact completedMultiplicityMeasure_isSpectral D B y ν hM
    (Nat.unpair q).1 (Nat.unpair q).2

theorem encodedProjection_zero_off_stratum
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (p : D.H) (γ : CircleMeasureData) (hγ : HasSpectralMeasure D p γ)
    (m q : ℕ) (hγsupp : γ.μ (B m)ᶜ = 0)
    (hoff : (Nat.unpair q).1 ≠ m ∨
      ¬ IsActiveMultiplicityIndex (Nat.unpair q).1 (Nat.unpair q).2) :
    DirectSumSpectralModel.projectionCoordinate D hD
      (encodedDecompositionVector D y) (encodedDecompositionMeasure ν)
      (encodedDecompositionMeasure_isSpectral D B y ν hM) p q = 0 := by
  apply DirectSumMeasureCoordinates.projectionCoordinate_eq_zero_of_support
    D hD (encodedDecompositionVector D y) (encodedDecompositionMeasure ν)
    (encodedDecompositionMeasure_isSpectral D B y ν hM)
    (encodedDecompositionVector_decomposition D hD B y ν hM)
    p γ hγ (B m) hγsupp q
  exact completedMultiplicityMeasure_otherStratum_zero D B y ν hM
    m (Nat.unpair q).1 (Nat.unpair q).2 hoff

theorem exists_finite_stratum_coordinates
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (p : D.H) (γ : CircleMeasureData) (hγ : HasSpectralMeasure D p γ)
    (m : ℕ) (hm : 0 < m) (hγsupp : γ.μ (B m)ᶜ = 0) :
    ∃ F : ∀ j : Fin m, Lp ℂ 2 (ν m j).μ,
      p = ∑ j, FiniteCyclicCoordinates.componentVector D hD
        (fun j : Fin m ↦ y m j) (fun j : Fin m ↦ ν m j) F j := by
  let xe := encodedDecompositionVector D y
  let μe := encodedDecompositionMeasure ν
  let hμe : ∀ q, HasSpectralMeasure D (xe q) (μe q) :=
    encodedDecompositionMeasure_isSpectral D B y ν hM
  let zN : ℕ → D.H := SpectralDecomposition.cyclicProjectionFamily D xe p
  have hactive (j : Fin m) : IsActiveMultiplicityIndex m j := Or.inr j.isLt
  have hzcyc (j : Fin m) : InCyclicSubspace D (y m j) (zN (Nat.pair m j)) := by
    simpa [xe, encodedDecompositionVector, Nat.unpair_pair] using
      (SpectralDecomposition.cyclicProjectionFamily_mem D xe p (Nat.pair m j))
  choose F hF using fun j : Fin m ↦
    (CyclicSpectralModel.inCyclicSubspace_iff_range D hD (y m j)
      (zN (Nat.pair m j)) (ν m j)
      (SpectralMeasure.full_moment_of_hasSpectralMeasure
        D hD (y m j) (ν m j) (hM.2.2.2.2.1 m j (hactive j)).1)).mp (hzcyc j)
  refine ⟨F, ?_⟩
  let S : Finset ℕ := Finset.univ.image (fun j : Fin m ↦ Nat.pair m j)
  have htail : ∀ q ∉ S, zN q = 0 := by
    intro q hq
    have hoff : (Nat.unpair q).1 ≠ m ∨
        ¬ IsActiveMultiplicityIndex (Nat.unpair q).1 (Nat.unpair q).2 := by
      by_cases hrm : (Nat.unpair q).1 = m
      · right
        intro hact
        rcases hact with hm0 | hjm
        · omega
        · apply hq
          apply Finset.mem_image.mpr
          refine ⟨⟨(Nat.unpair q).2, ?_⟩, Finset.mem_univ _, ?_⟩
          · simpa [hrm] using hjm
          · change Nat.pair m (Nat.unpair q).2 = q
            calc
              Nat.pair m (Nat.unpair q).2 =
                  Nat.pair (Nat.unpair q).1 (Nat.unpair q).2 := by rw [hrm]
              _ = q := Nat.pair_unpair q
      · exact Or.inl hrm
    have hcoord := encodedProjection_zero_off_stratum
      D hD B y ν hM p γ hγ m q hγsupp hoff
    have hspec := DirectSumSpectralModel.projectionCoordinate_spec
      D hD xe μe hμe p q
    rw [hcoord, map_zero] at hspec
    exact hspec.symm
  have hsum := SpectralDecomposition.tsum_cyclicProjectionFamily_eq
    D xe (encodedDecompositionVector_decomposition D hD B y ν hM) p
  calc
    p = ∑' q, zN q := hsum.symm
    _ = ∑ q ∈ S, zN q := tsum_eq_sum htail
    _ = ∑ j : Fin m, zN (Nat.pair m j) := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      have hu := congrArg Nat.unpair hij
      exact Fin.ext (by simpa [Nat.unpair_pair] using congrArg Prod.snd hu)
    _ = ∑ j, FiniteCyclicCoordinates.componentVector D hD
        (fun j : Fin m ↦ y m j) (fun j : Fin m ↦ ν m j) F j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hF j).symm

theorem spectralMeasure_stratum_zero_of_column_zero
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (p : D.H) (γ : CircleMeasureData) (hγ : HasSpectralMeasure D p γ)
    (A : Set Circle) (hγAc : γ.μ Aᶜ = 0)
    (m k : ℕ) (hmk : IsActiveMultiplicityIndex m k)
    (hcolA : (multiplicityColumnMeasure D B y ν hM k).μ A = 0) :
    γ.μ (B m) = 0 := by
  let xe := encodedDecompositionVector D y
  let μe := encodedDecompositionMeasure ν
  let hμe : ∀ q, HasSpectralMeasure D (xe q) (μe q) :=
    encodedDecompositionMeasure_isSpectral D B y ν hM
  have hsum := DirectSumMeasureCoordinates.spectralMeasure_eq_sum_projectionDensityMeasure
    D hD xe μe hμe (encodedDecompositionVector_decomposition D hD B y ν hM)
      p γ hγ
  rw [hsum, Measure.sum_apply _ (hM.1 m)]
  apply ENNReal.tsum_eq_zero.mpr
  intro q
  let ρ := DirectSumMeasureCoordinates.projectionDensityMeasure
    D hD xe μe hμe p q
  have hρac : ρ.μ ≪ (μe q).μ :=
    DirectSumMeasureCoordinates.projectionDensityMeasure_absolutelyContinuous
      D hD xe μe hμe p q
  have hρAc : ρ.μ Aᶜ = 0 := by
    exact nonpos_iff_eq_zero.mp
      ((DirectSumMeasureCoordinates.projectionDensityMeasure_le_spectralMeasure
        D hD xe μe hμe
        (encodedDecompositionVector_decomposition D hD B y ν hM)
        p γ hγ q Aᶜ).trans_eq hγAc)
  let r := (Nat.unpair q).1
  let j := (Nat.unpair q).2
  by_cases hrm : r = m
  · subst r
    by_cases hjactive : IsActiveMultiplicityIndex m j
    · have hmkA : (ν m k).μ A = 0 := by
        have hcac := MaximalSpectralType.componentMeasure_absolutelyContinuous_maximalTypeMeasure
          D (fun n ↦ y n k) (fun n ↦ completedMultiplicityMeasure ν n k)
          (fun n ↦ completedMultiplicityMeasure_isSpectral D B y ν hM n k) m
        have := hcac hcolA
        simpa [completedMultiplicityMeasure, hmk] using this
      have heq := hM.2.2.2.2.2.1 m k j hmk hjactive
      have hself : ν m j ∈ SpectralTypeDefinition (ν m j) :=
        ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
      have hjk : (ν m j).μ ≪ (ν m k).μ := by
        have hmemb : ν m j ∈ SpectralTypeDefinition (ν m k) := by
          rw [heq]
          exact hself
        exact hmemb.1
      have hbaseA : (μe q).μ A = 0 := by
        simpa [μe, encodedDecompositionMeasure, completedMultiplicityMeasure,
          j, hrm, hjactive] using hjk hmkA
      have hρA : ρ.μ A = 0 := hρac hbaseA
      apply le_antisymm
      · calc
          ρ.μ (B m) ≤ ρ.μ (A ∪ Aᶜ) := measure_mono (by intro z hz; simp)
          _ ≤ ρ.μ A + ρ.μ Aᶜ := measure_union_le _ _
          _ = 0 := by rw [hρA, hρAc, add_zero]
      · exact bot_le
    · exact hρac (by
        simpa [μe, encodedDecompositionMeasure, j, hrm] using
          (completedMultiplicityMeasure_otherStratum_zero D B y ν hM
            m m j (Or.inr hjactive)))
  · exact hρac (by
      apply completedMultiplicityMeasure_otherStratum_zero D B y ν hM
        m r j
      exact Or.inl hrm)

theorem ordered_component_ac_multiplicityColumnMeasure
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (k : ℕ) :
    (μ k).μ ≪ (multiplicityColumnMeasure D B y ν hM k).μ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hcolA
  by_contra hμkA
  let β := OrderedSpectralUniqueness.restrictedCircleMeasure (μ k) A
  have hβacK : β.μ ≪ (μ k).μ :=
    OrderedSpectralUniqueness.restrictedCircleMeasure_absolutelyContinuous _ _
  have hβac (i : Fin (k + 1)) : β.μ ≪ (μ i).μ := by
    have hik : (i : ℕ) ≤ k := Nat.le_of_lt_succ i.isLt
    exact hβacK.trans
      (OrderedSpectralDecomposition.component_dominates_later
        D hD x hord.2 hik (μ i) (μ k) (hμ i) (hμ k))
  choose p hpcyc hpβ using fun i : Fin (k + 1) ↦
    SpectralRelations.exists_cyclic_vector_with_ac_measure
      D hD (x i) (μ i) β (hμ i) (hβac i)
  have hpOrth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (p i) (p j) := by
    intro i j hij a b ha hb
    have hijNat : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (Fin.ext h)
    exact hord.1.1 i j hijNat a b
      (ha _ (SpectralDecomposition.cyclicSubmodule_reducing D (x i)) (hpcyc i))
      (hb _ (SpectralDecomposition.cyclicSubmodule_reducing D (x j)) (hpcyc j))
  have hβuniv : β.μ Set.univ ≠ 0 := by
    change (μ k).μ.restrict A Set.univ ≠ 0
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hμkA
  have hβAc : β.μ Aᶜ = 0 := by
    change (μ k).μ.restrict A Aᶜ = 0
    rw [Measure.restrict_apply hA.compl]
    simp
  have hactiveZero (m : ℕ) (hmk : IsActiveMultiplicityIndex m k) :
      β.μ (B m) = 0 :=
    spectralMeasure_stratum_zero_of_column_zero
      D hD B y ν hM (p 0) β (hpβ 0) A hβAc m k hmk hcolA
  have hex : ∃ m : ℕ, 0 < m ∧ m ≤ k ∧ β.μ (B m) ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    have hall : ∀ m, β.μ (B m) = 0 := by
      intro m
      by_cases hmk : IsActiveMultiplicityIndex m k
      · exact hactiveZero m hmk
      · have hm0 : 0 < m := by
          rcases m with _ | m
          · exact (hmk (Or.inl rfl)).elim
          · omega
        have hmk' : m ≤ k := by
          unfold IsActiveMultiplicityIndex at hmk
          push_neg at hmk
          exact hmk.2
        exact hnone m hm0 hmk'
    have hunion : β.μ (⋃ m, B m) = 0 := measure_iUnion_null hall
    rw [hM.2.2.1] at hunion
    exact hβuniv hunion
  obtain ⟨m, hm, hmk, hβBm⟩ := hex
  let γ := OrderedSpectralUniqueness.restrictedCircleMeasure β (B m)
  have hγacβ : γ.μ ≪ β.μ :=
    OrderedSpectralUniqueness.restrictedCircleMeasure_absolutelyContinuous _ _
  choose r hrcyc hrγ using fun i : Fin (k + 1) ↦
    SpectralRelations.exists_cyclic_vector_with_ac_measure
      D hD (p i) β γ (hpβ i) hγacβ
  have hrOrth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (r i) (r j) := by
    intro i j hij a b ha hb
    exact hpOrth i j hij a b
      (ha _ (SpectralDecomposition.cyclicSubmodule_reducing D (p i)) (hrcyc i))
      (hb _ (SpectralDecomposition.cyclicSubmodule_reducing D (p j)) (hrcyc j))
  have hγuniv : γ.μ Set.univ ≠ 0 := by
    change β.μ.restrict (B m) Set.univ ≠ 0
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hβBm
  have hγsupp : γ.μ (B m)ᶜ = 0 := by
    change β.μ.restrict (B m) (B m)ᶜ = 0
    rw [Measure.restrict_apply (hM.1 m).compl]
    simp
  choose F hF using fun i : Fin (k + 1) ↦
    exists_finite_stratum_coordinates D hD B y ν hM
      (r i) γ (hrγ i) m hm hγsupp
  let liftIndex : Fin (m + 1) → Fin (k + 1) := fun i ↦
    ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hmk)⟩
  let a : Fin m → D.H := fun j ↦ y m j
  let μa : Fin m → CircleMeasureData := fun j ↦ ν m j
  have haSpec (j : Fin m) : HasSpectralMeasure D (a j) (μa j) :=
    (hM.2.2.2.2.1 m j (Or.inr j.isLt)).1
  have haOrth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (a i) (a j) := by
    intro i j hij
    apply hM.2.2.2.2.2.2.1 m i m j
    · intro hpairs
      exact hij (Fin.ext (congrArg Prod.snd hpairs))
    · exact Or.inr i.isLt
    · exact Or.inr j.isLt
  have haAC (j : Fin m) : (μa j).μ ≪ (μa ⟨0, hm⟩).μ := by
    have heq := hM.2.2.2.2.2.1 m 0 j (Or.inr hm) (Or.inr j.isLt)
    have hself : ν m j ∈ SpectralTypeDefinition (ν m j) :=
      ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
    have hmemb : ν m j ∈ SpectralTypeDefinition (ν m 0) := by
      rw [heq]
      exact hself
    exact hmemb.1
  have hγacBase : γ.μ ≪ (μa ⟨0, hm⟩).μ := by
    let i0 : Fin (k + 1) := liftIndex 0
    have hcoord := FiniteCyclicCoordinates.coordinateMeasure_isSpectral
      D hD a μa haSpec haOrth (F i0)
    have hcoord' : HasSpectralMeasure D (r i0)
        (FiniteCyclicCoordinates.coordinateMeasure μa (F i0)) := by
      rw [hF i0]
      exact hcoord
    have heq : γ = FiniteCyclicCoordinates.coordinateMeasure μa (F i0) :=
      SpectralMeasure.eq_of_nat_moments _ _ fun t ↦
        (hrγ i0 t).trans (hcoord' t).symm
    rw [heq]
    refine Measure.AbsolutelyContinuous.mk ?_
    intro s hs hbase
    change (∑ j, (CyclicMeasureType.vectorDensityMeasure (F i0 j)).μ) s = 0
    rw [FiniteCyclicCoordinates.finsetSumMeasure_apply]
    apply Finset.sum_eq_zero
    intro j hj
    exact CyclicMeasureType.vectorDensityMeasure_absolutelyContinuous (F i0 j)
      (haAC j hbase)
  let p' : Fin (m + 1) → D.H := fun i ↦ r (liftIndex i)
  let F' : ∀ i : Fin (m + 1), ∀ j : Fin m, Lp ℂ 2 (μa j).μ :=
    fun i ↦ F (liftIndex i)
  exact FiniteCyclicCoordinates.no_overfull_finite_cyclic_coordinates
    D hD hm a μa haSpec haOrth haAC p' γ F'
    (fun i ↦ hF (liftIndex i)) (fun i ↦ hrγ (liftIndex i))
    hγuniv hγacBase (fun i j hij ↦ hrOrth (liftIndex i) (liftIndex j)
      (fun h ↦ hij (Fin.ext (by
        have hv := congrArg (fun z : Fin (k + 1) ↦ (z : ℕ)) h
        exact hv))))

theorem multiplicityColumnMeasure_inactiveStratum_zero
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k : ℕ) (hinactive : ¬ IsActiveMultiplicityIndex n k) :
    (multiplicityColumnMeasure D B y ν hM k).μ (B n) = 0 := by
  change Measure.sum
      (MaximalSpectralType.weightedComponentMeasure D
        (fun m ↦ y m k) (fun m ↦ completedMultiplicityMeasure ν m k)) (B n) = 0
  rw [Measure.sum_apply _ (hM.1 n)]
  apply ENNReal.tsum_eq_zero.mpr
  intro m
  by_cases hmactive : IsActiveMultiplicityIndex m k
  · have hmn : m ≠ n := by
      intro hmn
      subst m
      exact hinactive hmactive
    have hbase : (completedMultiplicityMeasure ν m k).μ (B n) = 0 :=
      completedMultiplicityMeasure_otherStratum_zero D B y ν hM
        n m k (Or.inl hmn)
    rw [MaximalSpectralType.weightedComponentMeasure,
      Measure.smul_apply, smul_eq_mul, hbase, mul_zero]
  · simp [MaximalSpectralType.weightedComponentMeasure,
      completedMultiplicityMeasure, hmactive, zeroCircleMeasure]

theorem active_arbitrary_component_ac_ordered_component
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k l : ℕ) (hnk : IsActiveMultiplicityIndex n k)
    (hnl : IsActiveMultiplicityIndex n l) :
    (ν n k).μ ≪ (μ l).μ := by
  have heq := hM.2.2.2.2.2.1 n k l hnk hnl
  have hself : ν n k ∈ SpectralTypeDefinition (ν n k) :=
    ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
  have hkl : (ν n k).μ ≪ (ν n l).μ := by
    have hm : ν n k ∈ SpectralTypeDefinition (ν n l) := by
      rw [← heq]
      exact hself
    exact hm.1
  have hlcol : (ν n l).μ ≪
      (multiplicityColumnMeasure D B y ν hM l).μ := by
    have hcac := MaximalSpectralType.componentMeasure_absolutelyContinuous_maximalTypeMeasure
      D (fun m ↦ y m l) (fun m ↦ completedMultiplicityMeasure ν m l)
      (fun m ↦ completedMultiplicityMeasure_isSpectral D B y ν hM m l) n
    simpa [completedMultiplicityMeasure, hnl] using hcac
  exact hkl.trans (hlcol.trans
    (multiplicityColumnMeasure_ac_ordered_component
      D hD x μ hμ hord B y ν hM l))

theorem ordered_component_zero_on_inactive_arbitraryStratum
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n l : ℕ) (hinactive : ¬ IsActiveMultiplicityIndex n l) :
    (μ l).μ (B n) = 0 := by
  exact ordered_component_ac_multiplicityColumnMeasure
    D hD x μ hμ hord B y ν hM l
    (multiplicityColumnMeasure_inactiveStratum_zero D B y ν hM n l hinactive)

theorem base_inter_spectralSupport_zero_of_measure_zero
    (R S : CircleMeasureData) (hSR : S.μ ≪ R.μ)
    (A : Set Circle) (hzero : S.μ A = 0) :
    R.μ (A ∩ OrderedMultiplicitySupports.spectralSupport R S) = 0 := by
  have hdensityZero : R.μ
      ({z | S.μ.rnDeriv R.μ z ≠ 0} ∩ A) = 0 := by
    apply (withDensity_apply_eq_zero'
      (Measure.measurable_rnDeriv S.μ R.μ).aemeasurable).1
    rw [Measure.withDensity_rnDeriv_eq S.μ R.μ hSR]
    exact hzero
  simpa [OrderedMultiplicitySupports.spectralSupport, Set.inter_comm] using hdensityZero

theorem arbitrary_component_compl_nestedSupport_zero_of_active
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k l : ℕ) (hnk : IsActiveMultiplicityIndex n k)
    (hnl : IsActiveMultiplicityIndex n l) :
    (ν n k).μ (OrderedMultiplicitySupports.nestedSupport μ l)ᶜ = 0 := by
  exact active_arbitrary_component_ac_ordered_component
    D hD x μ hμ hord B y ν hM n k l hnk hnl
    (OrderedMultiplicitySupports.componentMeasure_compl_nestedSupport_zero
      D hD x μ hμ hord.2 l)

theorem arbitrary_component_nestedSupport_zero_of_inactive
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k l : ℕ) (hnk : IsActiveMultiplicityIndex n k)
    (hnl : ¬ IsActiveMultiplicityIndex n l) :
    (ν n k).μ (OrderedMultiplicitySupports.nestedSupport μ l) = 0 := by
  have hνbase : (ν n k).μ ≪ (μ 0).μ :=
    active_arbitrary_component_ac_ordered_component
      D hD x μ hμ hord B y ν hM n k 0 hnk (by
        unfold IsActiveMultiplicityIndex
        omega)
  have hμlbase : (μ l).μ ≪ (μ 0).μ :=
    OrderedSpectralDecomposition.component_dominates_later
      D hD x hord.2 (Nat.zero_le l) (μ 0) (μ l) (hμ 0) (hμ l)
  have hbaseInter : (μ 0).μ
      (B n ∩ OrderedMultiplicitySupports.spectralSupport (μ 0) (μ l)) = 0 :=
    base_inter_spectralSupport_zero_of_measure_zero (μ 0) (μ l) hμlbase
      (B n)
      (ordered_component_zero_on_inactive_arbitraryStratum
        D hD x μ hμ hord B y ν hM n l hnl)
  have hνInter : (ν n k).μ
      (B n ∩ OrderedMultiplicitySupports.spectralSupport (μ 0) (μ l)) = 0 :=
    hνbase hbaseInter
  have hνOutside : (ν n k).μ (B n)ᶜ = 0 := (hM.2.2.2.2.1 n k hnk).2
  apply measure_mono_null (t :=
      (B n ∩ OrderedMultiplicitySupports.spectralSupport (μ 0) (μ l)) ∪ (B n)ᶜ)
  · intro z hz
    by_cases hzB : z ∈ B n
    · exact Or.inl ⟨hzB,
        OrderedMultiplicitySupports.nestedSupport_subset_spectralSupport μ l hz⟩
    · exact Or.inr hzB
  · exact measure_union_null hνInter hνOutside

theorem arbitrary_component_supported_on_canonical_stratum
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k : ℕ) (hnk : IsActiveMultiplicityIndex n k) :
    (ν n k).μ
      (OrderedMultiplicitySupports.multiplicityStratum μ n)ᶜ = 0 := by
  let T := OrderedMultiplicitySupports.nestedSupport μ
  rcases n with _ | _ | n
  · change (ν 0 k).μ (MultiplicityStrata.noExitSet T)ᶜ = 0
    rw [MultiplicityStrata.noExitSet, compl_iInter]
    apply measure_iUnion_null
    intro l
    exact arbitrary_component_compl_nestedSupport_zero_of_active
      D hD x μ hμ hord B y ν hM 0 k l hnk (Or.inl rfl)
  · have hT1 : (ν 1 k).μ (T 1) = 0 :=
      arbitrary_component_nestedSupport_zero_of_inactive
        D hD x μ hμ hord B y ν hM 1 k 1 hnk (by
          unfold IsActiveMultiplicityIndex
          omega)
    apply measure_mono_null (t := T 1)
    · intro z hz
      change z ∉ MultiplicityStrata.exitSet T 0 ∪
        MultiplicityStrata.exitSet T 1 at hz
      by_contra hzT1
      by_cases hzT0 : z ∈ T 0
      · apply hz
        exact Or.inr ⟨hzT1, Set.mem_iInter.2 fun j ↦ by
          have hj0 : (j : ℕ) = 0 := by omega
          simpa [hj0] using hzT0⟩
      · apply hz
        exact Or.inl ⟨hzT0, Set.mem_iInter.2 fun j ↦ (by omega)⟩
    · exact hT1
  · have hTn : (ν (n + 2) k).μ (T (n + 2)) = 0 :=
      arbitrary_component_nestedSupport_zero_of_inactive
        D hD x μ hμ hord B y ν hM (n + 2) k (n + 2) hnk (by
          unfold IsActiveMultiplicityIndex
          omega)
    apply measure_mono_null (t :=
        T (n + 2) ∪ ⋃ j : {j // j < n + 2}, (T j)ᶜ)
    · intro z hz
      change z ∉ MultiplicityStrata.exitSet T (n + 2) at hz
      by_cases hzT : z ∈ T (n + 2)
      · exact Or.inl hzT
      · have hnotAll : z ∉ ⋂ j : {j // j < n + 2}, T j := by
          intro hall
          exact hz ⟨hzT, hall⟩
        rw [Set.mem_iInter] at hnotAll
        push_neg at hnotAll
        obtain ⟨j, hj⟩ := hnotAll
        exact Or.inr (Set.mem_iUnion.2 ⟨j, hj⟩)
    · apply measure_union_null hTn
      apply measure_iUnion_null
      intro j
      exact arbitrary_component_compl_nestedSupport_zero_of_active
        D hD x μ hμ hord B y ν hM (n + 2) k j hnk (by
          unfold IsActiveMultiplicityIndex
          exact Or.inr j.property)

theorem absolutelyContinuous_restrict_of_supported
    {X : Type*} [MeasurableSpace X] {ρ σ : Measure X} {A : Set X}
    (hρσ : ρ ≪ σ) (hsupp : ρ Aᶜ = 0) :
    ρ ≪ σ.restrict A := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro E hE hzero
  rw [Measure.restrict_apply hE] at hzero
  have hin : ρ (E ∩ A) = 0 := hρσ hzero
  apply measure_mono_null (t := (E ∩ A) ∪ Aᶜ)
  · intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inl ⟨hz, hzA⟩
    · exact Or.inr hzA
  · exact measure_union_null hin hsupp

theorem arbitrary_component_ac_canonical_restrictedMeasure
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k : ℕ) (hnk : IsActiveMultiplicityIndex n k) :
    (ν n k).μ ≪
      (OrderedMultiplicitySupports.restrictedComponentMeasure μ n k).μ := by
  exact absolutelyContinuous_restrict_of_supported
    (active_arbitrary_component_ac_ordered_component
      D hD x μ hμ hord B y ν hM n k k hnk hnk)
    (arbitrary_component_supported_on_canonical_stratum
      D hD x μ hμ hord B y ν hM n k hnk)

theorem multiplicityColumn_restrict_canonicalStratum_ac_component
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k : ℕ) (hnk : IsActiveMultiplicityIndex n k) :
    (multiplicityColumnMeasure D B y ν hM k).μ.restrict
        (OrderedMultiplicitySupports.multiplicityStratum μ n) ≪ (ν n k).μ := by
  let C := OrderedMultiplicitySupports.multiplicityStratum μ n
  have hC : MeasurableSet C :=
    OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hνA
  rw [Measure.restrict_apply hA]
  change Measure.sum
      (MaximalSpectralType.weightedComponentMeasure D
        (fun m ↦ y m k) (fun m ↦ completedMultiplicityMeasure ν m k))
      (A ∩ C) = 0
  rw [Measure.sum_apply _ (hA.inter hC)]
  apply ENNReal.tsum_eq_zero.mpr
  intro m
  by_cases hmactive : IsActiveMultiplicityIndex m k
  · have hmcomp : (completedMultiplicityMeasure ν m k).μ (A ∩ C) = 0 := by
      by_cases hmn : m = n
      · subst m
        simpa [completedMultiplicityMeasure, hnk] using
          (measure_mono_null Set.inter_subset_left hνA)
      · have hdisj := OrderedMultiplicitySupports.multiplicityStrata_pairwise_disjoint
          μ n m (Ne.symm hmn)
        apply measure_mono_null
          (t := (OrderedMultiplicitySupports.multiplicityStratum μ m)ᶜ)
        · intro z hz hzm
          exact Set.disjoint_left.1 hdisj hz.2 hzm
        · simpa [completedMultiplicityMeasure, hmactive] using
            (arbitrary_component_supported_on_canonical_stratum
              D hD x μ hμ hord B y ν hM m k hmactive)
    rw [MaximalSpectralType.weightedComponentMeasure,
      Measure.smul_apply, smul_eq_mul, hmcomp, mul_zero]
  · simp [MaximalSpectralType.weightedComponentMeasure,
      completedMultiplicityMeasure, hmactive, zeroCircleMeasure]

theorem canonical_restrictedMeasure_ac_arbitrary_component
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k : ℕ) (hnk : IsActiveMultiplicityIndex n k) :
    (OrderedMultiplicitySupports.restrictedComponentMeasure μ n k).μ ≪
      (ν n k).μ := by
  have hkcol : (μ k).μ ≪ (multiplicityColumnMeasure D B y ν hM k).μ :=
    ordered_component_ac_multiplicityColumnMeasure
      D hD x μ hμ hord B y ν hM k
  exact (OrderedMultiplicitySupports.restrict_absolutelyContinuous_restrict
      (OrderedMultiplicitySupports.measurableSet_multiplicityStratum μ n) hkcol).trans
    (multiplicityColumn_restrict_canonicalStratum_ac_component
      D hD x μ hμ hord B y ν hM n k hnk)

theorem equivalentVectors_of_spectralMeasures_mutual_ac
    (D : HilbertOperatorData.{u}) {a b : D.H}
    (R S : CircleMeasureData)
    (ha : HasSpectralMeasure D a R) (hb : HasSpectralMeasure D b S)
    (hRS : R.μ ≪ S.μ) (hSR : S.μ ≪ R.μ) :
    SpectralMeasureEquivalentVectors D a b := by
  constructor
  · intro R' S' ha' hb'
    have hReq : R' = R := SpectralMeasure.eq_of_nat_moments _ _ fun t ↦
      (ha' t).trans (ha t).symm
    have hSeq : S' = S := SpectralMeasure.eq_of_nat_moments _ _ fun t ↦
      (hb' t).trans (hb t).symm
    simpa [hReq, hSeq] using hSR
  · intro S' R' hb' ha'
    have hSeq : S' = S := SpectralMeasure.eq_of_nat_moments _ _ fun t ↦
      (hb' t).trans (hb t).symm
    have hReq : R' = R := SpectralMeasure.eq_of_nat_moments _ _ fun t ↦
      (ha' t).trans (ha t).symm
    simpa [hReq, hSeq] using hRS

theorem canonical_multiplicity_decomposition_unique
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : IsOrderedSpectralDecomposition D x)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (n k : ℕ) (hnk : IsActiveMultiplicityIndex n k) :
    SpectralMeasureEquivalentVectors D
      (multiplicityVector D hD x μ hμ n k) (y n k) := by
  exact equivalentVectors_of_spectralMeasures_mutual_ac D
    (multiplicityMeasure μ n k) (ν n k)
    (multiplicityVector_active_spec D hD x μ hμ n k hnk).1
    (hM.2.2.2.2.1 n k hnk).1
    (canonical_restrictedMeasure_ac_arbitrary_component
      D hD x μ hμ hord B y ν hM n k hnk)
    (arbitrary_component_ac_canonical_restrictedMeasure
      D hD x μ hμ hord B y ν hM n k hnk)

end Chapter02.OrderedMultiplicityDecomposition
