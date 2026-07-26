import Chapter02.Spectral.OrderedMultiplicityDecomposition
import Chapter02.Spectral.HilbertDirectSum

open Classical Filter Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace Chapter02.SpectralClassification

universe u

def witnessEquiv {D E : HilbertOperatorData.{u}} (W : D.H → E.H)
    (hbij : Function.Bijective W)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖) : D.H ≃ₗᵢ[ℂ] E.H :=
  LinearIsometryEquiv.ofSurjective
    ({ toLinearMap :=
        { toFun := W
          map_add' := hadd
          map_smul' := hsmul }
       norm_map' := hnorm } : D.H →ₗᵢ[ℂ] E.H) hbij.2

@[simp] theorem witnessEquiv_apply {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H) (hbij hadd hsmul hnorm) (x : D.H) :
    witnessEquiv W hbij hadd hsmul hnorm x = W x := rfl

theorem witness_zero {D E : HilbertOperatorData.{u}} (W : D.H → E.H)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x) : W 0 = 0 := by
  have h := hsmul 0 0
  simpa using h

theorem witness_sub {D E : HilbertOperatorData.{u}} (W : D.H → E.H)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (x y : D.H) : W (x - y) = W x - W y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, hadd]
  have h := hsmul (-1) y
  simpa using h

theorem witness_finset_sum {D E : HilbertOperatorData.{u}} (W : D.H → E.H)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    {I : Type*} (s : Finset I) (z : I → D.H) :
    W (∑ i ∈ s, z i) = ∑ i ∈ s, W (z i) := by
  induction s using Finset.induction_on with
  | empty => simp [witness_zero W hsmul]
  | @insert i s hi ih => simp [hi, hadd, ih]

theorem witness_iterate {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H) (hinter : ∀ x, W (D.U x) = E.U (W x))
    (n : ℕ) (x : D.H) : W ((D.U^[n]) x) = (E.U^[n]) (W x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hinter, ih]

theorem transport_hasSpectralMeasure {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H) (hbij : Function.Bijective W)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hinter : ∀ x, W (D.U x) = E.U (W x))
    {x : D.H} {μ : CircleMeasureData} (hμ : HasSpectralMeasure D x μ) :
    HasSpectralMeasure E (W x) μ := by
  intro n
  rw [hμ n, ← witness_iterate W hinter n x]
  exact ((witnessEquiv W hbij hadd hsmul hnorm).inner_map_map
    x ((D.U^[n]) x)).symm

theorem preimage_reducing {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hinter : ∀ x, W (D.U x) = E.U (W x))
    (K : Set E.H) (hK : IsClosedReducingSubspace E K) :
    IsClosedReducingSubspace D (W ⁻¹' K) := by
  have hW0 : W 0 = 0 := witness_zero W hsmul
  refine ⟨by simpa [hW0] using hK.1, ?_, ?_, ?_⟩
  · intro x hx y hy a b
    change W (a • x + b • y) ∈ K
    rw [hadd, hsmul, hsmul]
    exact hK.2.1 (W x) hx (W y) hy a b
  · intro v hv x hlim
    apply hK.2.2.1 (fun n ↦ W (v n)) (fun n ↦ hv n) (W x)
    exact (tendsto_iff_norm_sub_tendsto_zero).2 (by
      have hvlim := (tendsto_iff_norm_sub_tendsto_zero).1 hlim
      apply hvlim.congr'
      filter_upwards with n
      rw [← witness_sub W hadd hsmul]
      exact (hnorm (v n - x)).symm)
  · intro x
    change W x ∈ K ↔ W (D.U x) ∈ K
    rw [hinter]
    exact hK.2.2.2 (W x)

theorem transport_inCyclicSubspace {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hinter : ∀ x, W (D.U x) = E.U (W x))
    {x y : D.H} (hy : InCyclicSubspace D x y) :
    InCyclicSubspace E (W x) (W y) := by
  intro K hK hx
  exact hy (W ⁻¹' K) (preimage_reducing W hadd hsmul hnorm hinter K hK) hx

theorem reflect_inCyclicSubspace {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H) (hbij : Function.Bijective W)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hinter : ∀ x, W (D.U x) = E.U (W x))
    {x y : D.H} (hy : InCyclicSubspace E (W x) (W y)) :
    InCyclicSubspace D x y := by
  let L := witnessEquiv W hbij hadd hsmul hnorm
  let V : E.H → D.H := fun z ↦ L.symm z
  have hVbij : Function.Bijective V := L.symm.bijective
  have hVadd : ∀ a b, V (a + b) = V a + V b := fun a b ↦ L.symm.map_add a b
  have hVsmul : ∀ c : ℂ, ∀ a, V (c • a) = c • V a :=
    fun c a ↦ L.symm.map_smul c a
  have hVnorm : ∀ a, ‖V a‖ = ‖a‖ := fun a ↦ L.symm.norm_map a
  have hVW : ∀ z, V (W z) = z := by
    intro z
    change L.symm (L z) = z
    exact L.symm_apply_apply z
  have hVinter : ∀ a, V (E.U a) = D.U (V a) := by
    intro a
    obtain ⟨z, rfl⟩ := hbij.2 a
    calc
      V (E.U (W z)) = V (W (D.U z)) := congrArg V (hinter z).symm
      _ = D.U z := hVW (D.U z)
      _ = D.U (V (W z)) := congrArg D.U (hVW z).symm
  have ht := transport_inCyclicSubspace V hVadd hVsmul hVnorm hVinter hy
  change InCyclicSubspace D (V (W x)) (V (W y)) at ht
  rw [hVW x, hVW y] at ht
  exact ht

theorem transport_orthogonalCyclicSubspaces {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H) (hbij : Function.Bijective W)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hinter : ∀ x, W (D.U x) = E.U (W x))
    {x y : D.H} (hxy : OrthogonalCyclicSubspaces D x y) :
    OrthogonalCyclicSubspaces E (W x) (W y) := by
  intro a b ha hb
  obtain ⟨a', rfl⟩ := hbij.2 a
  obtain ⟨b', rfl⟩ := hbij.2 b
  change @inner ℂ E.H _
    (witnessEquiv W hbij hadd hsmul hnorm a')
    (witnessEquiv W hbij hadd hsmul hnorm b') = 0
  rw [(witnessEquiv W hbij hadd hsmul hnorm).inner_map_map]
  exact hxy a' b'
    (reflect_inCyclicSubspace W hbij hadd hsmul hnorm hinter ha)
    (reflect_inCyclicSubspace W hbij hadd hsmul hnorm hinter hb)

theorem transport_multiplicityDecomposition {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H) (hbij : Function.Bijective W)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hinter : ∀ x, W (D.U x) = E.U (W x))
    (B : ℕ → Set Circle) (x : ℕ → ℕ → D.H)
    (μ : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B x μ) :
    IsMultiplicityDecomposition E B (fun n k ↦ W (x n k)) μ := by
  have hW0 : W 0 = 0 := witness_zero W hsmul
  refine ⟨hM.1, hM.2.1, hM.2.2.1, ?_, ?_, hM.2.2.2.2.2.1, ?_, ?_⟩
  · intro n k hk
    change W (x n k) = 0
    rw [hM.2.2.2.1 n k hk, hW0]
  · intro n k hk
    exact ⟨transport_hasSpectralMeasure W hbij hadd hsmul hnorm hinter
      (hM.2.2.2.2.1 n k hk).1, (hM.2.2.2.2.1 n k hk).2⟩
  · intro n i m j hne hni hmj
    exact transport_orthogonalCyclicSubspaces W hbij hadd hsmul hnorm hinter
      (hM.2.2.2.2.2.2.1 n i m j hne hni hmj)
  · intro y ε hε
    obtain ⟨y', rfl⟩ := hbij.2 y
    obtain ⟨s, z, hz, hclose⟩ := hM.2.2.2.2.2.2.2 y' ε hε
    refine ⟨s, fun p ↦ W (z p), ?_, ?_⟩
    · intro p hp
      exact ⟨(hz p hp).1,
        transport_inCyclicSubspace W hadd hsmul hnorm hinter (hz p hp).2⟩
    · have hsum : W (∑ p ∈ s, z p) = ∑ p ∈ s, W (z p) :=
        witness_finset_sum W hadd hsmul s z
      rw [← hsum]
      rw [← witness_sub W hadd hsmul]
      rw [hnorm]
      exact hclose

theorem transport_spectralMultiplicityData {D E : HilbertOperatorData.{u}}
    (W : D.H → E.H) (hbij : Function.Bijective W)
    (hadd : ∀ x y, W (x + y) = W x + W y)
    (hsmul : ∀ c : ℂ, ∀ x, W (c • x) = c • W x)
    (hnorm : ∀ x, ‖W x‖ = ‖x‖)
    (hinter : ∀ x, W (D.U x) = E.U (W x))
    {μmax : CircleMeasureData} {mult : Circle → ENNReal}
    (hdata : HasSpectralMultiplicityData D μmax mult) :
    HasSpectralMultiplicityData E μmax mult := by
  rcases hdata with ⟨hmax, hmeas, B, x, μ, hM, hmult⟩
  refine ⟨?_, hmeas, B, (fun n k ↦ W (x n k)), μ, ?_, hmult⟩
  · rcases hmax with ⟨hD, ⟨v, hv⟩, hdom⟩
    refine ⟨?_, ⟨W v, transport_hasSpectralMeasure W hbij hadd hsmul hnorm hinter hv⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro y
        obtain ⟨x, rfl⟩ := hbij.2 y
        obtain ⟨z, hz⟩ := hD.1 x
        refine ⟨W z, ?_⟩
        rw [← hinter, hz]
      · intro y
        obtain ⟨x, rfl⟩ := hbij.2 y
        rw [← hinter, hnorm, hD.2, hnorm]
    · intro y
      obtain ⟨x, rfl⟩ := hbij.2 y
      obtain ⟨ν, hν, hνac⟩ := hdom x
      exact ⟨ν, transport_hasSpectralMeasure W hbij hadd hsmul hnorm hinter hν, hνac⟩
  · exact transport_multiplicityDecomposition
      W hbij hadd hsmul hnorm hinter B x μ hM

theorem forward_invariants {D E : HilbertOperatorData.{u}}
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (hde : UnitarilyEquivalent D E) :
    ∃ μD μE : CircleMeasureData,
      ∃ multiplicityD multiplicityE : Circle → ENNReal,
        HasSpectralMultiplicityData D μD multiplicityD ∧
        HasSpectralMultiplicityData E μE multiplicityE ∧
        μD.μ ≪ μE.μ ∧ μE.μ ≪ μD.μ ∧
        multiplicityD =ᵐ[μD.μ] multiplicityE := by
  rcases hde with ⟨W, hbij, hadd, hsmul, hnorm, hinter⟩
  obtain ⟨μmax, mult, hdata⟩ :=
    OrderedMultiplicityDecomposition.exists_spectralMultiplicityData D hsep hD
  exact ⟨μmax, μmax, mult, mult, hdata,
    transport_spectralMultiplicityData W hbij hadd hsmul hnorm hinter hdata,
    Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl,
    Filter.Eventually.of_forall fun _ ↦ rfl⟩

theorem maximalSpectralMeasures_mutual_ac
    (D : HilbertOperatorData.{u})
    {R S : CircleMeasureData}
    (hR : IsMaximalSpectralMeasure D R)
    (hS : IsMaximalSpectralMeasure D S) : R.μ ≪ S.μ ∧ S.μ ≪ R.μ := by
  rcases hR.2.1 with ⟨x, hxR⟩
  rcases hS.2.2 x with ⟨Rx, hxRx, hRxS⟩
  have hRx : Rx = R := SpectralMeasure.eq_of_nat_moments _ _ fun n ↦
    (hxRx n).trans (hxR n).symm
  rcases hS.2.1 with ⟨y, hyS⟩
  rcases hR.2.2 y with ⟨Sy, hySy, hSyR⟩
  have hSy : Sy = S := SpectralMeasure.eq_of_nat_moments _ _ fun n ↦
    (hySy n).trans (hyS n).symm
  exact ⟨by simpa [hRx] using hRxS, by simpa [hSy] using hSyR⟩

theorem column_zero_mutual_ac_maximalMeasure
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (μmax : CircleMeasureData) (hmax : IsMaximalSpectralMeasure D μmax) :
    (OrderedMultiplicityDecomposition.multiplicityColumnMeasure
        D B y ν hM 0).μ ≪ μmax.μ ∧
      μmax.μ ≪
        (OrderedMultiplicityDecomposition.multiplicityColumnMeasure
          D B y ν hM 0).μ := by
  obtain ⟨x, hx⟩ :=
    OrderedSpectralDecomposition.exists_orderedSpectralDecomposition D hsep hD
  choose μ hμ _ using fun n ↦ SpectralMeasure.spectralMeasure D hD (x n)
  have hμ0max :=
    (OrderedMultiplicityDecomposition.hasSpectralMultiplicityData_of_ordered
      D hD x μ hμ hx).1
  obtain ⟨hμmax, hmaxμ⟩ := maximalSpectralMeasures_mutual_ac D hμ0max hmax
  exact ⟨
    (OrderedMultiplicityDecomposition.multiplicityColumnMeasure_ac_ordered_component
      D hD x μ hμ hx B y ν hM 0).trans hμmax,
    hmaxμ.trans
      (OrderedMultiplicityDecomposition.ordered_component_ac_multiplicityColumnMeasure
        D hD x μ hμ hx B y ν hM 0)⟩

theorem column_zero_restrict_stratum_ac_component
    (D : HilbertOperatorData.{u})
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν) (n : ℕ) :
    (OrderedMultiplicityDecomposition.multiplicityColumnMeasure
      D B y ν hM 0).μ.restrict (B n) ≪ (ν n 0).μ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hνA
  rw [Measure.restrict_apply hA]
  change Measure.sum
      (MaximalSpectralType.weightedComponentMeasure D
        (fun m ↦ y m 0)
        (fun m ↦ OrderedMultiplicityDecomposition.completedMultiplicityMeasure ν m 0))
      (A ∩ B n) = 0
  rw [Measure.sum_apply _ (hA.inter (hM.1 n))]
  apply ENNReal.tsum_eq_zero.mpr
  intro m
  have hmactive : IsActiveMultiplicityIndex m 0 := by
    unfold IsActiveMultiplicityIndex
    omega
  have hmzero :
      (OrderedMultiplicityDecomposition.completedMultiplicityMeasure ν m 0).μ
        (A ∩ B n) = 0 := by
    by_cases hmn : m = n
    · subst m
      simpa [OrderedMultiplicityDecomposition.completedMultiplicityMeasure, hmactive] using
        (measure_mono_null Set.inter_subset_left hνA)
    · apply measure_mono_null (t := (B m)ᶜ)
      · intro z hz hzm
        exact Set.disjoint_left.1 (hM.2.1 n m (Ne.symm hmn)) hz.2 hzm
      · simpa [OrderedMultiplicityDecomposition.completedMultiplicityMeasure, hmactive] using
          (hM.2.2.2.2.1 m 0 hmactive).2
  rw [MaximalSpectralType.weightedComponentMeasure,
    Measure.smul_apply, smul_eq_mul, hmzero, mul_zero]

theorem active_component_equivalent_maximal_restriction
    (D : HilbertOperatorData.{u})
    (hsep : TopologicalSpace.SeparableSpace D.H) (hD : IsUnitary D)
    (B : ℕ → Set Circle) (y : ℕ → ℕ → D.H)
    (ν : ℕ → ℕ → CircleMeasureData)
    (hM : IsMultiplicityDecomposition D B y ν)
    (μmax : CircleMeasureData) (hmax : IsMaximalSpectralMeasure D μmax)
    (n k : ℕ) (hnk : IsActiveMultiplicityIndex n k) :
    (ν n k).μ ≪ μmax.μ.restrict (B n) ∧
      μmax.μ.restrict (B n) ≪ (ν n k).μ := by
  have hn0 : IsActiveMultiplicityIndex n 0 := by
    unfold IsActiveMultiplicityIndex
    omega
  have heq := hM.2.2.2.2.2.1 n k 0 hnk hn0
  have hnk0 : (ν n k).μ ≪ (ν n 0).μ ∧ (ν n 0).μ ≪ (ν n k).μ := by
    constructor
    · have hself : ν n k ∈ SpectralTypeDefinition (ν n k) :=
        ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
      have hm : ν n k ∈ SpectralTypeDefinition (ν n 0) := by
        rw [← heq]
        exact hself
      exact hm.1
    · have hself : ν n 0 ∈ SpectralTypeDefinition (ν n 0) :=
        ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
      have hm : ν n 0 ∈ SpectralTypeDefinition (ν n k) := by
        rw [heq]
        exact hself
      exact hm.1
  obtain ⟨hcolmax, hmaxcol⟩ :=
    column_zero_mutual_ac_maximalMeasure D hsep hD B y ν hM μmax hmax
  have hν0col : (ν n 0).μ ≪
      (OrderedMultiplicityDecomposition.multiplicityColumnMeasure D B y ν hM 0).μ := by
    have hc := MaximalSpectralType.componentMeasure_absolutelyContinuous_maximalTypeMeasure
      D (fun m ↦ y m 0)
      (fun m ↦ OrderedMultiplicityDecomposition.completedMultiplicityMeasure ν m 0)
      (fun m ↦ OrderedMultiplicityDecomposition.completedMultiplicityMeasure_isSpectral
        D B y ν hM m 0) n
    simpa [OrderedMultiplicityDecomposition.completedMultiplicityMeasure, hn0] using hc
  constructor
  · exact OrderedMultiplicityDecomposition.absolutelyContinuous_restrict_of_supported
      (hnk0.1.trans (hν0col.trans hcolmax)) (hM.2.2.2.2.1 n k hnk).2
  · exact (OrderedMultiplicitySupports.restrict_absolutelyContinuous_restrict
      (hM.1 n) hmaxcol).trans
        ((column_zero_restrict_stratum_ac_component D B y ν hM n).trans hnk0.2)

theorem multiplicityValue_injective :
    Function.Injective OrderedMultiplicityDecomposition.multiplicityValue := by
  intro n m h
  rcases n with _ | n <;> rcases m with _ | m
  · rfl
  · exfalso
    have h' : (⊤ : ENNReal) = (m + 1 : ℕ) := by
      simpa [OrderedMultiplicityDecomposition.multiplicityValue] using h
    exact ENNReal.natCast_ne_top (m + 1) h'.symm
  · exfalso
    have h' : ((n + 1 : ℕ) : ENNReal) = ⊤ := by
      simp [OrderedMultiplicityDecomposition.multiplicityValue] at h
    exact ENNReal.natCast_ne_top (n + 1) h'
  · congr 1
    have h' : ((n + 1 : ℕ) : ENNReal) = (m + 1 : ℕ) := by
      simpa [OrderedMultiplicityDecomposition.multiplicityValue] using h
    have hnat : n + 1 = m + 1 := by exact_mod_cast h'
    omega

theorem multiplicity_stratum_ae_subset
    {ρ σ : Measure Circle} (hρσ : ρ ≪ σ)
    (B C : ℕ → Set Circle)
    (hCunion : (⋃ m, C m) = Set.univ)
    (f g : Circle → ENNReal)
    (hf : ∀ n, ∀ᵐ z ∂ρ, z ∈ B n →
      f z = OrderedMultiplicityDecomposition.multiplicityValue n)
    (hg : ∀ m, ∀ᵐ z ∂σ, z ∈ C m →
      g z = OrderedMultiplicityDecomposition.multiplicityValue m)
    (hfg : f =ᵐ[ρ] g) (n : ℕ) : B n ≤ᶠ[ae ρ] C n := by
  have hfAll : ∀ᵐ z ∂ρ, ∀ n, z ∈ B n →
      f z = OrderedMultiplicityDecomposition.multiplicityValue n :=
    ae_all_iff.mpr hf
  have hgAllσ : ∀ᵐ z ∂σ, ∀ m, z ∈ C m →
      g z = OrderedMultiplicityDecomposition.multiplicityValue m :=
    ae_all_iff.mpr hg
  have hgAll : ∀ᵐ z ∂ρ, ∀ m, z ∈ C m →
      g z = OrderedMultiplicityDecomposition.multiplicityValue m :=
    hρσ.ae_le hgAllσ
  filter_upwards [hfAll, hgAll, hfg] with z hfz hgz hfgz
  intro hzB
  have hzUnion : z ∈ ⋃ m, C m := by
    rw [hCunion]
    exact Set.mem_univ z
  obtain ⟨m, hzC⟩ := Set.mem_iUnion.mp hzUnion
  have hval : OrderedMultiplicityDecomposition.multiplicityValue n =
      OrderedMultiplicityDecomposition.multiplicityValue m := by
    calc
      _ = f z := (hfz n hzB).symm
      _ = g z := hfgz
      _ = _ := hgz m hzC
  have hnm : n = m := multiplicityValue_injective hval
  simpa [hnm] using hzC

theorem multiplicity_strata_ae_equal
    {ρ σ : Measure Circle} (hρσ : ρ ≪ σ) (hσρ : σ ≪ ρ)
    (B C : ℕ → Set Circle)
    (hBunion : (⋃ n, B n) = Set.univ) (hCunion : (⋃ n, C n) = Set.univ)
    (f g : Circle → ENNReal)
    (hf : ∀ n, ∀ᵐ z ∂ρ, z ∈ B n →
      f z = OrderedMultiplicityDecomposition.multiplicityValue n)
    (hg : ∀ n, ∀ᵐ z ∂σ, z ∈ C n →
      g z = OrderedMultiplicityDecomposition.multiplicityValue n)
    (hfg : f =ᵐ[ρ] g) (n : ℕ) :
    ρ (B n \ C n) = 0 ∧ σ (C n \ B n) = 0 := by
  constructor
  · exact ae_le_set.mp
      (multiplicity_stratum_ae_subset hρσ B C hCunion f g hf hg hfg n)
  · have hgf : g =ᵐ[σ] f := hσρ.ae_le hfg.symm
    exact ae_le_set.mp
      (multiplicity_stratum_ae_subset hσρ C B hBunion g f hg hf hgf n)

theorem restrict_ac_restrict_of_ae_subset
    {X : Type*} [MeasurableSpace X] {ρ σ : Measure X}
    (hρσ : ρ ≪ σ) {B C : Set X} (hBC : ρ (B \ C) = 0) :
    ρ.restrict B ≪ σ.restrict C := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hzero
  rw [Measure.restrict_apply hA] at hzero ⊢
  have hAC : ρ (A ∩ C) = 0 := hρσ hzero
  apply measure_mono_null (t := (A ∩ C) ∪ (B \ C))
  · intro z hz
    by_cases hzC : z ∈ C
    · exact Or.inl ⟨hz.1, hzC⟩
    · exact Or.inr ⟨hz.2, hzC⟩
  · exact measure_union_null hAC hBC

theorem active_components_cross_mutual_ac
    (D E : HilbertOperatorData.{u})
    (hsepD : TopologicalSpace.SeparableSpace D.H)
    (hsepE : TopologicalSpace.SeparableSpace E.H)
    (hD : IsUnitary D) (hE : IsUnitary E)
    (μD μE : CircleMeasureData) (multD multE : Circle → ENNReal)
    (hdataD : HasSpectralMultiplicityData D μD multD)
    (hdataE : HasSpectralMultiplicityData E μE multE)
    (hDE : μD.μ ≪ μE.μ) (hED : μE.μ ≪ μD.μ)
    (hmult : multD =ᵐ[μD.μ] multE) :
    ∃ BD : ℕ → Set Circle, ∃ xD : ℕ → ℕ → D.H,
    ∃ νD : ℕ → ℕ → CircleMeasureData,
    ∃ BE : ℕ → Set Circle, ∃ xE : ℕ → ℕ → E.H,
    ∃ νE : ℕ → ℕ → CircleMeasureData,
      IsMultiplicityDecomposition D BD xD νD ∧
      IsMultiplicityDecomposition E BE xE νE ∧
      ∀ n k, IsActiveMultiplicityIndex n k →
        (νD n k).μ ≪ (νE n k).μ ∧ (νE n k).μ ≪ (νD n k).μ := by
  rcases hdataD with ⟨hmaxD, _hmeasD, BD, xD, νD, hMD, hmultD⟩
  rcases hdataE with ⟨hmaxE, _hmeasE, BE, xE, νE, hME, hmultE⟩
  refine ⟨BD, xD, νD, BE, xE, νE, hMD, hME, ?_⟩
  intro n k hnk
  obtain ⟨hBD_BE, hBE_BD⟩ := multiplicity_strata_ae_equal
    hDE hED BD BE hMD.2.2.1 hME.2.2.1 multD multE hmultD hmultE hmult n
  obtain ⟨hD_to_base, hbase_to_D⟩ :=
    active_component_equivalent_maximal_restriction
      D hsepD hD BD xD νD hMD μD hmaxD n k hnk
  obtain ⟨hE_to_base, hbase_to_E⟩ :=
    active_component_equivalent_maximal_restriction
      E hsepE hE BE xE νE hME μE hmaxE n k hnk
  exact ⟨
    hD_to_base.trans
      ((restrict_ac_restrict_of_ae_subset hDE hBD_BE).trans hbase_to_E),
    hE_to_base.trans
      ((restrict_ac_restrict_of_ae_subset hED hBE_BD).trans hbase_to_D)⟩

theorem encoded_components_cross_mutual_ac
    (D E : HilbertOperatorData.{u})
    (BD : ℕ → Set Circle) (xD : ℕ → ℕ → D.H)
    (νD : ℕ → ℕ → CircleMeasureData)
    (BE : ℕ → Set Circle) (xE : ℕ → ℕ → E.H)
    (νE : ℕ → ℕ → CircleMeasureData)
    (_hMD : IsMultiplicityDecomposition D BD xD νD)
    (_hME : IsMultiplicityDecomposition E BE xE νE)
    (hcross : ∀ n k, IsActiveMultiplicityIndex n k →
      (νD n k).μ ≪ (νE n k).μ ∧ (νE n k).μ ≪ (νD n k).μ)
    (q : ℕ) :
    (OrderedMultiplicityDecomposition.encodedDecompositionMeasure νD q).μ ≪
        (OrderedMultiplicityDecomposition.encodedDecompositionMeasure νE q).μ ∧
      (OrderedMultiplicityDecomposition.encodedDecompositionMeasure νE q).μ ≪
        (OrderedMultiplicityDecomposition.encodedDecompositionMeasure νD q).μ := by
  let n := (Nat.unpair q).1
  let k := (Nat.unpair q).2
  by_cases hactive : IsActiveMultiplicityIndex n k
  · simpa [OrderedMultiplicityDecomposition.encodedDecompositionMeasure,
      OrderedMultiplicityDecomposition.completedMultiplicityMeasure, n, k, hactive] using
      hcross n k hactive
  · simp [OrderedMultiplicityDecomposition.encodedDecompositionMeasure,
      OrderedMultiplicityDecomposition.completedMultiplicityMeasure, n, k, hactive,
      OrderedMultiplicityDecomposition.zeroCircleMeasure]

theorem reverse_equivalence
    (D E : HilbertOperatorData.{u})
    (hsepD : TopologicalSpace.SeparableSpace D.H)
    (hsepE : TopologicalSpace.SeparableSpace E.H)
    (hD : IsUnitary D) (hE : IsUnitary E)
    (μD μE : CircleMeasureData) (multD multE : Circle → ENNReal)
    (hdataD : HasSpectralMultiplicityData D μD multD)
    (hdataE : HasSpectralMultiplicityData E μE multE)
    (hDE : μD.μ ≪ μE.μ) (hED : μE.μ ≪ μD.μ)
    (hmult : multD =ᵐ[μD.μ] multE) :
    UnitarilyEquivalent D E := by
  obtain ⟨BD, xD, νD, BE, xE, νE, hMD, hME, hcross⟩ :=
    active_components_cross_mutual_ac D E hsepD hsepE hD hE
      μD μE multD multE hdataD hdataE hDE hED hmult
  let yD := OrderedMultiplicityDecomposition.encodedDecompositionVector D xD
  let yE := OrderedMultiplicityDecomposition.encodedDecompositionVector E xE
  let ρ := OrderedMultiplicityDecomposition.encodedDecompositionMeasure νD
  let σ := OrderedMultiplicityDecomposition.encodedDecompositionMeasure νE
  have hρ : ∀ q, HasSpectralMeasure D (yD q) (ρ q) := by
    intro q
    exact OrderedMultiplicityDecomposition.encodedDecompositionMeasure_isSpectral
      D BD xD νD hMD q
  have hσ : ∀ q, HasSpectralMeasure E (yE q) (σ q) := by
    intro q
    exact OrderedMultiplicityDecomposition.encodedDecompositionMeasure_isSpectral
      E BE xE νE hME q
  have hdecD : IsOrthogonalCyclicDecomposition D yD :=
    OrderedMultiplicityDecomposition.encodedDecompositionVector_decomposition
      D hD BD xD νD hMD
  have hdecE : IsOrthogonalCyclicDecomposition E yE :=
    OrderedMultiplicityDecomposition.encodedDecompositionVector_decomposition
      E hE BE xE νE hME
  have hac : ∀ q, (ρ q).μ ≪ (σ q).μ ∧ (σ q).μ ≪ (ρ q).μ := by
    intro q
    exact encoded_components_cross_mutual_ac D E BD xD νD BE xE νE hMD hME hcross q
  let e : ∀ q, Lp ℂ 2 (ρ q).μ ≃ₗᵢ[ℂ] Lp ℂ 2 (σ q).μ := fun q ↦
    RadonNikodymTransfer.transferEquiv (σ q) (ρ q) (hac q).1 (hac q).2
  let C := HilbertDirectSum.coordinatewiseEquiv e
  let LD := HilbertDirectSum.modelEquiv D hD yD ρ hρ hdecD
  let LE := HilbertDirectSum.modelEquiv E hE yE σ hσ hdecE
  let W : D.H ≃ₗᵢ[ℂ] E.H := LD.symm.trans (C.trans LE)
  refine ⟨W, W.bijective, W.map_add, W.map_smul, W.norm_map, ?_⟩
  intro y
  change LE (C (LD.symm (D.U y))) = E.U (LE (C (LD.symm y)))
  rw [HilbertDirectSum.modelEquiv_symm_operator D hD yD ρ hρ hdecD]
  have hcoord : C (HilbertDirectSum.coordinate ρ (LD.symm y)) =
      HilbertDirectSum.coordinate σ (C (LD.symm y)) := by
    apply lp.ext
    funext q
    exact RadonNikodymTransfer.transfer_coordinate
      (σ q) (ρ q) (hac q).1 (LD.symm y q)
  rw [hcoord]
  change HilbertDirectSum.model E hE yE σ hσ
      (HilbertDirectSum.coordinate σ (C (LD.symm y))) =
    E.U (HilbertDirectSum.model E hE yE σ hσ (C (LD.symm y)))
  exact HilbertDirectSum.model_coordinate E hE yE σ hσ hdecE _

theorem classification
    (D : HilbertOperatorData.{u}) :
    SpectralClassificationByMaximalTypeAndMultiplicity D := by
  intro hsepD hD E hsepE hE
  constructor
  · exact forward_invariants hsepD hD
  · rintro ⟨μD, μE, multD, multE, hdataD, hdataE, hDE, hED, hmult⟩
    exact reverse_equivalence D E hsepD hsepE hD hE
      μD μE multD multE hdataD hdataE hDE hED hmult

end Chapter02.SpectralClassification
