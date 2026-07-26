import Chapter02.Spectral.MultiplicityStrata
import Chapter02.Spectral.OrderedSpectralUniqueness

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.OrderedMultiplicitySupports

universe u

def spectralSupport (μbase μ : CircleMeasureData) : Set Circle :=
  {z | μ.μ.rnDeriv μbase.μ z ≠ 0}

def nestedSupport (μ : ℕ → CircleMeasureData) (k : ℕ) : Set Circle :=
  ⋂ j : Fin (k + 1), spectralSupport (μ 0) (μ j)

def multiplicityStratum (μ : ℕ → CircleMeasureData) (n : ℕ) : Set Circle :=
  MultiplicityStrata.stratum (nestedSupport μ) n

def restrictedComponentMeasure (μ : ℕ → CircleMeasureData) (n k : ℕ) :
    CircleMeasureData :=
  OrderedSpectralUniqueness.restrictedCircleMeasure (μ k) (multiplicityStratum μ n)

theorem measurableSet_spectralSupport (μbase μ : CircleMeasureData) :
    MeasurableSet (spectralSupport μbase μ) := by
  change MeasurableSet (μ.μ.rnDeriv μbase.μ ⁻¹' ({0} : Set ENNReal)ᶜ)
  exact (Measure.measurable_rnDeriv μ.μ μbase.μ)
    (measurableSet_singleton (0 : ENNReal)).compl

theorem measurableSet_nestedSupport (μ : ℕ → CircleMeasureData) (k : ℕ) :
    MeasurableSet (nestedSupport μ k) := by
  exact MeasurableSet.iInter fun j ↦ measurableSet_spectralSupport (μ 0) (μ j)

theorem measurableSet_multiplicityStratum (μ : ℕ → CircleMeasureData) :
    ∀ n, MeasurableSet (multiplicityStratum μ n) :=
  MultiplicityStrata.measurableSet_stratum (fun k ↦ measurableSet_nestedSupport μ k)

theorem nestedSupport_antitone (μ : ℕ → CircleMeasureData) :
    Antitone (nestedSupport μ) := by
  intro i j hij z hz
  apply Set.mem_iInter.2
  intro k
  have hki : (k : ℕ) < i + 1 := k.isLt
  have hkj : (k : ℕ) < j + 1 := lt_of_lt_of_le hki (Nat.succ_le_succ hij)
  exact Set.mem_iInter.mp hz ⟨k, hkj⟩

theorem nestedSupport_subset_spectralSupport (μ : ℕ → CircleMeasureData) (k : ℕ) :
    nestedSupport μ k ⊆ spectralSupport (μ 0) (μ k) := by
  intro z hz
  exact Set.mem_iInter.mp hz ⟨k, Nat.lt_succ_self k⟩

theorem spectralMeasure_compl_support_zero (μbase μ : CircleMeasureData)
    (hμ : μ.μ ≪ μbase.μ) : μ.μ (spectralSupport μbase μ)ᶜ = 0 := by
  rw [← Measure.withDensity_rnDeriv_eq μ.μ μbase.μ hμ]
  apply (withDensity_apply_eq_zero'
    (Measure.measurable_rnDeriv μ.μ μbase.μ).aemeasurable).2
  have hempty : {z | μ.μ.rnDeriv μbase.μ z ≠ 0} ∩
      (spectralSupport μbase μ)ᶜ = ∅ := by
    ext z
    simp [spectralSupport]
  rw [hempty, measure_empty]

theorem componentMeasure_compl_nestedSupport_zero
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    (k : ℕ) : (μ k).μ (nestedSupport μ k)ᶜ = 0 := by
  rw [nestedSupport, compl_iInter]
  apply measure_iUnion_null
  intro j
  have hjk : (j : ℕ) ≤ k := Nat.le_of_lt_succ j.isLt
  have hacjk := OrderedSpectralDecomposition.component_dominates_later
    D hD x hord hjk
  exact hacjk (μ j) (μ k) (hμ j) (hμ k)
    (spectralMeasure_compl_support_zero (μ 0) (μ j)
      (OrderedSpectralDecomposition.component_dominates_later
      D hD x hord (Nat.zero_le j) (μ 0) (μ j) (hμ 0) (hμ j)))

theorem activeStratum_outside_support_zero
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    (n k : ℕ) (hactive : IsActiveMultiplicityIndex n k) :
    (μ 0).μ (multiplicityStratum μ n \ spectralSupport (μ 0) (μ k)) = 0 := by
  rcases n with _ | _ | n
  · have hsubset : multiplicityStratum μ 0 ⊆ spectralSupport (μ 0) (μ k) := by
      intro z hz
      exact nestedSupport_subset_spectralSupport μ k
        (Set.mem_iInter.mp hz k)
    have hempty : multiplicityStratum μ 0 \ spectralSupport (μ 0) (μ k) = ∅ :=
      Set.diff_eq_empty.mpr hsubset
    rw [hempty, measure_empty]
  · have hk0 : k = 0 := by simpa [IsActiveMultiplicityIndex] using hactive
    subst k
    apply measure_mono_null (t := (nestedSupport μ 0)ᶜ)
    · intro z hz
      rcases hz.1 with hz0 | hz1
      · exact hz0.1
      · exfalso
        apply hz.2
        exact nestedSupport_subset_spectralSupport μ 0
          (Set.mem_iInter.mp hz1.2 ⟨0, by omega⟩)
    · exact componentMeasure_compl_nestedSupport_zero D hD x μ hμ hord 0
  · have hkle : k ≤ n + 1 := by simpa [IsActiveMultiplicityIndex] using hactive
    have hkn : k < n + 2 := by omega
    have hsubset : multiplicityStratum μ (n + 2) ⊆
        spectralSupport (μ 0) (μ k) := by
      intro z hz
      have hTk : z ∈ nestedSupport μ k := by
        have hall := Set.mem_iInter.mp hz.2
        exact hall ⟨k, hkn⟩
      exact nestedSupport_subset_spectralSupport μ k hTk
    rw [Set.diff_eq_empty.mpr hsubset, measure_empty]

theorem inactiveStratum_componentMeasure_zero
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    (n k : ℕ) (hinactive : ¬ IsActiveMultiplicityIndex n k) :
    (μ k).μ (multiplicityStratum μ n) = 0 := by
  have hn0 : n ≠ 0 := by
    intro hn
    apply hinactive
    exact Or.inl hn
  have hnk : n ≤ k := by
    simpa [IsActiveMultiplicityIndex, hn0] using hinactive
  apply measure_mono_null (t := (nestedSupport μ k)ᶜ)
  · intro z hz hzk
    have hTn : z ∈ nestedSupport μ n := nestedSupport_antitone μ hnk hzk
    rcases n with _ | _ | n
    · exact (hn0 rfl).elim
    · rcases hz with hz0 | hz1
      · exact hz0.1 (nestedSupport_antitone μ (by omega) hzk)
      · exact hz1.1 hTn
    · exact hz.1 hTn
  · exact componentMeasure_compl_nestedSupport_zero D hD x μ hμ hord k

theorem restrict_absolutelyContinuous_restrict {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {B : Set α} (hB : MeasurableSet B) (hμν : μ ≪ ν) :
    μ.restrict B ≪ ν.restrict B := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hzero
  rw [Measure.restrict_apply hA] at hzero ⊢
  exact hμν hzero

theorem restrict_base_absolutelyContinuous_restrict_of_positive_support
    (μbase μ : CircleMeasureData) (hμ : μ.μ ≪ μbase.μ)
    (B : Set Circle) (hB : MeasurableSet B)
    (houtside : μbase.μ (B \ spectralSupport μbase μ) = 0) :
    μbase.μ.restrict B ≪ μ.μ.restrict B := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hzero
  rw [Measure.restrict_apply hA] at hzero ⊢
  have hAB : MeasurableSet (A ∩ B) := hA.inter hB
  have hdensityZero : μbase.μ
      ({z | μ.μ.rnDeriv μbase.μ z ≠ 0} ∩ (A ∩ B)) = 0 := by
    apply (withDensity_apply_eq_zero'
      (Measure.measurable_rnDeriv μ.μ μbase.μ).aemeasurable).1
    rw [Measure.withDensity_rnDeriv_eq μ.μ μbase.μ hμ]
    exact hzero
  apply measure_mono_null (t :=
      ({z | μ.μ.rnDeriv μbase.μ z ≠ 0} ∩ (A ∩ B)) ∪
        (B \ spectralSupport μbase μ))
  · intro z hz
    by_cases hzs : z ∈ spectralSupport μbase μ
    · exact Or.inl ⟨hzs, hz⟩
    · exact Or.inr ⟨hz.2, hzs⟩
  · exact measure_union_null hdensityZero houtside

theorem active_restrictedMeasure_equivalent_base
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x : ℕ → D.H) (μ : ℕ → CircleMeasureData)
    (hμ : ∀ n, HasSpectralMeasure D (x n) (μ n))
    (hord : ∀ n, SpectralMeasureDominatesVector D (x n) (x (n + 1)))
    (n k : ℕ) (hactive : IsActiveMultiplicityIndex n k) :
    (restrictedComponentMeasure μ n k).μ ≪
        (restrictedComponentMeasure μ n 0).μ ∧
      (restrictedComponentMeasure μ n 0).μ ≪
        (restrictedComponentMeasure μ n k).μ := by
  let B := multiplicityStratum μ n
  have hB := measurableSet_multiplicityStratum μ n
  have hμk0 : (μ k).μ ≪ (μ 0).μ :=
    OrderedSpectralDecomposition.component_dominates_later D hD x hord
      (Nat.zero_le k) (μ 0) (μ k) (hμ 0) (hμ k)
  exact ⟨restrict_absolutelyContinuous_restrict hB hμk0,
    restrict_base_absolutelyContinuous_restrict_of_positive_support
      (μ 0) (μ k) hμk0 B hB
      (activeStratum_outside_support_zero D hD x μ hμ hord n k hactive)⟩

theorem multiplicityStrata_pairwise_disjoint (μ : ℕ → CircleMeasureData) :
    ∀ n m, n ≠ m → Disjoint (multiplicityStratum μ n) (multiplicityStratum μ m) :=
  MultiplicityStrata.stratum_pairwise_disjoint (nestedSupport μ)

theorem iUnion_multiplicityStratum (μ : ℕ → CircleMeasureData) :
    (⋃ n, multiplicityStratum μ n) = Set.univ :=
  MultiplicityStrata.iUnion_stratum (nestedSupport μ)

end Chapter02.OrderedMultiplicitySupports
