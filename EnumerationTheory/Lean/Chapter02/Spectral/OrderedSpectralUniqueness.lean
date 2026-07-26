import Chapter02.Spectral.FiniteDirectSumOrthogonality

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.OrderedSpectralUniqueness

universe u

def restrictedCircleMeasure (μ : CircleMeasureData) (B : Set Circle) :
    CircleMeasureData where
  μ := μ.μ.restrict B
  isFinite := inferInstance

theorem restrictedCircleMeasure_absolutelyContinuous
    (μ : CircleMeasureData) (B : Set Circle) :
    (restrictedCircleMeasure μ B).μ ≪ μ.μ := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  change μ.μ.restrict B s = 0
  rw [Measure.restrict_apply hs]
  exact measure_mono_null inter_subset_left hzero

theorem ordered_component_dominates_across
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x y : ℕ → D.H)
    (hx : IsOrderedSpectralDecomposition D x)
    (hy : IsOrderedSpectralDecomposition D y) (n : ℕ) :
    SpectralMeasureDominatesVector D (y n) (x n) := by
  intro μyGiven μxGiven hμyGiven hμxGiven
  choose μx hμx _hμxuniq using fun i ↦ SpectralMeasure.spectralMeasure D hD (x i)
  choose μy hμy _hμyuniq using fun i ↦ SpectralMeasure.spectralMeasure D hD (y i)
  have hμxn : μx n = μxGiven := SpectralMeasure.eq_of_nat_moments _ _
    (fun k ↦ (hμx n k).trans (hμxGiven k).symm)
  have hμyn : μy n = μyGiven := SpectralMeasure.eq_of_nat_moments _ _
    (fun k ↦ (hμy n k).trans (hμyGiven k).symm)
  refine Measure.AbsolutelyContinuous.mk ?_
  intro B hB hμyB
  by_contra hμxB
  have hμyCanonicalB : (μy n).μ B = 0 := by simpa [hμyn] using hμyB
  have hμxCanonicalB : (μx n).μ B ≠ 0 := by simpa [hμxn] using hμxB
  let ν : CircleMeasureData := restrictedCircleMeasure (μx n) B
  have hνacn : ν.μ ≪ (μx n).μ :=
    restrictedCircleMeasure_absolutelyContinuous (μx n) B
  have hνaci (i : Fin (n + 1)) : ν.μ ≪ (μx i).μ := by
    have hin : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
    have hac := OrderedSpectralDecomposition.component_dominates_later
      D hD x hx.2 hin
    exact hνacn.trans (hac (μx i) (μx n) (hμx i) (hμx n))
  choose p hpcyc hpν using fun i : Fin (n + 1) ↦
    SpectralRelations.exists_cyclic_vector_with_ac_measure
      D hD (x i) (μx i) ν (hμx i) (hνaci i)
  have hporth : ∀ i j, i ≠ j → OrthogonalCyclicSubspaces D (p i) (p j) := by
    intro i j hij a b ha hb
    have hval : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (Fin.ext h)
    apply hx.1.1 i j hval
    · intro K hK hxi
      exact ha K hK (hpcyc i K hK hxi)
    · intro K hK hxj
      exact hb K hK (hpcyc j K hK hxj)
  have hνuniv : ν.μ Set.univ ≠ 0 := by
    change (μx n).μ.restrict B Set.univ ≠ 0
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hμxCanonicalB
  have hνBc : ν.μ Bᶜ = 0 := by
    change (μx n).μ.restrict B Bᶜ = 0
    rw [Measure.restrict_apply hB.compl]
    simp
  exact FiniteDirectSumOrthogonality.no_overfull_common_spectral_measure
    D hD y μy hμy hy n p ν hpν hνuniv B hνBc hμyCanonicalB hporth

theorem ordered_components_equivalent
    (D : HilbertOperatorData.{u}) (hD : IsUnitary D)
    (x y : ℕ → D.H)
    (hx : IsOrderedSpectralDecomposition D x)
    (hy : IsOrderedSpectralDecomposition D y) (n : ℕ) :
    SpectralMeasureEquivalentVectors D (x n) (y n) := by
  exact ⟨ordered_component_dominates_across D hD y x hy hx n,
    ordered_component_dominates_across D hD x y hx hy n⟩

end Chapter02.OrderedSpectralUniqueness
