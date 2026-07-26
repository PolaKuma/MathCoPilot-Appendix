import Chapter02.Common
import Chapter00.Section01

noncomputable section

open Filter

namespace Chapter02
namespace CorrelationSemiAlgebra

universe u

lemma generatedAlgebra_isAlgebra {X : Type u} (S : Chapter00.SetFamily X) :
    Chapter00.IsAlgebra (Chapter00.generatedAlgebra S) := by
  unfold Chapter00.generatedAlgebra
  constructor
  · change ∀ A ∈ {A : Chapter00.SetFamily X | Chapter00.IsAlgebra A ∧ S ⊆ A},
      (∅ : Set X) ∈ A
    intro A hA
    exact hA.1.1
  · constructor
    · intro E hE F hF
      change ∀ A ∈ {A : Chapter00.SetFamily X | Chapter00.IsAlgebra A ∧ S ⊆ A},
        E \ F ∈ A
      intro A hA
      exact hA.1.2.1 E (hE A hA) F (hF A hA)
    · intro E hE
      change ∀ A ∈ {A : Chapter00.SetFamily X | Chapter00.IsAlgebra A ∧ S ⊆ A},
        Eᶜ ∈ A
      intro A hA
      exact hA.1.2.2 E (hE A hA)

lemma subset_generatedAlgebra {X : Type u} (S : Chapter00.SetFamily X) :
    S ⊆ Chapter00.generatedAlgebra S := by
  intro E hE
  change ∀ A ∈ {A : Chapter00.SetFamily X | Chapter00.IsAlgebra A ∧ S ⊆ A}, E ∈ A
  intro A hA
  exact hA.2 hE

lemma generatedAlgebra_subset_generatedSigmaAlgebra {X : Type u}
    (S : Chapter00.SetFamily X) :
    Chapter00.generatedAlgebra S ⊆ Chapter00.generatedSigmaAlgebra S := by
  intro E hE
  apply hE (Chapter00.generatedSigmaAlgebra S)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact @MeasurableSet.empty X (MeasurableSpace.generateFrom S)
  · intro A hA B hB
    change @MeasurableSet X (MeasurableSpace.generateFrom S) A at hA
    change @MeasurableSet X (MeasurableSpace.generateFrom S) B at hB
    change @MeasurableSet X (MeasurableSpace.generateFrom S) (A \ B)
    exact hA.diff hB
  · intro A hA
    change @MeasurableSet X (MeasurableSpace.generateFrom S) A at hA
    change @MeasurableSet X (MeasurableSpace.generateFrom S) Aᶜ
    exact hA.compl
  · intro A hA
    exact MeasurableSpace.measurableSet_generateFrom hA

lemma generateFrom_generatedAlgebra {X : Type u} (S : Chapter00.SetFamily X) :
    MeasurableSpace.generateFrom (Chapter00.generatedAlgebra S) =
      MeasurableSpace.generateFrom S := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro E hE
    exact generatedAlgebra_subset_generatedSigmaAlgebra S hE
  · exact MeasurableSpace.generateFrom_mono (subset_generatedAlgebra S)

lemma correlation_finite_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {n m : ℕ} (C : Fin n → Set M.X) (D : Fin m → Set M.X)
    (hCdisj : Chapter00.PairwiseDisjoint C)
    (hDdisj : Chapter00.PairwiseDisjoint D)
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j))
    (k : ℕ) :
    correlation M (⋃ i, C i) (⋃ j, D j) k =
      ∑ i, ∑ j, correlation M (C i) (D j) k := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let E : Fin n → Fin m → Set M.X :=
    fun i j ↦ C i ∩ preimageIter M k (D j)
  have hset : (⋃ i, C i) ∩ preimageIter M k (⋃ j, D j) =
      ⋃ i, ⋃ j, E i j := by
    ext x
    simp [E, preimageIter, Chapter01.iterateMap]
  have hEmeas : ∀ i j, MeasurableSet (E i j) := by
    intro i j
    exact (hCmeas i).inter ((hDmeas j).preimage (hM.2.measurable.iterate k))
  have hEdisj_j : ∀ i, Pairwise (Function.onFun Disjoint (E i)) := by
    intro i j l hjl
    apply Set.disjoint_left.2
    intro x hxj hxl
    exact Set.disjoint_left.1 (hDdisj j l hjl) hxj.2 hxl.2
  have hEdisj_i : Pairwise (Function.onFun Disjoint (fun i ↦ ⋃ j, E i j)) := by
    intro i l hil
    apply Set.disjoint_left.2
    intro x hxi hxl
    simp only [Set.mem_iUnion] at hxi hxl
    exact Set.disjoint_left.1 (hCdisj i l hil)
      (Classical.choose_spec hxi).1 (Classical.choose_spec hxl).1
  unfold correlation realMeasure
  rw [hset, MeasureTheory.measure_iUnion hEdisj_i
    (fun i ↦ MeasurableSet.iUnion (fun j ↦ hEmeas i j))]
  have hinner (i : Fin n) : M.μ (⋃ j, E i j) = ∑ j, M.μ (E i j) := by
    simpa only [tsum_fintype] using
      MeasureTheory.measure_iUnion (hEdisj_j i) (hEmeas i)
  simp_rw [hinner]
  simp only [tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ ↦ by simp)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_sum (fun a _ ↦ by simp)]

lemma realMeasure_finite_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {n : ℕ} (C : Fin n → Set M.X)
    (hCdisj : Chapter00.PairwiseDisjoint C)
    (hCmeas : ∀ i, MeasurableSet (C i)) :
    realMeasure M (⋃ i, C i) = ∑ i, realMeasure M (C i) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  unfold realMeasure
  rw [MeasureTheory.measure_iUnion hCdisj hCmeas]
  simp only [tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ ↦ by simp)]

lemma productMeasureValue_finite_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {n m : ℕ} (C : Fin n → Set M.X) (D : Fin m → Set M.X)
    (hCdisj : Chapter00.PairwiseDisjoint C)
    (hDdisj : Chapter00.PairwiseDisjoint D)
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j)) :
    productMeasureValue M (⋃ i, C i) (⋃ j, D j) =
      ∑ i, ∑ j, productMeasureValue M (C i) (D j) := by
  unfold productMeasureValue
  rw [realMeasure_finite_iUnion M hM C hCdisj hCmeas,
    realMeasure_finite_iUnion M hM D hDdisj hDmeas]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

lemma cesaroAverage_finite_sum {n m : ℕ} (a : Fin n → Fin m → ℕ → ℝ)
    (N : ℕ) :
    cesaroAverage (fun k ↦ ∑ i, ∑ j, a i j k) N =
      ∑ i, ∑ j, cesaroAverage (a i j) N := by
  unfold cesaroAverage
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm, Finset.mul_sum]

lemma cesaro_finite_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {n m : ℕ} (C : Fin n → Set M.X) (D : Fin m → Set M.X)
    (hCdisj : Chapter00.PairwiseDisjoint C)
    (hDdisj : Chapter00.PairwiseDisjoint D)
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j))
    (hlim : ∀ i j, cesaroTendsTo (fun k ↦ correlation M (C i) (D j) k)
      (productMeasureValue M (C i) (D j))) :
    cesaroTendsTo (fun k ↦ correlation M (⋃ i, C i) (⋃ j, D j) k)
      (productMeasureValue M (⋃ i, C i) (⋃ j, D j)) := by
  unfold cesaroTendsTo seqTendsTo at hlim ⊢
  have hsum : Tendsto
      (fun N ↦ ∑ i, ∑ j,
        cesaroAverage (fun k ↦ correlation M (C i) (D j) k) N) atTop
      (nhds (∑ i, ∑ j, productMeasureValue M (C i) (D j))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    exact hlim i j
  convert hsum using 1
  · funext N
    rw [show (fun k ↦ correlation M (⋃ i, C i) (⋃ j, D j) k) =
        (fun k ↦ ∑ i, ∑ j, correlation M (C i) (D j) k) by
      funext k
      exact correlation_finite_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas k]
    exact cesaroAverage_finite_sum
      (fun i j k ↦ correlation M (C i) (D j) k) N
  · congr 1
    exact productMeasureValue_finite_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas

lemma absDeviation_cesaro_finite_iUnion (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {n m : ℕ} (C : Fin n → Set M.X) (D : Fin m → Set M.X)
    (hCdisj : Chapter00.PairwiseDisjoint C)
    (hDdisj : Chapter00.PairwiseDisjoint D)
    (hCmeas : ∀ i, MeasurableSet (C i)) (hDmeas : ∀ j, MeasurableSet (D j))
    (hlim : ∀ i j, cesaroTendsTo
      (fun k ↦ |correlation M (C i) (D j) k - productMeasureValue M (C i) (D j)|) 0) :
    cesaroTendsTo
      (fun k ↦ |correlation M (⋃ i, C i) (⋃ j, D j) k -
        productMeasureValue M (⋃ i, C i) (⋃ j, D j)|) 0 := by
  have hpoint (k : ℕ) :
      |correlation M (⋃ i, C i) (⋃ j, D j) k -
        productMeasureValue M (⋃ i, C i) (⋃ j, D j)| ≤
        ∑ i, ∑ j, |correlation M (C i) (D j) k -
          productMeasureValue M (C i) (D j)| := by
    rw [correlation_finite_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas,
      productMeasureValue_finite_iUnion M hM C D hCdisj hDdisj hCmeas hDmeas,
      ← Finset.sum_sub_distrib]
    calc
      |∑ i, ((∑ j, correlation M (C i) (D j) k) -
          (∑ j, productMeasureValue M (C i) (D j)))| ≤
          ∑ i, |(∑ j, correlation M (C i) (D j) k) -
            (∑ j, productMeasureValue M (C i) (D j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |correlation M (C i) (D j) k -
          productMeasureValue M (C i) (D j)| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
  unfold cesaroTendsTo seqTendsTo at hlim ⊢
  have hsum : Tendsto
      (fun N ↦ ∑ i, ∑ j, cesaroAverage
        (fun k ↦ |correlation M (C i) (D j) k -
          productMeasureValue M (C i) (D j)|) N) atTop (nhds 0) := by
    have hsum' : Tendsto
        (fun N ↦ ∑ i, ∑ j, cesaroAverage
          (fun k ↦ |correlation M (C i) (D j) k -
            productMeasureValue M (C i) (D j)|) N) atTop
        (nhds (∑ _i : Fin n, ∑ _j : Fin m, (0 : ℝ))) := by
      apply tendsto_finset_sum
      intro i hi
      apply tendsto_finset_sum
      intro j hj
      exact hlim i j
    simpa using hsum'
  apply squeeze_zero' (g := fun N ↦ ∑ i, ∑ j, cesaroAverage
    (fun k ↦ |correlation M (C i) (D j) k -
      productMeasureValue M (C i) (D j)|) N)
  · filter_upwards [] with N
    unfold cesaroAverage
    positivity
  · filter_upwards [] with N
    rw [← cesaroAverage_finite_sum (fun i j k ↦
      |correlation M (C i) (D j) k - productMeasureValue M (C i) (D j)|) N]
    unfold cesaroAverage
    gcongr with k hk
    exact hpoint k
  · exact hsum

lemma abs_correlation_sub_le_symmDiff (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B C D : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    |correlation M A B k - correlation M C D k| ≤
      M.μ.real (_root_.symmDiff A C) + M.μ.real (_root_.symmDiff B D) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let E := A ∩ preimageIter M k B
  let F := C ∩ preimageIter M k D
  have hE : MeasurableSet E :=
    hA.inter (hB.preimage (hM.2.measurable.iterate k))
  have hF : MeasurableSet F :=
    hC.inter (hD.preimage (hM.2.measurable.iterate k))
  calc
    |correlation M A B k - correlation M C D k| =
        |M.μ.real E - M.μ.real F| := rfl
    _ ≤ M.μ.real (_root_.symmDiff E F) :=
      MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff
        hE.nullMeasurableSet hF.nullMeasurableSet
    _ ≤ M.μ.real
        (_root_.symmDiff A C ∪ preimageIter M k (_root_.symmDiff B D)) := by
      apply MeasureTheory.measureReal_mono
      · intro x hx
        simp only [E, F, Set.mem_symmDiff, Set.mem_inter_iff, not_and_or,
          Set.mem_union, preimageIter, Chapter01.iterateMap, Set.mem_preimage] at hx ⊢
        tauto
      · simp
    _ ≤ M.μ.real (_root_.symmDiff A C) +
        M.μ.real (preimageIter M k (_root_.symmDiff B D)) :=
      MeasureTheory.measureReal_union_le _ _
    _ = M.μ.real (_root_.symmDiff A C) +
        M.μ.real (_root_.symmDiff B D) := by
      congr 1
      unfold preimageIter Chapter01.iterateMap
      unfold MeasureTheory.Measure.real
      rw [(hM.2.iterate k).measure_preimage]
      exact (hB.symmDiff hD).nullMeasurableSet

lemma abs_cesaroAverage_sub_le {a b : ℕ → ℝ} {d : ℝ}
    (h : ∀ k, |a k - b k| ≤ d) (N : ℕ) :
    |cesaroAverage a N - cesaroAverage b N| ≤ d := by
  unfold cesaroAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  calc
    ((N + 1 : ℕ) : ℝ)⁻¹ * |∑ i ∈ Finset.range (N + 1), (a i - b i)| ≤
        ((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ i ∈ Finset.range (N + 1), |a i - b i| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ *
        ∑ _i ∈ Finset.range (N + 1), d := by
      gcongr with i hi
      exact h i
    _ = d := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

lemma abs_productMeasureValue_sub_le_symmDiff (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B C D : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    |productMeasureValue M A B - productMeasureValue M C D| ≤
      M.μ.real (_root_.symmDiff A C) + M.μ.real (_root_.symmDiff B D) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hAC : |M.μ.real A - M.μ.real C| ≤
      M.μ.real (_root_.symmDiff A C) :=
    MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet hC.nullMeasurableSet
  have hBD : |M.μ.real B - M.μ.real D| ≤
      M.μ.real (_root_.symmDiff B D) :=
    MeasureTheory.abs_measureReal_sub_le_measureReal_symmDiff
      hB.nullMeasurableSet hD.nullMeasurableSet
  have hB0 : 0 ≤ M.μ.real B := MeasureTheory.measureReal_nonneg
  have hC0 : 0 ≤ M.μ.real C := MeasureTheory.measureReal_nonneg
  have hB1 : M.μ.real B ≤ 1 := by
    simpa using MeasureTheory.measureReal_mono (μ := M.μ)
      (Set.subset_univ B) (by simp)
  have hC1 : M.μ.real C ≤ 1 := by
    simpa using MeasureTheory.measureReal_mono (μ := M.μ)
      (Set.subset_univ C) (by simp)
  unfold productMeasureValue realMeasure
  calc
    |M.μ.real A * M.μ.real B - M.μ.real C * M.μ.real D| =
        |(M.μ.real A - M.μ.real C) * M.μ.real B +
          M.μ.real C * (M.μ.real B - M.μ.real D)| := by ring_nf
    _ ≤ |M.μ.real A - M.μ.real C| * M.μ.real B +
        M.μ.real C * |M.μ.real B - M.μ.real D| := by
      calc
        _ ≤ |(M.μ.real A - M.μ.real C) * M.μ.real B| +
            |M.μ.real C * (M.μ.real B - M.μ.real D)| := abs_add_le _ _
        _ = _ := by
          simp only [abs_mul, abs_of_nonneg hB0, abs_of_nonneg hC0]
    _ ≤ M.μ.real (_root_.symmDiff A C) +
        M.μ.real (_root_.symmDiff B D) := by
      nlinarith [abs_nonneg (M.μ.real A - M.μ.real C),
        abs_nonneg (M.μ.real B - M.μ.real D)]

lemma abs_absDeviation_sub_le_two_symmDiff (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B C D : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    abs (abs (correlation M A B k - productMeasureValue M A B) -
      abs (correlation M C D k - productMeasureValue M C D)) ≤
      2 * (M.μ.real (_root_.symmDiff A C) +
        M.μ.real (_root_.symmDiff B D)) := by
  have hcorr := abs_correlation_sub_le_symmDiff M hM A B C D hA hB hC hD k
  have hprod := abs_productMeasureValue_sub_le_symmDiff M hM A B C D hA hB hC hD
  have hrev : |productMeasureValue M C D - productMeasureValue M A B| ≤
      M.μ.real (_root_.symmDiff A C) + M.μ.real (_root_.symmDiff B D) := by
    simpa [abs_sub_comm] using hprod
  calc
    _ ≤ |(correlation M A B k - productMeasureValue M A B) -
        (correlation M C D k - productMeasureValue M C D)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = |(correlation M A B k - correlation M C D k) +
        (productMeasureValue M C D - productMeasureValue M A B)| := by ring_nf
    _ ≤ |correlation M A B k - correlation M C D k| +
        |productMeasureValue M C D - productMeasureValue M A B| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma cesaro_on_generatedAlgebra (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (S : SetFamily M.X)
    (hS : Chapter00.IsSemiAlgebra S)
    (hgen : Chapter00.generatedSigmaAlgebra S =
      {E : Set M.X | @MeasurableSet M.X M.measurableSpace E})
    (hlim : ∀ A B : Set M.X, A ∈ S → B ∈ S →
      cesaroTendsTo (fun k ↦ correlation M A B k) (productMeasureValue M A B)) :
    ∀ A B : Set M.X, A ∈ Chapter00.generatedAlgebra S →
      B ∈ Chapter00.generatedAlgebra S →
      cesaroTendsTo (fun k ↦ correlation M A B k) (productMeasureValue M A B) := by
  intro A B hA hB
  rw [Chapter00.Section01.algebraGeneratedBySemiAlgebraFiniteDisjointUnions S hS] at hA hB
  obtain ⟨n, C, hCdisj, hCS, rfl⟩ := hA
  obtain ⟨m, D, hDdisj, hDS, rfl⟩ := hB
  have hSmeas : ∀ E, E ∈ S → MeasurableSet E := by
    intro E hE
    change E ∈ {F : Set M.X | @MeasurableSet M.X M.measurableSpace F}
    rw [← hgen]
    exact MeasurableSpace.measurableSet_generateFrom hE
  exact cesaro_finite_iUnion M hM C D hCdisj hDdisj
    (fun i ↦ hSmeas (C i) (hCS i)) (fun j ↦ hSmeas (D j) (hDS j))
    (fun i j ↦ hlim (C i) (D j) (hCS i) (hDS j))

lemma absDeviation_on_generatedAlgebra (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (S : SetFamily M.X)
    (hS : Chapter00.IsSemiAlgebra S)
    (hgen : Chapter00.generatedSigmaAlgebra S =
      {E : Set M.X | @MeasurableSet M.X M.measurableSpace E})
    (hlim : ∀ A B : Set M.X, A ∈ S → B ∈ S →
      cesaroTendsTo
        (fun k ↦ |correlation M A B k - productMeasureValue M A B|) 0) :
    ∀ A B : Set M.X, A ∈ Chapter00.generatedAlgebra S →
      B ∈ Chapter00.generatedAlgebra S →
      cesaroTendsTo
        (fun k ↦ |correlation M A B k - productMeasureValue M A B|) 0 := by
  intro A B hA hB
  rw [Chapter00.Section01.algebraGeneratedBySemiAlgebraFiniteDisjointUnions S hS] at hA hB
  obtain ⟨n, C, hCdisj, hCS, rfl⟩ := hA
  obtain ⟨m, D, hDdisj, hDS, rfl⟩ := hB
  have hSmeas : ∀ E, E ∈ S → MeasurableSet E := by
    intro E hE
    change E ∈ {F : Set M.X | @MeasurableSet M.X M.measurableSpace F}
    rw [← hgen]
    exact MeasurableSpace.measurableSet_generateFrom hE
  exact absDeviation_cesaro_finite_iUnion M hM C D hCdisj hDdisj
    (fun i ↦ hSmeas (C i) (hCS i)) (fun j ↦ hSmeas (D j) (hDS j))
    (fun i j ↦ hlim (C i) (D j) (hCS i) (hDS j))

lemma seq_on_generatedAlgebra (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (S : SetFamily M.X)
    (hS : Chapter00.IsSemiAlgebra S)
    (hgen : Chapter00.generatedSigmaAlgebra S =
      {E : Set M.X | @MeasurableSet M.X M.measurableSpace E})
    (hlim : ∀ A B : Set M.X, A ∈ S → B ∈ S →
      Tendsto (fun k ↦ correlation M A B k) atTop
        (nhds (productMeasureValue M A B))) :
    ∀ A B : Set M.X, A ∈ Chapter00.generatedAlgebra S →
      B ∈ Chapter00.generatedAlgebra S →
      Tendsto (fun k ↦ correlation M A B k) atTop
        (nhds (productMeasureValue M A B)) := by
  intro A B hA hB
  rw [Chapter00.Section01.algebraGeneratedBySemiAlgebraFiniteDisjointUnions S hS] at hA hB
  obtain ⟨n, C, hCdisj, hCS, rfl⟩ := hA
  obtain ⟨m, D, hDdisj, hDS, rfl⟩ := hB
  have hSmeas : ∀ E, E ∈ S → MeasurableSet E := by
    intro E hE
    change E ∈ {F : Set M.X | @MeasurableSet M.X M.measurableSpace F}
    rw [← hgen]
    exact MeasurableSpace.measurableSet_generateFrom hE
  have hsum : Tendsto (fun k ↦ ∑ i, ∑ j, correlation M (C i) (D j) k) atTop
      (nhds (∑ i, ∑ j, productMeasureValue M (C i) (D j))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    exact hlim (C i) (D j) (hCS i) (hDS j)
  convert hsum using 1
  · funext k
    exact correlation_finite_iUnion M hM C D hCdisj hDdisj
      (fun i ↦ hSmeas (C i) (hCS i))
      (fun j ↦ hSmeas (D j) (hDS j)) k
  · congr 1
    exact productMeasureValue_finite_iUnion M hM C D hCdisj hDdisj
      (fun i ↦ hSmeas (C i) (hCS i))
      (fun j ↦ hSmeas (D j) (hDS j))

set_option maxHeartbeats 400000 in
lemma cesaro_on_all_measurable (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (S : SetFamily M.X)
    (hgen : Chapter00.generatedSigmaAlgebra S =
      {E : Set M.X | @MeasurableSet M.X M.measurableSpace E})
    (hlim : ∀ A B : Set M.X, A ∈ Chapter00.generatedAlgebra S →
      B ∈ Chapter00.generatedAlgebra S →
      cesaroTendsTo (fun k ↦ correlation M A B k) (productMeasureValue M A B)) :
    ∀ A B : Set M.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo (fun k ↦ correlation M A B k) (productMeasureValue M A B) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hAlg := generatedAlgebra_isAlgebra S
  have hUnion : ∀ E F : Set M.X, E ∈ Chapter00.generatedAlgebra S →
      F ∈ Chapter00.generatedAlgebra S → E ∪ F ∈ Chapter00.generatedAlgebra S := by
    intro E F hE hF
    have hd := hAlg.2.1 Eᶜ (hAlg.2.2 E hE) F hF
    have hc := hAlg.2.2 (Eᶜ \ F) hd
    convert hc using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]
    tauto
  have hSetAlg : MeasureTheory.IsSetAlgebra (Chapter00.generatedAlgebra S) :=
    { empty_mem := hAlg.1
      compl_mem := fun E hE ↦ hAlg.2.2 E hE
      union_mem := fun E F hE hF ↦ hUnion E F hE hF }
  have hMS : M.measurableSpace = MeasurableSpace.generateFrom S := by
    apply MeasurableSpace.ext
    intro E
    change E ∈ {F : Set M.X | @MeasurableSet M.X M.measurableSpace F} ↔
      E ∈ Chapter00.generatedSigmaAlgebra S
    rw [hgen]
  have hMSAlg : M.measurableSpace =
      MeasurableSpace.generateFrom (Chapter00.generatedAlgebra S) :=
    hMS.trans (generateFrom_generatedAlgebra S).symm
  have hdense : M.μ.MeasureDense (Chapter00.generatedAlgebra S) :=
    MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
      M.μ hSetAlg hMSAlg
  intro A B hA hB
  unfold cesaroTendsTo seqTendsTo
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C, hCAlg, hAC⟩ := hdense.approx A hA (by simp) δ hδ
  obtain ⟨D, hDAlg, hBD⟩ := hdense.approx B hB (by simp) δ hδ
  have hC : MeasurableSet C := hdense.measurable C hCAlg
  have hD : MeasurableSet D := hdense.measurable D hDAlg
  have hACreal : M.μ.real (_root_.symmDiff A C) < δ := by
    unfold MeasureTheory.Measure.real
    have ht := (ENNReal.toReal_lt_toReal (by simp) (by simp)).mpr hAC
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  have hBDreal : M.μ.real (_root_.symmDiff B D) < δ := by
    unfold MeasureTheory.Measure.real
    have ht := (ENNReal.toReal_lt_toReal (by simp) (by simp)).mpr hBD
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  let d := M.μ.real (_root_.symmDiff A C) + M.μ.real (_root_.symmDiff B D)
  have hdlt : d < ε / 4 := by
    dsimp [d, δ] at hACreal hBDreal ⊢
    linarith
  have havgbound : ∀ N,
      |cesaroAverage (fun k ↦ correlation M A B k) N -
        cesaroAverage (fun k ↦ correlation M C D k) N| ≤ d := by
    intro N
    apply abs_cesaroAverage_sub_le
    intro k
    exact abs_correlation_sub_le_symmDiff M hM A B C D hA hB hC hD k
  have hprodbound :
      |productMeasureValue M A B - productMeasureValue M C D| ≤ d :=
    abs_productMeasureValue_sub_le_symmDiff M hM A B C D hA hB hC hD
  have hCD := hlim C D hCAlg hDAlg
  unfold cesaroTendsTo seqTendsTo at hCD
  rw [Metric.tendsto_atTop] at hCD
  obtain ⟨N, hN⟩ := hCD (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmid := hN n hn
  rw [Real.dist_eq] at hmid ⊢
  calc
    |cesaroAverage (fun k ↦ correlation M A B k) n - productMeasureValue M A B| ≤
        |cesaroAverage (fun k ↦ correlation M A B k) n -
          cesaroAverage (fun k ↦ correlation M C D k) n| +
        |cesaroAverage (fun k ↦ correlation M C D k) n - productMeasureValue M C D| +
        |productMeasureValue M C D - productMeasureValue M A B| := by
      calc
        _ = |(cesaroAverage (fun k ↦ correlation M A B k) n -
              cesaroAverage (fun k ↦ correlation M C D k) n) +
            (cesaroAverage (fun k ↦ correlation M C D k) n - productMeasureValue M C D) +
            (productMeasureValue M C D - productMeasureValue M A B)| := by ring_nf
        _ ≤ |(cesaroAverage (fun k ↦ correlation M A B k) n -
              cesaroAverage (fun k ↦ correlation M C D k) n) +
            (cesaroAverage (fun k ↦ correlation M C D k) n - productMeasureValue M C D)| +
            |productMeasureValue M C D - productMeasureValue M A B| := abs_add_le _ _
        _ ≤ _ := by
          nlinarith [abs_add_le
            (cesaroAverage (fun k ↦ correlation M A B k) n -
              cesaroAverage (fun k ↦ correlation M C D k) n)
            (cesaroAverage (fun k ↦ correlation M C D k) n -
              productMeasureValue M C D)]
    _ < ε := by
      rw [abs_sub_comm (productMeasureValue M C D)]
      linarith [havgbound n, hprodbound]

set_option maxHeartbeats 400000 in
lemma absDeviation_on_all_measurable (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (S : SetFamily M.X)
    (hgen : Chapter00.generatedSigmaAlgebra S =
      {E : Set M.X | @MeasurableSet M.X M.measurableSpace E})
    (hlim : ∀ A B : Set M.X, A ∈ Chapter00.generatedAlgebra S →
      B ∈ Chapter00.generatedAlgebra S →
      cesaroTendsTo
        (fun k ↦ |correlation M A B k - productMeasureValue M A B|) 0) :
    ∀ A B : Set M.X, MeasurableSet A → MeasurableSet B →
      cesaroTendsTo
        (fun k ↦ |correlation M A B k - productMeasureValue M A B|) 0 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hAlg := generatedAlgebra_isAlgebra S
  have hUnion : ∀ E F : Set M.X, E ∈ Chapter00.generatedAlgebra S →
      F ∈ Chapter00.generatedAlgebra S → E ∪ F ∈ Chapter00.generatedAlgebra S := by
    intro E F hE hF
    have hd := hAlg.2.1 Eᶜ (hAlg.2.2 E hE) F hF
    have hc := hAlg.2.2 (Eᶜ \ F) hd
    convert hc using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]
    tauto
  have hSetAlg : MeasureTheory.IsSetAlgebra (Chapter00.generatedAlgebra S) :=
    { empty_mem := hAlg.1
      compl_mem := fun E hE ↦ hAlg.2.2 E hE
      union_mem := fun E F hE hF ↦ hUnion E F hE hF }
  have hMS : M.measurableSpace = MeasurableSpace.generateFrom S := by
    apply MeasurableSpace.ext
    intro E
    change E ∈ {F : Set M.X | @MeasurableSet M.X M.measurableSpace F} ↔
      E ∈ Chapter00.generatedSigmaAlgebra S
    rw [hgen]
  have hMSAlg : M.measurableSpace =
      MeasurableSpace.generateFrom (Chapter00.generatedAlgebra S) :=
    hMS.trans (generateFrom_generatedAlgebra S).symm
  have hdense : M.μ.MeasureDense (Chapter00.generatedAlgebra S) :=
    MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
      M.μ hSetAlg hMSAlg
  intro A B hA hB
  unfold cesaroTendsTo seqTendsTo
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C, hCAlg, hAC⟩ := hdense.approx A hA (by simp) δ hδ
  obtain ⟨D, hDAlg, hBD⟩ := hdense.approx B hB (by simp) δ hδ
  have hC : MeasurableSet C := hdense.measurable C hCAlg
  have hD : MeasurableSet D := hdense.measurable D hDAlg
  have hACreal : M.μ.real (_root_.symmDiff A C) < δ := by
    unfold MeasureTheory.Measure.real
    have ht := (ENNReal.toReal_lt_toReal (by simp) (by simp)).mpr hAC
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  have hBDreal : M.μ.real (_root_.symmDiff B D) < δ := by
    unfold MeasureTheory.Measure.real
    have ht := (ENNReal.toReal_lt_toReal (by simp) (by simp)).mpr hBD
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  let d := M.μ.real (_root_.symmDiff A C) + M.μ.real (_root_.symmDiff B D)
  have hdlt : d < ε / 4 := by
    dsimp [d, δ] at hACreal hBDreal ⊢
    linarith
  have havgbound : ∀ N,
      |cesaroAverage
          (fun k ↦ |correlation M A B k - productMeasureValue M A B|) N -
        cesaroAverage
          (fun k ↦ |correlation M C D k - productMeasureValue M C D|) N| ≤ 2 * d := by
    intro N
    apply abs_cesaroAverage_sub_le
    intro k
    exact abs_absDeviation_sub_le_two_symmDiff M hM A B C D hA hB hC hD k
  have hCD := hlim C D hCAlg hDAlg
  unfold cesaroTendsTo seqTendsTo at hCD
  rw [Metric.tendsto_atTop] at hCD
  obtain ⟨N, hN⟩ := hCD (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmid := hN n hn
  rw [Real.dist_eq, sub_zero] at hmid ⊢
  have hbound := havgbound n
  calc
    |cesaroAverage (fun k ↦ |correlation M A B k - productMeasureValue M A B|) n| ≤
        |cesaroAverage (fun k ↦ |correlation M A B k - productMeasureValue M A B|) n -
          cesaroAverage (fun k ↦ |correlation M C D k - productMeasureValue M C D|) n| +
        |cesaroAverage (fun k ↦ |correlation M C D k - productMeasureValue M C D|) n| := by
      simpa only [sub_add_cancel] using abs_add_le
        (cesaroAverage (fun k ↦ |correlation M A B k - productMeasureValue M A B|) n -
          cesaroAverage (fun k ↦ |correlation M C D k - productMeasureValue M C D|) n)
        (cesaroAverage (fun k ↦ |correlation M C D k - productMeasureValue M C D|) n)
    _ < ε := by linarith

set_option maxHeartbeats 400000 in
lemma seq_on_all_measurable (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (S : SetFamily M.X)
    (hgen : Chapter00.generatedSigmaAlgebra S =
      {E : Set M.X | @MeasurableSet M.X M.measurableSpace E})
    (hlim : ∀ A B : Set M.X, A ∈ Chapter00.generatedAlgebra S →
      B ∈ Chapter00.generatedAlgebra S →
      Tendsto (fun k ↦ correlation M A B k) atTop
        (nhds (productMeasureValue M A B))) :
    ∀ A B : Set M.X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun k ↦ correlation M A B k) atTop
        (nhds (productMeasureValue M A B)) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hAlg := generatedAlgebra_isAlgebra S
  have hUnion : ∀ E F : Set M.X, E ∈ Chapter00.generatedAlgebra S →
      F ∈ Chapter00.generatedAlgebra S → E ∪ F ∈ Chapter00.generatedAlgebra S := by
    intro E F hE hF
    have hd := hAlg.2.1 Eᶜ (hAlg.2.2 E hE) F hF
    have hc := hAlg.2.2 (Eᶜ \ F) hd
    convert hc using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]
    tauto
  have hSetAlg : MeasureTheory.IsSetAlgebra (Chapter00.generatedAlgebra S) :=
    { empty_mem := hAlg.1
      compl_mem := fun E hE ↦ hAlg.2.2 E hE
      union_mem := fun E F hE hF ↦ hUnion E F hE hF }
  have hMS : M.measurableSpace = MeasurableSpace.generateFrom S := by
    apply MeasurableSpace.ext
    intro E
    change E ∈ {F : Set M.X | @MeasurableSet M.X M.measurableSpace F} ↔
      E ∈ Chapter00.generatedSigmaAlgebra S
    rw [hgen]
  have hMSAlg : M.measurableSpace =
      MeasurableSpace.generateFrom (Chapter00.generatedAlgebra S) :=
    hMS.trans (generateFrom_generatedAlgebra S).symm
  have hdense : M.μ.MeasureDense (Chapter00.generatedAlgebra S) :=
    MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
      M.μ hSetAlg hMSAlg
  intro A B hA hB
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C, hCAlg, hAC⟩ := hdense.approx A hA (by simp) δ hδ
  obtain ⟨D, hDAlg, hBD⟩ := hdense.approx B hB (by simp) δ hδ
  have hC : MeasurableSet C := hdense.measurable C hCAlg
  have hD : MeasurableSet D := hdense.measurable D hDAlg
  have hACreal : M.μ.real (_root_.symmDiff A C) < δ := by
    unfold MeasureTheory.Measure.real
    have ht := (ENNReal.toReal_lt_toReal (by simp) (by simp)).mpr hAC
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  have hBDreal : M.μ.real (_root_.symmDiff B D) < δ := by
    unfold MeasureTheory.Measure.real
    have ht := (ENNReal.toReal_lt_toReal (by simp) (by simp)).mpr hBD
    simpa [ENNReal.toReal_ofReal hδ.le] using ht
  let d := M.μ.real (_root_.symmDiff A C) + M.μ.real (_root_.symmDiff B D)
  have hdlt : d < ε / 4 := by
    dsimp [d, δ] at hACreal hBDreal ⊢
    linarith
  have hcorrbound : ∀ n, |correlation M A B n - correlation M C D n| ≤ d :=
    fun n ↦ abs_correlation_sub_le_symmDiff M hM A B C D hA hB hC hD n
  have hprodbound :
      |productMeasureValue M A B - productMeasureValue M C D| ≤ d :=
    abs_productMeasureValue_sub_le_symmDiff M hM A B C D hA hB hC hD
  have hCD := hlim C D hCAlg hDAlg
  rw [Metric.tendsto_atTop] at hCD
  obtain ⟨N, hN⟩ := hCD (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmid := hN n hn
  rw [Real.dist_eq] at hmid ⊢
  calc
    |correlation M A B n - productMeasureValue M A B| ≤
        |correlation M A B n - correlation M C D n| +
        |correlation M C D n - productMeasureValue M C D| +
        |productMeasureValue M C D - productMeasureValue M A B| := by
      calc
        _ = |(correlation M A B n - correlation M C D n) +
            (correlation M C D n - productMeasureValue M C D) +
            (productMeasureValue M C D - productMeasureValue M A B)| := by ring_nf
        _ ≤ |(correlation M A B n - correlation M C D n) +
            (correlation M C D n - productMeasureValue M C D)| +
            |productMeasureValue M C D - productMeasureValue M A B| := abs_add_le _ _
        _ ≤ _ := by
          nlinarith [abs_add_le
            (correlation M A B n - correlation M C D n)
            (correlation M C D n - productMeasureValue M C D)]
    _ < ε := by
      rw [abs_sub_comm (productMeasureValue M C D)]
      linarith [hcorrbound n, hprodbound]

end CorrelationSemiAlgebra
end Chapter02
