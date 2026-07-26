import Chapter02.Ergodic.CorrelationSemiAlgebra
import Chapter00.Section01
import Chapter01.Coding.MarkovCoding

noncomputable section

open Classical Filter
open scoped BigOperators ENNReal

namespace Chapter02
namespace BernoulliMixing

private theorem alphabetProbabilityMeasure_isProbabilityMeasure
    (k : ℕ) (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    MeasureTheory.IsProbabilityMeasure (Chapter01.alphabetProbabilityMeasure k p) := by
  constructor
  change (∑ i : Fin k, (ENNReal.ofReal (p i) • MeasureTheory.Measure.dirac i)) Set.univ = 1
  rw [MeasureTheory.Measure.finset_sum_apply]
  simp_rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply]
  simp only [Set.indicator_of_mem, Set.mem_univ, smul_eq_mul, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := p)
    (fun i _ ↦ hp i)]
  simp [hsum]

private theorem alphabetProbabilityMeasure_singleton
    (k : ℕ) (p : Fin k → ℝ) (i : Fin k) :
    Chapter01.alphabetProbabilityMeasure k p ({i} : Set (Fin k)) =
      ENNReal.ofReal (p i) := by
  rw [Chapter01.alphabetProbabilityMeasure,
    MeasureTheory.Measure.finset_sum_apply]
  simp [MeasureTheory.Measure.smul_apply, Pi.single_apply]

private theorem infinitePi_wordCylinder
    (k : ℕ) (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (h : ℤ) (word : List (Fin k)) :
    (MeasureTheory.Measure.infinitePi
      (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p))
        (Chapter00.twoSidedCylinder h word) =
      ENNReal.ofReal ((word.map p).prod) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (Chapter01.alphabetProbabilityMeasure k p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  let emb : Fin word.length ↪ ℤ :=
    ⟨fun i ↦ h + (i : ℕ), by
      intro i j hij
      apply Fin.ext
      exact_mod_cast (add_left_cancel hij : (i : ℤ) = (j : ℤ))⟩
  let s : Finset ℤ := Finset.univ.map emb
  let e0 : Fin word.length → {z // z ∈ s} := fun i ↦ ⟨emb i, by simp [s]⟩
  have he0 : Function.Bijective e0 := by
    constructor
    · intro i j hij
      apply emb.injective
      exact congrArg Subtype.val hij
    · intro z
      have hz : z.1 ∈ Finset.univ.map emb := by simpa [s] using z.2
      rcases Finset.mem_map.1 hz with ⟨i, _hi, hiz⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hiz
  let e : Fin word.length ≃ {z // z ∈ s} := Equiv.ofBijective e0 he0
  let t : ℤ → Set (Fin k) := fun z ↦
    if hz : z ∈ s then {word.get (e.symm ⟨z, hz⟩)} else Set.univ
  have hset : Chapter00.twoSidedCylinder h word = Set.pi s t := by
    ext x
    simp only [Chapter00.twoSidedCylinder, Set.mem_setOf_eq, Set.mem_pi]
    constructor
    · intro hx z hz
      change z ∈ s at hz
      rcases Finset.mem_map.1 hz with ⟨i, _hi, rfl⟩
      have hi : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi⟩ : {z // z ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      have ht : t (emb i) = ({word.get i} : Set (Fin k)) := by
        simp [t, hi, he]
      rw [ht]
      exact Set.mem_singleton_iff.mpr (by simpa [emb] using (hx i).symm)
    · intro hx i
      have hi : emb i ∈ s := by simp [s]
      have hxi := hx (emb i) hi
      have hsub : (⟨emb i, hi⟩ : {z // z ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      have ht : t (emb i) = ({word.get i} : Set (Fin k)) := by
        simp [t, hi, he]
      rw [ht] at hxi
      simpa [emb] using (Set.mem_singleton_iff.mp hxi).symm
  rw [hset, MeasureTheory.Measure.infinitePi_pi]
  · rw [show s = Finset.univ.map emb by rfl, Finset.prod_map]
    simp_rw [show ∀ i : Fin word.length,
      Chapter01.alphabetProbabilityMeasure k p (t (emb i)) =
        ENNReal.ofReal (p (word.get i)) by
      intro i
      have hi : emb i ∈ s := by simp [s]
      have hsub : (⟨emb i, hi⟩ : {z // z ∈ s}) = e i := by
        apply Subtype.ext
        rfl
      have he : e.symm ⟨emb i, hi⟩ = i := by
        rw [hsub, e.symm_apply_apply]
      simp [t, hi, he, alphabetProbabilityMeasure_singleton]]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    · simp
    · intro i hi
      exact hp _
  · intro z hz
    simp [t, hz]

def coordinateSetFamily (ι : Type*) (k : ℕ) : Set (Set (ι → Fin k)) :=
  {A | ∃ i : ι, ∃ a : Fin k, A = {x | x i = a}}

theorem coordinateSetFamily_generate {ι : Type*} [Countable ι] (k : ℕ) :
    Chapter00.generatedSigmaAlgebra (coordinateSetFamily ι k) =
      {A : Set (ι → Fin k) | MeasurableSet A} := by
  apply Set.ext
  intro A
  change @MeasurableSet (ι → Fin k)
      (MeasurableSpace.generateFrom (coordinateSetFamily ι k)) A ↔ MeasurableSet A
  have hms : (inferInstance : MeasurableSpace (ι → Fin k)) =
      MeasurableSpace.generateFrom (coordinateSetFamily ι k) := by
    apply le_antisymm
    · rw [MeasurableSpace.pi_eq_generateFrom_projections]
      apply MeasurableSpace.generateFrom_le
      rintro _ ⟨i, B, _hB, rfl⟩
      letI : MeasurableSpace (ι → Fin k) :=
        MeasurableSpace.generateFrom (coordinateSetFamily ι k)
      have heq : (fun x : ι → Fin k ↦ x i) ⁻¹' B =
          ⋃ a : {a : Fin k // a ∈ B}, {x | x i = a.1} := by
        ext x
        simp
      rw [heq]
      apply MeasurableSet.iUnion
      intro a
      exact MeasurableSpace.measurableSet_generateFrom ⟨i, a.1, rfl⟩
    · apply MeasurableSpace.generateFrom_le
      rintro _ ⟨i, a, rfl⟩
      exact measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  rw [← hms]

def DependsOnFiniteCoordinates {ι : Type*} {k : ℕ} (A : Set (ι → Fin k)) : Prop :=
  ∃ s : Finset ι, ∀ x y, (∀ i ∈ s, x i = y i) → (x ∈ A ↔ y ∈ A)

private theorem finiteCoordinateSets_isAlgebra {ι : Type*} {k : ℕ} :
    Chapter00.IsAlgebra {A : Set (ι → Fin k) | DependsOnFiniteCoordinates A} := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨∅, ?_⟩
    simp
  · intro A hA B hB
    rcases hA with ⟨s, hs⟩
    rcases hB with ⟨t, ht⟩
    refine ⟨s ∪ t, ?_⟩
    intro x y hxy
    have hxs : ∀ i ∈ s, x i = y i := fun i hi ↦ hxy i (Finset.mem_union_left t hi)
    have hxt : ∀ i ∈ t, x i = y i := fun i hi ↦ hxy i (Finset.mem_union_right s hi)
    simpa only [Set.mem_diff] using and_congr (hs x y hxs) (not_congr (ht x y hxt))
  · intro A hA
    rcases hA with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    intro x y hxy
    simpa only [Set.mem_compl_iff] using not_congr (hs x y hxy)

theorem generatedAlgebra_dependsOnFiniteCoordinates {ι : Type*} {k : ℕ}
    {A : Set (ι → Fin k)}
    (hA : A ∈ Chapter00.generatedAlgebra (coordinateSetFamily ι k)) :
    DependsOnFiniteCoordinates A := by
  rw [Chapter00.generatedAlgebra] at hA
  apply hA
  refine ⟨finiteCoordinateSets_isAlgebra, ?_⟩
  rintro C ⟨i, a, rfl⟩
  refine ⟨{i}, ?_⟩
  intro x y hxy
  have hi := hxy i (by simp)
  simp only [Set.mem_setOf_eq]
  rw [hi]

private def restrictionEvent {ι : Type*} {k : ℕ}
    (A : Set (ι → Fin k)) (s : Finset ι) : Set (s → Fin k) :=
  {u | ∃ x ∈ A, ∀ i : s, u i = x i}

private theorem preimage_restrictionEvent_of_depends {ι : Type*} {k : ℕ}
    {A : Set (ι → Fin k)} {s : Finset ι}
    (hA : ∀ x y, (∀ i ∈ s, x i = y i) → (x ∈ A ↔ y ∈ A)) :
    (fun x : ι → Fin k ↦ fun i : s ↦ x i) ⁻¹' restrictionEvent A s = A := by
  ext x
  constructor
  · rintro ⟨y, hyA, hxy⟩
    exact (hA y x (fun i hi ↦ (hxy ⟨i, hi⟩).symm)).mp hyA
  · intro hxA
    exact ⟨x, hxA, fun _ ↦ rfl⟩

private theorem infinitePi_inter_eq_mul_of_disjoint
    {ι : Type*} [Countable ι] {k : ℕ}
    (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (A C : Set (ι → Fin k)) (s t : Finset ι) (hst : Disjoint s t)
    (hA : ∀ x y, (∀ i ∈ s, x i = y i) → (x ∈ A ↔ y ∈ A))
    (hC : ∀ x y, (∀ i ∈ t, x i = y i) → (x ∈ C ↔ y ∈ C)) :
    let μ := MeasureTheory.Measure.infinitePi
      (fun _ : ι ↦ Chapter01.alphabetProbabilityMeasure k p)
    μ (A ∩ C) = μ A * μ C := by
  letI : MeasureTheory.IsProbabilityMeasure
      (Chapter01.alphabetProbabilityMeasure k p) :=
    alphabetProbabilityMeasure_isProbabilityMeasure k p hp hsum
  let μ := MeasureTheory.Measure.infinitePi
    (fun _ : ι ↦ Chapter01.alphabetProbabilityMeasure k p)
  have hind : ProbabilityTheory.iIndepFun
      (fun i (ω : ι → Fin k) ↦ ω i) μ :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ x ↦ x) (by fun_prop)
  have hpair := ProbabilityTheory.iIndepFun.indepFun_finset s t hst hind
    (fun _ ↦ measurable_pi_apply _)
  have hmeasure := hpair.measure_inter_preimage_eq_mul
    (restrictionEvent A s) (restrictionEvent C t)
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  rw [preimage_restrictionEvent_of_depends hA,
    preimage_restrictionEvent_of_depends hC] at hmeasure
  exact hmeasure

private theorem oneSidedShift_iterate (k n : ℕ) (x : ℕ → Fin k) (i : ℕ) :
    ((Chapter01.oneSidedShift^[n]) x) i = x (i + n) := by
  induction n generalizing x i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      rw [ih]
      simp only [Chapter01.oneSidedShift]
      congr 1

theorem canonicalOneSidedStrongMixing (k : ℕ) (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsStrongMixing (Chapter01.oneSidedBernoulliSystem k p) := by
  let M := Chapter01.oneSidedBernoulliSystem k p
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.Section02.oneSidedBernoulliExampleSystem_mps k p hp hsum
  refine ⟨hM, ?_⟩
  have hgen : Chapter00.generatedSigmaAlgebra (coordinateSetFamily ℕ k) =
      {E : Set (ℕ → Fin k) | MeasurableSet E} :=
    coordinateSetFamily_generate (ι := ℕ) k
  apply CorrelationSemiAlgebra.seq_on_all_measurable M hM
    (coordinateSetFamily ℕ k) hgen
  intro A B hAAlg hBAlg
  rcases generatedAlgebra_dependsOnFiniteCoordinates hAAlg with ⟨s, hAs⟩
  rcases generatedAlgebra_dependsOnFiniteCoordinates hBAlg with ⟨t, hBt⟩
  let N : ℕ := ∑ i ∈ s, (i + 1)
  have hAmeas : MeasurableSet A := by
    have h := CorrelationSemiAlgebra.generatedAlgebra_subset_generatedSigmaAlgebra
      (coordinateSetFamily ℕ k) hAAlg
    simpa [coordinateSetFamily_generate (ι := ℕ) k] using h
  have hBmeas : MeasurableSet B := by
    have h := CorrelationSemiAlgebra.generatedAlgebra_subset_generatedSigmaAlgebra
      (coordinateSetFamily ℕ k) hBAlg
    simpa [coordinateSetFamily_generate (ι := ℕ) k] using h
  have hevent : ∀ n ≥ N,
      correlation M A B n = productMeasureValue M A B := by
    intro n hn
    let emb : ℕ ↪ ℕ :=
      ⟨fun i ↦ i + n, fun a b hab ↦ Nat.add_right_cancel hab⟩
    let u : Finset ℕ := t.map emb
    have hsu : Disjoint s u := by
      rw [Finset.disjoint_left]
      intro i hiS hiU
      change i ∈ t.map emb at hiU
      rcases Finset.mem_map.1 hiU with ⟨j, _hj, hji⟩
      have hibound : i + 1 ≤ N := by
        dsimp [N]
        exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le (q + 1)) hiS
      have hijn : i = j + n := by simpa [emb] using hji.symm
      omega
    have hC : ∀ x y : ℕ → Fin k, (∀ i ∈ u, x i = y i) →
        (x ∈ preimageIter M n B ↔ y ∈ preimageIter M n B) := by
      intro x y hxy
      apply hBt
      intro i hi
      have hiu : emb i ∈ u := Finset.mem_map.2 ⟨i, hi, rfl⟩
      have hcoord := hxy (emb i) hiu
      change ((Chapter01.oneSidedShift^[n]) x) i =
        ((Chapter01.oneSidedShift^[n]) y) i
      rw [oneSidedShift_iterate, oneSidedShift_iterate]
      simpa [emb] using hcoord
    have hfac := infinitePi_inter_eq_mul_of_disjoint p hp hsum A
      (preimageIter M n B) s u hsu hAs hC
    have hpre : M.μ (preimageIter M n B) = M.μ B := by
      change M.μ ((M.T^[n]) ⁻¹' B) = M.μ B
      exact (hM.2.iterate n).measure_preimage hBmeas.nullMeasurableSet
    unfold correlation productMeasureValue realMeasure
    change (MeasureTheory.Measure.infinitePi
      (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p))
        (A ∩ preimageIter M n B) =
      (MeasureTheory.Measure.infinitePi
        (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p)) A *
      (MeasureTheory.Measure.infinitePi
        (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p))
          (preimageIter M n B) at hfac
    change (MeasureTheory.Measure.infinitePi
      (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p))
        (preimageIter M n B) =
      (MeasureTheory.Measure.infinitePi
        (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p)) B at hpre
    change ((MeasureTheory.Measure.infinitePi
      (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p))
        (A ∩ preimageIter M n B)).toReal =
      ((MeasureTheory.Measure.infinitePi
        (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p)) A).toReal *
      ((MeasureTheory.Measure.infinitePi
        (fun _ : ℕ ↦ Chapter01.alphabetProbabilityMeasure k p)) B).toReal
    rw [hfac, hpre, ENNReal.toReal_mul]
  exact Filter.Tendsto.congr'
    (eventually_atTop.2 ⟨N, fun n hn ↦ (hevent n hn).symm⟩) tendsto_const_nhds

private def bilateralShift {k : ℕ} (x : ℤ → Fin k) : ℤ → Fin k :=
  fun i ↦ x (i + 1)

private theorem bilateralShift_iterate (k n : ℕ) (x : ℤ → Fin k) (i : ℤ) :
    ((bilateralShift^[n]) x) i = x (i + n) := by
  induction n generalizing x i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [bilateralShift]
      congr 1
      omega

theorem canonicalTwoSidedStrongMixing (k : ℕ) (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsStrongMixing (Chapter01.Section02.twoSidedBernoulliExampleSystem k p) := by
  let M := Chapter01.Section02.twoSidedBernoulliExampleSystem k p
  have hM : Chapter01.IsMeasurePreservingSystem M :=
    Chapter01.Section02.twoSidedBernoulliExampleSystem_mps k p hp hsum
  refine ⟨hM, ?_⟩
  have hgen : Chapter00.generatedSigmaAlgebra (coordinateSetFamily ℤ k) =
      {E : Set (ℤ → Fin k) | MeasurableSet E} :=
    coordinateSetFamily_generate (ι := ℤ) k
  apply CorrelationSemiAlgebra.seq_on_all_measurable M hM
    (coordinateSetFamily ℤ k) hgen
  intro A B hAAlg hBAlg
  rcases generatedAlgebra_dependsOnFiniteCoordinates hAAlg with ⟨s, hAs⟩
  rcases generatedAlgebra_dependsOnFiniteCoordinates hBAlg with ⟨t, hBt⟩
  let Ns : ℕ := ∑ i ∈ s, (Int.natAbs i + 1)
  let Nt : ℕ := ∑ i ∈ t, (Int.natAbs i + 1)
  let N : ℕ := Ns + Nt + 1
  have hBmeas : MeasurableSet B := by
    have h := CorrelationSemiAlgebra.generatedAlgebra_subset_generatedSigmaAlgebra
      (coordinateSetFamily ℤ k) hBAlg
    simpa [coordinateSetFamily_generate (ι := ℤ) k] using h
  have hevent : ∀ n ≥ N,
      correlation M A B n = productMeasureValue M A B := by
    intro n hn
    let emb : ℤ ↪ ℤ :=
      ⟨fun i ↦ i + (n : ℤ), fun a b hab ↦ add_right_cancel hab⟩
    let u : Finset ℤ := t.map emb
    have hsu : Disjoint s u := by
      rw [Finset.disjoint_left]
      intro i hiS hiU
      change i ∈ t.map emb at hiU
      rcases Finset.mem_map.1 hiU with ⟨j, hjT, hji⟩
      have hibound : Int.natAbs i + 1 ≤ Ns := by
        dsimp [Ns]
        exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le (Int.natAbs q + 1)) hiS
      have hjbound : Int.natAbs j + 1 ≤ Nt := by
        dsimp [Nt]
        exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le (Int.natAbs q + 1)) hjT
      have heq : i = j + (n : ℤ) := by simpa [emb] using hji.symm
      have hnabs : n = Int.natAbs (i - j) := by
        rw [heq]
        simp
      have htri : Int.natAbs (i - j) ≤ Int.natAbs i + Int.natAbs j :=
        Int.natAbs_sub_le i j
      dsimp [N] at hn
      omega
    have hC : ∀ x y : ℤ → Fin k, (∀ i ∈ u, x i = y i) →
        (x ∈ preimageIter M n B ↔ y ∈ preimageIter M n B) := by
      intro x y hxy
      apply hBt
      intro i hi
      have hiu : emb i ∈ u := Finset.mem_map.2 ⟨i, hi, rfl⟩
      have hcoord := hxy (emb i) hiu
      change ((bilateralShift^[n]) x) i = ((bilateralShift^[n]) y) i
      rw [bilateralShift_iterate, bilateralShift_iterate]
      simpa [emb] using hcoord
    have hfac := infinitePi_inter_eq_mul_of_disjoint p hp hsum A
      (preimageIter M n B) s u hsu hAs hC
    have hpre : M.μ (preimageIter M n B) = M.μ B := by
      change M.μ ((M.T^[n]) ⁻¹' B) = M.μ B
      exact (hM.2.iterate n).measure_preimage hBmeas.nullMeasurableSet
    unfold correlation productMeasureValue realMeasure
    change (MeasureTheory.Measure.infinitePi
      (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p))
        (A ∩ preimageIter M n B) =
      (MeasureTheory.Measure.infinitePi
        (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p)) A *
      (MeasureTheory.Measure.infinitePi
        (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p))
          (preimageIter M n B) at hfac
    change (MeasureTheory.Measure.infinitePi
      (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p))
        (preimageIter M n B) =
      (MeasureTheory.Measure.infinitePi
        (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p)) B at hpre
    change ((MeasureTheory.Measure.infinitePi
      (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p))
        (A ∩ preimageIter M n B)).toReal =
      ((MeasureTheory.Measure.infinitePi
        (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p)) A).toReal *
      ((MeasureTheory.Measure.infinitePi
        (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p)) B).toReal
    rw [hfac, hpre, ENNReal.toReal_mul]
  exact Filter.Tendsto.congr'
    (eventually_atTop.2 ⟨N, fun n hn ↦ (hevent n hn).symm⟩) tendsto_const_nhds

private theorem iterate_conjugacy {M : System.{u}} {N : System.{v}}
    (e : M.X ≃ N.X) (hT : ∀ x, e (M.T x) = N.T (e x))
    (n : ℕ) (x : M.X) : e ((M.T^[n]) x) = (N.T^[n]) (e x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hT]

theorem strongMixing_of_measurable_conjugacy {M : System.{u}} {N : System.{v}}
    (hM : Chapter01.IsMeasurePreservingSystem M) (hN : IsStrongMixing N)
    (e : M.X ≃ N.X) (he : Measurable e) (heinv : Measurable e.symm)
    (hmap : MeasureTheory.Measure.map e M.μ = N.μ)
    (hT : ∀ x, e (M.T x) = N.T (e x)) : IsStrongMixing M := by
  refine ⟨hM, ?_⟩
  intro A B hA hB
  let A' : Set N.X := e.symm ⁻¹' A
  let B' : Set N.X := e.symm ⁻¹' B
  have hA' : MeasurableSet A' := heinv hA
  have hB' : MeasurableSet B' := heinv hB
  have hmeasure : ∀ C : Set N.X, MeasurableSet C → M.μ (e ⁻¹' C) = N.μ C := by
    intro C hC
    calc
      M.μ (e ⁻¹' C) = MeasureTheory.Measure.map e M.μ C := by
        rw [MeasureTheory.Measure.map_apply he hC]
      _ = N.μ C := by rw [hmap]
  have hpreA : e ⁻¹' A' = A := by
    ext x
    simp [A']
  have hpreB : e ⁻¹' B' = B := by
    ext x
    simp [B']
  have hcorr : ∀ n, correlation M A B n = correlation N A' B' n := by
    intro n
    have hset : A ∩ preimageIter M n B =
        e ⁻¹' (A' ∩ preimageIter N n B') := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, preimageIter,
        Chapter01.iterateMap]
      rw [← hpreA, ← hpreB]
      simp only [Set.mem_preimage]
      rw [iterate_conjugacy e hT n x]
    have htarget : MeasurableSet (A' ∩ preimageIter N n B') :=
      hA'.inter (hB'.preimage (hN.1.2.iterate n).measurable)
    unfold correlation realMeasure
    rw [hset, hmeasure _ htarget]
  have hprod : productMeasureValue M A B = productMeasureValue N A' B' := by
    unfold productMeasureValue realMeasure
    rw [← hpreA, ← hpreB, hmeasure A' hA', hmeasure B' hB']
  rw [hprod]
  exact (hN.2 A' B' hA' hB').congr'
    (Filter.Eventually.of_forall fun n ↦ (hcorr n).symm)

private theorem oneSided_map_eq {M : System.{u}} (k : ℕ) (p : Fin k → ℝ)
    (h : Chapter01.IsOneSidedBernoulliShiftWith M k p) :
    ∃ e : M.X ≃ (ℕ → Fin k),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e M.μ = Chapter01.oneSidedBernoulliMeasure k p ∧
      (∀ x n, e (M.T x) n = e x (n + 1)) := by
  rcases h with ⟨hM, e, he, heinv, hp, hsum, hT, hcyl⟩
  refine ⟨e, he, heinv, ?_, hT⟩
  let ν := MeasureTheory.Measure.map e M.μ
  let μ := Chapter01.oneSidedBernoulliMeasure k p
  have hfin : ∀ n : ℕ,
      MeasureTheory.Measure.map (Chapter01.finitePrefix n) ν =
        MeasureTheory.Measure.map (Chapter01.finitePrefix n) μ := by
    intro n
    apply MeasureTheory.Measure.ext_of_singleton
    intro a
    have hfiber : MeasurableSet
        (Chapter01.finitePrefix n ⁻¹' ({a} : Set (Fin (n + 1) → Fin k))) :=
      (Chapter01.finitePrefix_measurable n) (MeasurableSet.singleton a)
    rw [MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
      (MeasurableSet.singleton a)]
    change MeasureTheory.Measure.map e M.μ
      (Chapter01.finitePrefix n ⁻¹' {a}) = _
    rw [MeasureTheory.Measure.map_apply he hfiber]
    have hsource : e ⁻¹' (Chapter01.finitePrefix n ⁻¹' {a}) =
        {x | ∀ i : Fin (n + 1), e x i = a i} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · intro hx i
        exact congrFun hx i
      · intro hx
        funext i
        exact hx i
    rw [hsource, hcyl n a]
    rw [MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
      (MeasurableSet.singleton a)]
    have htarget : Chapter01.finitePrefix n ⁻¹' {a} =
        {x : ℕ → Fin k | ∀ i : Fin (n + 1), x i = a i} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      constructor
      · intro hx i
        exact congrFun hx i
      · intro hx
        funext i
        exact hx i
    rw [htarget]
    exact (Chapter01.Section02.oneSidedBernoulli_cylinder k n a p hp hsum).symm
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset
    (Chapter01.markovPrefixSetFamily_generate k)
    (Chapter01.markovPrefixSetFamily_piSystem k) (T := {Set.univ})
  · intro C hC
    subst C
    exact ⟨0, Set.univ, by simp⟩
  · exact Set.countable_singleton _
  · simp
  · intro C hC
    have hCu : C = Set.univ := Set.mem_singleton_iff.mp hC
    subst C
    rw [MeasureTheory.Measure.map_apply he MeasurableSet.univ]
    simp only [Set.preimage_univ]
    change (Chapter01.MeasurePreservingSystemData.toProbabilitySpace M).μ Set.univ ≠ ∞
    rw [hM.1.measure_univ]
    norm_num
  · rintro C ⟨n, A, rfl⟩
    rw [← MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
        (Set.toFinite A).measurableSet,
      ← MeasureTheory.Measure.map_apply (Chapter01.finitePrefix_measurable n)
        (Set.toFinite A).measurableSet, hfin n]

private theorem twoSided_map_eq {M : System.{u}} (k : ℕ) (p : Fin k → ℝ)
    (h : Chapter01.IsTwoSidedBernoulliShiftWith M k p) :
    ∃ e : M.X ≃ (ℤ → Fin k),
      Measurable e ∧ Measurable e.symm ∧
      MeasureTheory.Measure.map e M.μ =
        MeasureTheory.Measure.infinitePi
          (fun _ : ℤ ↦ Chapter01.alphabetProbabilityMeasure k p) ∧
      (∀ x n, e (M.T x) n = e x (n + 1)) := by
  rcases h with ⟨_hM, e, he, heinv, hmap, _hp, _hsum, hT, _hcyl⟩
  exact ⟨e, he, heinv, hmap, hT⟩

theorem bernoulliShiftStrongMixing : BernoulliShiftStrongMixingStatement := by
  intro M hB
  rcases hB with ⟨k, hone | htwo⟩
  · rcases hone with ⟨p, hp⟩
    have hp' := hp
    rcases hp with ⟨hM, _e, _he, _heinv, hpnonneg, hpsum, _hT, _hcyl⟩
    rcases oneSided_map_eq k p hp' with ⟨e, he, heinv, hmap, hT⟩
    apply strongMixing_of_measurable_conjugacy hM
      (canonicalOneSidedStrongMixing k p hpnonneg hpsum) e he heinv hmap
    intro x
    funext n
    exact hT x n
  · rcases htwo with ⟨p, hp⟩
    have hp' := hp
    rcases hp with ⟨hM, _e, _he, _heinv, _hmap, hpnonneg, hpsum, _hT, _hcyl⟩
    rcases twoSided_map_eq k p hp' with ⟨e, he, heinv, hmap, hT⟩
    apply strongMixing_of_measurable_conjugacy hM
      (canonicalTwoSidedStrongMixing k p hpnonneg hpsum) e he heinv hmap
    intro x
    funext n
    exact hT x n

end BernoulliMixing
end Chapter02
