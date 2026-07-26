import Chapter04.Section04
import Mathlib.Analysis.PSeries

noncomputable section

set_option maxHeartbeats 800000

open Classical Filter
open scoped BigOperators ENNReal

namespace Chapter04

universe u

/-- The measurable finite-measure form of the exhaustion argument used in 4.5.2. -/
theorem exists_measurableUnion_of_hereditary
    (P : ProbabilitySpace.{u}) (𝓗 : Set (Set P.X))
    (hprob : Chapter01.IsProbabilitySpace P)
    (hher : IsHereditaryFamily 𝓗)
    (hmeas : ∀ A ∈ 𝓗, MeasurableSet A) :
    ∃ U : Set P.X, HasMeasurableUnion 𝓗 P.𝓧 P.μ U := by
  let hempty : (∅ : Set P.X) ∈ 𝓗 := by
    obtain ⟨B, hB⟩ := hher.1
    exact hher.2 ∅ B (Set.empty_subset B) hB
  let pick : Set P.X → ℕ → Set P.X := fun U n =>
    if h : ∃ B : Set P.X, B ∈ 𝓗 ∧ B ⊆ Uᶜ ∧
        (1 / ((n : ℝ) + 1)) < P.μ.real B then
      Classical.choose h
    else ∅
  let chosenUnion : ℕ → Set P.X := fun n =>
    Nat.rec ∅ (fun k U => U ∪ pick U k) n
  let A : ℕ → Set P.X := fun n => pick (chosenUnion n) n
  have hpartial_zero : chosenUnion 0 = ∅ := rfl
  have hpartial_succ (n : ℕ) : chosenUnion (n + 1) = chosenUnion n ∪ A n := by
    rfl
  have hpick_spec (n : ℕ) :
      A n ∈ 𝓗 ∧ A n ⊆ (chosenUnion n)ᶜ ∧
        ((∃ B : Set P.X, B ∈ 𝓗 ∧ B ⊆ (chosenUnion n)ᶜ ∧
            (1 / ((n : ℝ) + 1)) < P.μ.real B) →
          (1 / ((n : ℝ) + 1)) < P.μ.real (A n)) := by
    classical
    by_cases h : ∃ B : Set P.X, B ∈ 𝓗 ∧ B ⊆ (chosenUnion n)ᶜ ∧
        (1 / ((n : ℝ) + 1)) < P.μ.real B
    · have hs := Classical.choose_spec h
      dsimp [A, pick]
      rw [dif_pos h]
      exact ⟨hs.1, hs.2.1, fun _ => hs.2.2⟩
    · dsimp [A, pick]
      rw [dif_neg h]
      exact ⟨hempty, Set.empty_subset _, fun hex => (h hex).elim⟩
  have hA_mem (n : ℕ) : A n ∈ 𝓗 := (hpick_spec n).1
  have hA_meas (n : ℕ) : MeasurableSet (A n) := hmeas (A n) (hA_mem n)
  have hA_compl (n : ℕ) : A n ⊆ (chosenUnion n)ᶜ := (hpick_spec n).2.1
  have hpartial_mono : Monotone chosenUnion := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hpartial_succ]
    exact Set.subset_union_left
  have hA_subset_partial_succ (n : ℕ) : A n ⊆ chosenUnion (n + 1) := by
    rw [hpartial_succ]
    exact Set.subset_union_right
  have hA_pairwise : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with hij' | hji'
    · apply Set.disjoint_left.2
      intro x hxi hxj
      have hix : x ∈ chosenUnion j :=
        hpartial_mono (Nat.succ_le_iff.2 hij') (hA_subset_partial_succ i hxi)
      exact (hA_compl j hxj) hix
    · apply Set.disjoint_left.2
      intro x hxi hxj
      have hjx : x ∈ chosenUnion i :=
        hpartial_mono (Nat.succ_le_iff.2 hji') (hA_subset_partial_succ j hxj)
      exact (hA_compl i hxi) hjx
  let U : Set P.X := ⋃ n, A n
  have hU_meas : MeasurableSet U := MeasurableSet.iUnion hA_meas
  refine ⟨U, hU_meas, A, hA_mem, ?_, rfl, ?_⟩
  · intro i j hij
    exact hA_pairwise hij
  · intro B hB
    let C : Set P.X := B \ U
    have hC_mem : C ∈ 𝓗 := hher.2 C B Set.diff_subset hB
    have hC_meas : MeasurableSet C := hmeas C hC_mem
    by_contra hCzero
    have hCpos : 0 < P.μ C := bot_lt_iff_ne_bot.2 hCzero
    have hCfinite : P.μ C ≠ ∞ := by
      apply ne_of_lt
      calc
        P.μ C ≤ P.μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ C)
        _ = 1 := hprob.measure_univ
        _ < ∞ := ENNReal.one_lt_top
    have hCrealpos : 0 < P.μ.real C :=
      ENNReal.toReal_pos (ne_of_gt hCpos) hCfinite
    have hevent : ∀ᶠ n : ℕ in atTop,
        (1 / ((n : ℝ) + 1)) < P.μ.real C := by
      exact (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
        (Iio_mem_nhds hCrealpos)
    obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
    have hpartial_subset_U (n : ℕ) : chosenUnion n ⊆ U := by
      induction n with
      | zero => simp [hpartial_zero]
      | succ n ih =>
          rw [hpartial_succ]
          exact Set.union_subset ih (Set.subset_iUnion A n)
    have hcandidate (n : ℕ) (hn : N ≤ n) :
        ∃ D : Set P.X, D ∈ 𝓗 ∧ D ⊆ (chosenUnion n)ᶜ ∧
          (1 / ((n : ℝ) + 1)) < P.μ.real D := by
      refine ⟨C, hC_mem, ?_, hN n hn⟩
      intro x hxC hxpartial
      exact hxC.2 (hpartial_subset_U n hxpartial)
    have hlarge (n : ℕ) (hn : N ≤ n) :
        (1 / ((n : ℝ) + 1)) < P.μ.real (A n) :=
      (hpick_spec n).2.2 (hcandidate n hn)
    letI : MeasureTheory.IsFiniteMeasure P.μ :=
      MeasureTheory.IsFiniteMeasure.mk (by simp [hprob.measure_univ])
    have hsum : Summable (fun n => P.μ.real (A n)) :=
      MeasureTheory.summable_measure_toReal hA_meas hA_pairwise
    have hsum_tail : Summable (fun n => P.μ.real (A (n + N))) := by
      exact (summable_nat_add_iff N).2 hsum
    have hharm_tail : Summable (fun n : ℕ => 1 / (((n + N : ℕ) : ℝ) + 1)) := by
      apply hsum_tail.of_nonneg_of_le
      · intro n
        positivity
      · intro n
        exact (hlarge (n + N) (Nat.le_add_left N n)).le
    have hharm : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      exact (summable_nat_add_iff N).1 (by simpa [Nat.cast_add] using hharm_tail)
    exact Real.not_summable_one_div_natCast (by
      rw [← summable_nat_add_iff 1]
      simpa [Nat.cast_add] using hharm)

end Chapter04
