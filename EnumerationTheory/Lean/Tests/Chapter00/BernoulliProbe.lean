import Chapter00.Section01

#check MeasureTheory.Measure.eq_infinitePi
#check MeasureTheory.Measure.ext
#check MeasurableSpace.pi_eq_generateFrom_projections
#check MeasureTheory.Measure.infinitePi_pi
#check MeasureTheory.Measure.finset_sum_apply
#check List.prod_nonneg
#check List.prod_append
#check Finset.sum_mul
#check Finset.mul_sum
#check Finset.sum_congr
#check List.prod_eq_one
#check List.prod_eq_one_iff
#check MeasureTheory.IsProbabilityMeasure.measure_univ

open Classical
open scoped BigOperators

namespace Chapter00
namespace Section01

example (k : ℕ) (p : Fin k -> ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 ->
      0 ≤ (word.map p).prod := by
  intro n word _hlen
  exact List.prod_nonneg (by
    intro r hr
    rcases List.mem_map.mp hr with ⟨a, _ha, rfl⟩
    exact hp a)

example (k : ℕ) (p : Fin k -> ℝ) (hsum : Finset.univ.sum p = 1) :
    ∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 ->
      (word.map p).prod =
        Finset.univ.sum fun a : Fin k => ((word ++ [a]).map p).prod := by
  intro n word _hlen
  have hterm : ∀ a : Fin k,
      ((word ++ [a]).map p).prod = (word.map p).prod * p a := by
    intro a
    simp [List.map_append, List.prod_append]
  calc
    (word.map p).prod = (word.map p).prod * (Finset.univ.sum p) := by
      rw [hsum, mul_one]
    _ = Finset.univ.sum (fun a : Fin k => (word.map p).prod * p a) := by
      rw [Finset.mul_sum]
    _ = Finset.univ.sum fun a : Fin k => ((word ++ [a]).map p).prod := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact (hterm a).symm

example (k : ℕ) (p : Fin k -> ℝ) (hsum : Finset.univ.sum p = 1) :
    ∀ n : ℕ, ∀ word : List (Fin k), word.length = n + 1 ->
      (word.map p).prod =
        Finset.univ.sum fun a : Fin k => ((a :: word).map p).prod := by
  intro n word _hlen
  have hterm : ∀ a : Fin k,
      ((a :: word).map p).prod = p a * (word.map p).prod := by
    intro a
    simp
  calc
    (word.map p).prod = (Finset.univ.sum p) * (word.map p).prod := by
      rw [hsum, one_mul]
    _ = Finset.univ.sum (fun a : Fin k => p a * (word.map p).prod) := by
      rw [Finset.sum_mul]
    _ = Finset.univ.sum fun a : Fin k => ((a :: word).map p).prod := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact (hterm a).symm

example (k : ℕ) (h : ¬ 2 ≤ k) : k = 0 ∨ k = 1 := by
  omega

example (p : Fin 0 -> ℝ) (hsum : Finset.univ.sum p = 1) : False := by
  have h01 : (0 : ℝ) = 1 := by
    simpa using hsum
  norm_num at h01

end Section01
end Chapter00
