import Chapter04.Common

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter04

universe u

/-- The measurable sets of a probability space, modulo null symmetric difference,
form a measure algebra. -/
theorem isMeasureAlgebra_inducedMeasureAlgebra (P : ProbabilitySpace.{u})
    (hP : Chapter01.IsProbabilitySpace P) :
    IsMeasureAlgebra (inducedMeasureAlgebra P) := by
  letI : MeasureTheory.IsProbabilityMeasure P.μ := hP
  have ae_iff (A B : (inducedMeasureAlgebra P).carrier) :
      (inducedMeasureAlgebra P).equiv A B ↔ A.1 =ᵐ[P.μ] B.1 := by
    exact MeasureTheory.measure_symmDiff_eq_zero_iff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro A
      exact (ae_iff A A).mpr EventuallyEq.rfl
    · intro A B hAB
      exact (ae_iff B A).mpr ((ae_iff A B).mp hAB).symm
    · intro A B C hAB hBC
      exact (ae_iff A C).mpr (((ae_iff A B).mp hAB).trans ((ae_iff B C).mp hBC))
  · intro A B A' B' hA hB
    constructor
    · exact (ae_iff _ _).mpr (((ae_iff A A').mp hA).union ((ae_iff B B').mp hB))
    · exact (ae_iff _ _).mpr (((ae_iff A A').mp hA).inter ((ae_iff B B').mp hB))
  · intro A B hAB
    exact (ae_iff _ _).mpr ((ae_iff A B).mp hAB).compl
  · intro A B hAB
    exact congrArg ENNReal.toReal (MeasureTheory.measure_congr ((ae_iff A B).mp hAB))
  · intro A
    constructor <;> simp [inducedMeasureAlgebra, Chapter00.symmDiff]
  · intro A
    constructor <;> simp [inducedMeasureAlgebra, Chapter00.symmDiff]
  · intro A
    simp [inducedMeasureAlgebra, Chapter00.symmDiff]
  · intro A
    simp [inducedMeasureAlgebra, Chapter00.symmDiff]
  · intro A
    simp [inducedMeasureAlgebra, Chapter00.symmDiff]
  · intro A B
    constructor
    · apply (ae_iff _ _).mpr
      filter_upwards with x
      change (x ∈ A.1 ∨ x ∈ B.1) = (x ∈ B.1 ∨ x ∈ A.1)
      apply propext
      tauto
    · apply (ae_iff _ _).mpr
      filter_upwards with x
      change (x ∈ A.1 ∧ x ∈ B.1) = (x ∈ B.1 ∧ x ∈ A.1)
      apply propext
      tauto
  · intro A B C
    constructor
    · apply (ae_iff _ _).mpr
      filter_upwards with x
      change ((x ∈ A.1 ∨ x ∈ B.1) ∨ x ∈ C.1) =
        (x ∈ A.1 ∨ (x ∈ B.1 ∨ x ∈ C.1))
      apply propext
      tauto
    · apply (ae_iff _ _).mpr
      filter_upwards with x
      change ((x ∈ A.1 ∧ x ∈ B.1) ∧ x ∈ C.1) =
        (x ∈ A.1 ∧ (x ∈ B.1 ∧ x ∈ C.1))
      apply propext
      tauto
  · intro A B C
    constructor
    · apply (ae_iff _ _).mpr
      filter_upwards with x
      change (x ∈ A.1 ∧ (x ∈ B.1 ∨ x ∈ C.1)) =
        ((x ∈ A.1 ∧ x ∈ B.1) ∨ (x ∈ A.1 ∧ x ∈ C.1))
      apply propext
      tauto
    · apply (ae_iff _ _).mpr
      filter_upwards with x
      change (x ∈ A.1 ∨ (x ∈ B.1 ∧ x ∈ C.1)) =
        ((x ∈ A.1 ∨ x ∈ B.1) ∧ (x ∈ A.1 ∨ x ∈ C.1))
      apply propext
      tauto
  · intro f n
    apply (ae_iff _ _).mpr
    filter_upwards with x
    simp only [inducedMeasureAlgebra]
    change (((f n).1 ∩ ⋃ i, (f i).1) x) = (f n).1 x
    apply propext
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, Set.mem_iUnion_of_mem n hx⟩
  · intro f B hsub
    change P.μ (Chapter00.symmDiff ((⋃ n, (f n).1) ∩ B.1) (⋃ n, (f n).1)) = 0
    have hset : Chapter00.symmDiff ((⋃ n, (f n).1) ∩ B.1) (⋃ n, (f n).1) =
        ⋃ n, (f n).1 \ B.1 := by
      ext x
      simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
        Set.mem_inter_iff, Set.mem_iUnion]
      tauto
    rw [hset]
    apply MeasureTheory.measure_iUnion_null
    intro n
    have hn := hsub n
    change P.μ (Chapter00.symmDiff ((f n).1 ∩ B.1) (f n).1) = 0 at hn
    have hnset : Chapter00.symmDiff ((f n).1 ∩ B.1) (f n).1 = (f n).1 \ B.1 := by
      ext x
      simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
      tauto
    rwa [hnset] at hn
  · simp [inducedMeasureAlgebra]
  · intro A
    exact ENNReal.toReal_nonneg
  · intro A
    constructor
    · intro hzero
      have hμ0 : P.μ A.1 = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (P.μ A.1)).mp hzero with h | h
        · exact h
        · exact (MeasureTheory.measure_ne_top P.μ A.1 h).elim
      simpa [inducedMeasureAlgebra, Chapter00.symmDiff] using hμ0
    · intro hzero
      have hμ0 : P.μ A.1 = 0 := by
        simpa [inducedMeasureAlgebra, Chapter00.symmDiff] using hzero
      simpa [inducedMeasureAlgebra, hμ0]
  · intro f hdis
    have hae : Pairwise (Function.onFun (MeasureTheory.AEDisjoint P.μ)
        (fun n => (f n).1)) := by
      intro i j hij
      change P.μ ((f i).1 ∩ (f j).1) = 0
      simpa [inducedMeasureAlgebra, Chapter00.symmDiff] using hdis i j hij
    have hmeasure : P.μ (⋃ n, (f n).1) = ∑' n, P.μ (f n).1 :=
      MeasureTheory.measure_iUnion₀ hae (fun n => (f n).2.nullMeasurableSet)
    change (P.μ (⋃ n, (f n).1)).toReal = ∑' n, (P.μ (f n).1).toReal
    rw [hmeasure]
    exact ENNReal.tsum_toReal_eq (fun n => MeasureTheory.measure_ne_top P.μ (f n).1)

end Chapter04
