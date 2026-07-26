import Chapter02.Section01
import Chapter02.Recurrence.MultipleKhintchineSyndetic

open Classical Filter Set

noncomputable section

namespace Chapter02.MultipleKhintchine

universe u

/-- The existential final clause in the formalized remark.  The quantifier
order and the restriction to positive times match the source: one ergodic
system works for every exponent `l`. -/
theorem exists_system_with_fivefold_upper_bound :
    ∃ N : System.{u}, IsErgodic N ∧ ∀ l : ℕ, ∃ A : Set N.X,
      MeasurableSet A ∧ 0 < N.μ A ∧
      ∀ n : ℕ, 0 < n →
        realMeasure N
          (A ∩ preimageIter N n A ∩ preimageIter N (2 * n) A ∩
            preimageIter N (3 * n) A ∩ preimageIter N (4 * n) A) ≤
          (realMeasure N A) ^ l := by
  obtain ⟨N, hperiodic, hN⟩ :=
    Section01.nPeriodicSystemIsErgodic.{u} 1 (by omega)
  letI : MeasureTheory.IsProbabilityMeasure N.μ := hN.1.1
  refine ⟨N, hN, ?_⟩
  intro l
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · simp
  · intro n hn
    have huniv : N.μ Set.univ = 1 := hN.1.1.measure_univ
    simp [preimageIter, realMeasure, huniv]

end Chapter02.MultipleKhintchine
