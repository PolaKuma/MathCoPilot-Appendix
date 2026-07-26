import Chapter04.Section03

noncomputable section

open Classical

namespace Chapter04

/-- The one-point probability-preserving identity system. -/
def onePointSystem : System.{0} where
  X := PUnit
  measurableSpace := ⊤
  μ := MeasureTheory.Measure.dirac PUnit.unit
  T := id

private lemma punit_set_empty_or_univ (A : Set PUnit) : A = ∅ ∨ A = Set.univ := by
  by_cases h : PUnit.unit ∈ A
  · right
    ext x
    cases x
    simp [h]
  · left
    ext x
    cases x
    simp [h]

lemma onePointSystem_measurePreserving :
    Chapter01.IsMeasurePreservingSystem onePointSystem := by
  constructor
  · change MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.dirac PUnit.unit)
    infer_instance
  · simpa [onePointSystem] using
      (MeasureTheory.MeasurePreserving.id
        (μ := MeasureTheory.Measure.dirac PUnit.unit))

lemma onePointSystem_uniformMixing : Chapter02.IsUniformMixing onePointSystem := by
  refine ⟨onePointSystem_measurePreserving, ?_⟩
  intro A _ k B _ ε hε
  refine ⟨0, ?_⟩
  intro n _ C _
  rcases punit_set_empty_or_univ A with rfl | rfl <;>
    rcases punit_set_empty_or_univ C with rfl | rfl <;>
    simp [Chapter02.realMeasure, onePointSystem, hε]

lemma onePointSystem_not_kolmogorov : ¬ IsKolmogorovSystem onePointSystem := by
  intro hK
  obtain ⟨B, -, hBpos, hBlt⟩ := hK.2.2.2.1
  rcases punit_set_empty_or_univ B with rfl | rfl
  · simpa [onePointSystem] using hBpos
  · simpa [onePointSystem] using hBlt

/-- The reverse implication is false without the nontrivial ambient hypotheses
of the textbook's Theorem 4.3.10. -/
theorem currentKolmogorovIffUniformMixingIsFalse :
    ¬ (IsKolmogorovSystem onePointSystem ↔
      Chapter02.IsUniformMixing onePointSystem) := by
  intro h
  exact onePointSystem_not_kolmogorov (h.mpr onePointSystem_uniformMixing)

end Chapter04
