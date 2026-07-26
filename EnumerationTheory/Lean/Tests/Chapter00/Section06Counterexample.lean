import Chapter00.Section06

open Classical

namespace Chapter00.Section06Counterexample

universe u

def emptyFamily (X : Type u) : FurstenbergFamily X := ∅

theorem emptyFamily_isFurstenberg (X : Type u) :
    IsFurstenbergFamily (emptyFamily X) := by
  intro A B hA
  exact False.elim hA

theorem product_empty_not_proper (X : Type u) :
    ¬ ProperFamily (familyProduct (emptyFamily X) (emptyFamily X)) := by
  intro h
  have hu := h.2.2
  rcases hu with ⟨A, hA, B, hB, _⟩
  exact hA

theorem empty_subset_dual_empty (X : Type u) :
    emptyFamily X ⊆ familyDual (emptyFamily X) := by
  intro A hA
  exact False.elim hA

theorem emptyFamily_ramsey (X : Type u) :
    HasRamseyProperty (emptyFamily X) := by
  intro A B h
  exact False.elim h

theorem emptyFamily_not_filterDual (X : Type u) :
    ¬ IsFilterDual (emptyFamily X) := by
  intro h
  exact h.1.2.1 (by simp [familyDual, emptyFamily])

end Chapter00.Section06Counterexample
