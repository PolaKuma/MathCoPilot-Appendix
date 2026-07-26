import Chapter04.Descriptive.StandardBorel

noncomputable section

open Classical

namespace Chapter04.StandardBorel

universe u

/-- Mathlib's Baire-space definition of an analytic set also yields the
chapter's image-of-a-Borel-set presentation.  Together with
`analyticSet_of_data`, this closes the representation gap between the two
APIs. -/
theorem data_of_analyticSet
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    (A : Set M.X)
    (hA :
      @MeasureTheory.AnalyticSet M.X
        (upgradeStandardBorel M.X
          (h := instanceOfData M hM)).toTopologicalSpace A) :
    IsAnalyticSet M A := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  rw [MeasureTheory.AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, hfrange⟩
  · let Y : MeasurableSpaceData.{u} :=
      { X := ULift.{u} Empty
        measurableSpace := inferInstance }
    have sY : @StandardBorelSpace Y.X Y.measurableSpace := by
      infer_instance
    have hY : IsStandardBorelSpaceData Y := by
      refine ⟨Y.X, Y.measurableSpace, sY, id, id,
        fun _ => rfl, fun _ => rfl, ?_, ?_⟩
      · exact fun _ h => h
      · exact fun _ h => h
    let g : Y.X → M.X := fun y => isEmptyElim y.down
    have hg : IsMeasurableMap Y M g := by
      intro B hB
      have hempty : g ⁻¹' B = (∅ : Set Y.X) := by
        ext y
        exact isEmptyElim y.down
      rw [hempty]
      change @MeasurableSet Y.X Y.measurableSpace ∅
      exact MeasurableSet.empty
    have hemptyY : (∅ : Set Y.X) ∈ Y.sets := by
      change @MeasurableSet Y.X Y.measurableSpace ∅
      exact MeasurableSet.empty
    refine ⟨Y, hY, ∅, hemptyY, g, hg, ?_⟩
    simp only [Set.image_empty]
  · let Y : MeasurableSpaceData.{u} :=
      { X := (ℕ → ℕ) × ULift.{u} Unit
        measurableSpace := inferInstance }
    have sY : @StandardBorelSpace Y.X Y.measurableSpace := by
      infer_instance
    have hY : IsStandardBorelSpaceData Y := by
      refine ⟨Y.X, Y.measurableSpace, sY, id, id,
        fun _ => rfl, fun _ => rfl, ?_, ?_⟩
      · exact fun _ h => h
      · exact fun _ h => h
    let g : Y.X → M.X := fun y => f y.1
    have hgcont : Continuous g :=
      hf.comp continuous_fst
    have hg : IsMeasurableMap Y M g := by
      exact hgcont.measurable
    have hgrange : Set.range g = Set.range f := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.1, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨(y, ULift.up ()), rfl⟩
    have hunivY : (Set.univ : Set Y.X) ∈ Y.sets := by
      change @MeasurableSet Y.X Y.measurableSpace Set.univ
      exact MeasurableSet.univ
    refine ⟨Y, hY, Set.univ, hunivY, g, hg, ?_⟩
    rw [Set.image_univ, hgrange, hfrange]

/-- On a standard Borel target, the chapter's analytic-set predicate is
equivalent to Mathlib's universe-safe Baire-space predicate. -/
theorem analyticSet_iff_data
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    (A : Set M.X) :
    IsAnalyticSet M A ↔
      @MeasureTheory.AnalyticSet M.X
        (upgradeStandardBorel M.X
          (h := instanceOfData M hM)).toTopologicalSpace A :=
  ⟨analyticSet_of_data M hM A, data_of_analyticSet M hM A⟩

/-- Borel sets are analytic in the chapter's data presentation. -/
theorem analyticSet_of_measurableSet
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    {A : Set M.X} (hA : A ∈ M.sets) :
    IsAnalyticSet M A := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  apply data_of_analyticSet M hM A
  exact hA.analyticSet

/-- Analytic sets are closed under countable unions. -/
theorem analyticSet_iUnion
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    (A : ℕ → Set M.X) (hA : ∀ n, IsAnalyticSet M (A n)) :
    IsAnalyticSet M (⋃ n, A n) := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  apply data_of_analyticSet M hM
  exact MeasureTheory.AnalyticSet.iUnion
    (fun n => analyticSet_of_data M hM (A n) (hA n))

/-- Analytic sets are closed under countable intersections. -/
theorem analyticSet_iInter
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    (A : ℕ → Set M.X) (hA : ∀ n, IsAnalyticSet M (A n)) :
    IsAnalyticSet M (⋂ n, A n) := by
  letI : StandardBorelSpace M.X := instanceOfData M hM
  letI : UpgradedStandardBorel M.X := upgradeStandardBorel M.X
  apply data_of_analyticSet M hM
  exact MeasureTheory.AnalyticSet.iInter
    (fun n => analyticSet_of_data M hM (A n) (hA n))

/-- Analytic sets are closed under binary intersections. -/
theorem analyticSet_inter
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    {A B : Set M.X} (hA : IsAnalyticSet M A)
    (hB : IsAnalyticSet M B) :
    IsAnalyticSet M (A ∩ B) := by
  let C : ℕ → Set M.X := fun n => if n = 0 then A else B
  have hC : IsAnalyticSet M (⋂ n, C n) :=
    analyticSet_iInter M hM C (fun n => by
      by_cases hn : n = 0
      · simpa [C, hn] using hA
      · simpa [C, hn] using hB)
  have heq : (⋂ n, C n) = A ∩ B := by
    ext x
    constructor
    · intro hx
      have hx0 := Set.mem_iInter.mp hx 0
      have hx1 := Set.mem_iInter.mp hx 1
      exact ⟨by simpa [C] using hx0, by simpa [C] using hx1⟩
    · rintro ⟨hxA, hxB⟩
      apply Set.mem_iInter.mpr
      intro n
      by_cases hn : n = 0
      · simpa [C, hn] using hxA
      · simpa [C, hn] using hxB
  rwa [heq] at hC

/-- Removing a Borel set from an analytic set preserves analyticity. -/
theorem analyticSet_diff_measurable
    (M : MeasurableSpaceData.{u}) (hM : IsStandardBorelSpaceData M)
    {A B : Set M.X} (hA : IsAnalyticSet M A) (hB : B ∈ M.sets) :
    IsAnalyticSet M (A \ B) := by
  rw [Set.diff_eq]
  exact analyticSet_inter M hM hA
    (analyticSet_of_measurableSet M hM hB.compl)

end Chapter04.StandardBorel
