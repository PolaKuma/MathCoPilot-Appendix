import Chapter04.Common

noncomputable section

open Classical Filter

namespace Chapter04.ErgodicDecomposition

universe u

private abbrev One : Type u := ULift.{u} Unit

private def star : One.{u} := ULift.up ()

/-- The one-component decomposition of a system that is already ergodic. -/
def trivial (M : System.{u}) : ErgodicDecompositionData M where
  Y := One.{u}
  measurableSpace := ⊤
  ν := MeasureTheory.Measure.dirac star
  component := fun _ => M.μ

/-- An ergodic probability-preserving system is its own unique component. -/
theorem trivial_isErgodicDecomposition (M : System.{u})
    (hM : Chapter02.IsErgodic M) :
    IsErgodicDecomposition M (trivial M) := by
  refine ⟨hM.1, ?_, ?_, ?_, ?_⟩
  · change MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac star)
    infer_instance
  · exact Filter.Eventually.of_forall fun _ =>
      ⟨hM.1.1, hM.1.2, hM.2⟩
  · intro A hA
    change Measurable (fun _ : One.{u} => M.μ A)
    exact measurable_const
  · intro A hA
    change M.μ A = ∫⁻ _ : One.{u}, M.μ A ∂MeasureTheory.Measure.dirac star
    rw [MeasureTheory.lintegral_dirac]

theorem exists_of_ergodic (M : System.{u})
    (hM : Chapter02.IsErgodic M) :
    ∃ D : ErgodicDecompositionData M, IsErgodicDecomposition M D :=
  ⟨trivial M, trivial_isErgodicDecomposition M hM⟩

/-- The one-point factor used by the factor form of an ergodic decomposition. -/
def pointSystem : System.{u} where
  X := One.{u}
  measurableSpace := ⊤
  μ := MeasureTheory.Measure.dirac star
  T := id

theorem pointSystem_measurePreserving :
    Chapter01.IsMeasurePreservingSystem pointSystem.{u} := by
  constructor
  · change MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.dirac star)
    infer_instance
  · change MeasureTheory.MeasurePreserving id
      (MeasureTheory.Measure.dirac star) (MeasureTheory.Measure.dirac star)
    exact MeasureTheory.MeasurePreserving.id _

theorem const_point_isFactorMap (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Chapter01.IsFactorMap M pointSystem.{u} (fun _ => star.{u}) := by
  refine ⟨hM, pointSystem_measurePreserving, Set.univ, Set.univ,
    hM.1.measure_univ, pointSystem_measurePreserving.1.measure_univ,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Set.mem_univ _
  · intro y hy
    exact Set.mem_univ _
  · refine ⟨?_, ?_, hM.1.measure_univ,
      pointSystem_measurePreserving.1.measure_univ, ?_, ?_⟩
    · exact MeasurableSet.univ
    · change MeasurableSet (Set.univ : Set One.{u})
      exact MeasurableSet.univ
    · intro x hx
      exact Set.mem_univ _
    · intro B hB
      change MeasurableSet B at hB
      constructor
      · change MeasurableSet
          (Set.univ ∩ (fun _ : M.X => star.{u}) ⁻¹' (B ∩ Set.univ))
        simpa only [Set.inter_univ, Set.univ_inter] using
          ((measurable_const : Measurable (fun _ : M.X => star.{u})) hB)
      · have hBcases : B = ∅ ∨ B = Set.univ := by
          by_cases hunit : star.{u} ∈ B
          · right
            ext y
            change One.{u} at y
            have hy : y = star.{u} := Subsingleton.elim _ _
            subst y
            simp only [Set.mem_univ, iff_true]
            exact hunit
          · left
            ext y
            change One.{u} at y
            have hy : y = star.{u} := Subsingleton.elim _ _
            subst y
            constructor
            · exact fun h => hunit h
            · exact fun h => False.elim h
        rcases hBcases with rfl | rfl
        · simp [pointSystem]
        · simpa [pointSystem] using hM.1.measure_univ
  · intro x hx
    rfl

theorem hasFactor_of_ergodic (M : System.{u})
    (hM : Chapter02.IsErgodic M) :
    HasFactorErgodicDecomposition M := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  refine ⟨pointSystem.{u}, (fun _ => star.{u}), const_point_isFactorMap M hM.1,
    rfl, ?_, trivial M, trivial_isErgodicDecomposition M hM, id, ?_, ?_, ?_⟩
  · constructor
    · rintro A ⟨B, hB, rfl⟩
      by_cases hs : star.{u} ∈ B
      · refine ⟨Set.univ, ⟨MeasurableSet.univ, by
            simp [Chapter00.symmDiff]⟩, ?_⟩
        have heq :
            (fun _ : M.X => star.{u}) ⁻¹' B = Set.univ := by
          ext x
          simp [hs]
        rw [heq]
        simp [Chapter00.symmDiff]
      · refine ⟨∅, ⟨MeasurableSet.empty, by
            simp [Chapter00.symmDiff]⟩, ?_⟩
        have heq :
            (fun _ : M.X => star.{u}) ⁻¹' B = ∅ := by
          ext x
          simp [hs]
        rw [heq]
        simp [Chapter00.symmDiff]
    · intro A hA
      rcases hM.2 A hA.1 hA.2 with hzero | hone
      · refine ⟨∅, ⟨∅, MeasurableSet.empty, by simp⟩, ?_⟩
        simpa [Chapter00.symmDiff] using hzero
      · refine ⟨Set.univ, ⟨Set.univ, MeasurableSet.univ, by simp⟩, ?_⟩
        have hAcompl : M.μ Aᶜ = 0 := by
          rw [MeasureTheory.measure_compl hA.1
            (MeasureTheory.measure_ne_top M.μ A), hone]
          simp
        have hdiff : Chapter00.symmDiff Set.univ A = Aᶜ := by
          ext x
          simp [Chapter00.symmDiff]
        rwa [hdiff]
  · exact Function.bijective_id
  · exact measurable_id
  · exact Filter.Eventually.of_forall fun y => by
      change One.{u} at y
      change M.μ ((fun _ : M.X => star.{u}) ⁻¹' {id y}) = 1
      have hy : y = star.{u} := Subsingleton.elim _ _
      subst y
      simpa using hM.1.1.measure_univ

end Chapter04.ErgodicDecomposition
