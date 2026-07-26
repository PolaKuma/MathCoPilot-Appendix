import Chapter04.MeasureAlgebra.QuotientBoolean

noncomputable section

open Classical

namespace Chapter04.MeasureAlgebraSpatial

universe u v

theorem nullSet_sigmaIdeal (P : ProbabilitySpace.{u}) : IsSigmaIdeal (IsNullSet P) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · exact ⟨∅, MeasurableSet.empty, Set.Subset.rfl, MeasureTheory.measure_empty⟩
    · intro A B hAB
      rintro ⟨C, hC, hBC, hC0⟩
      exact ⟨C, hC, hAB.trans hBC, hC0⟩
    · intro A B
      rintro ⟨C, hC, hAC, hC0⟩ ⟨D, hD, hBD, hD0⟩
      exact ⟨C ∪ D, hC.union hD, fun x hx => hx.elim
        (fun hxA => Or.inl (hAC hxA)) (fun hxB => Or.inr (hBD hxB)), by simp [hC0, hD0]⟩
  · intro A hA
    choose B hB hAB hB0 using hA
    exact ⟨⋃ n, B n, MeasurableSet.iUnion hB,
      Set.iUnion_mono hAB, MeasureTheory.measure_iUnion_null hB0⟩

private noncomputable def quotientMap
    (P : ProbabilitySpace.{v}) (Q : ProbabilitySpace.{u})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q) (inducedMeasureAlgebra P))
    (A : Set Q.X) : Set P.X :=
  if hA : MeasurableSet A then (Φ.map ⟨A, hA⟩).1 else ∅

theorem quotient_iso_of_measureAlgebra_iso
    (P : ProbabilitySpace.{v}) (Q : ProbabilitySpace.{u})
    (Φ : MeasureAlgebraHomData (inducedMeasureAlgebra Q) (inducedMeasureAlgebra P))
    (hΦ : IsMeasureAlgebraIsomorphism Φ) :
    ∃ Ψ : QuotientBooleanHomData
        { X := P.X, measurableSpace := P.measurableSpace }
        { X := Q.X, measurableSpace := Q.measurableSpace }
        (IsNullSet P) (IsNullSet Q),
      IsQuotientBooleanIso Ψ ∧
      ∀ A : Set Q.X, ∀ hA : MeasurableSet A,
        Ψ.map A = (Φ.map ⟨A, hA⟩).1 := by
  let M : MeasurableSpaceData.{v} := { X := P.X, measurableSpace := P.measurableSpace }
  let N : MeasurableSpaceData.{u} := { X := Q.X, measurableSpace := Q.measurableSpace }
  let Ψ : QuotientBooleanHomData M N (IsNullSet P) (IsNullSet Q) :=
    { map := quotientMap P Q Φ }
  have hmap (A : Set Q.X) (hA : MeasurableSet A) :
      Ψ.map A = (Φ.map ⟨A, hA⟩).1 := by simp [Ψ, quotientMap, hA]
  refine ⟨Ψ, ⟨?_, ?_, ?_⟩, hmap⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro A hA
      rw [hmap A hA]
      exact (Φ.map ⟨A, hA⟩).2
    · intro A B hA hB hAB
      rcases hAB with ⟨C, hC, hsub, hC0⟩
      have hQ0 : Q.μ (Chapter00.symmDiff A B) = 0 :=
        MeasureTheory.measure_mono_null hsub hC0
      have hrel : (inducedMeasureAlgebra Q).equiv ⟨A, hA⟩ ⟨B, hB⟩ := hQ0
      have himg := hΦ.1.1 _ _ hrel
      rw [hmap A hA, hmap B hB]
      exact ⟨Chapter00.symmDiff (Φ.map ⟨A, hA⟩).1 (Φ.map ⟨B, hB⟩).1,
        (Φ.map ⟨A, hA⟩).2.diff (Φ.map ⟨B, hB⟩).2 |>.union
          ((Φ.map ⟨B, hB⟩).2.diff (Φ.map ⟨A, hA⟩).2), Set.Subset.rfl, himg⟩
    · intro A B hA hB
      have hu := hΦ.1.2.1 ⟨A, hA⟩ ⟨B, hB⟩
      rw [hmap (A ∪ B) (hA.union hB), hmap A hA, hmap B hB]
      exact ⟨_, (Φ.map ⟨A ∪ B, hA.union hB⟩).2.diff
          ((Φ.map ⟨A, hA⟩).2.union (Φ.map ⟨B, hB⟩).2) |>.union
          (((Φ.map ⟨A, hA⟩).2.union (Φ.map ⟨B, hB⟩).2).diff
            (Φ.map ⟨A ∪ B, hA.union hB⟩).2), Set.Subset.rfl, hu⟩
    · intro A hA
      have hc := hΦ.1.2.2.1 ⟨A, hA⟩
      rw [hmap Aᶜ hA.compl, hmap A hA]
      exact ⟨_, (Φ.map ⟨Aᶜ, hA.compl⟩).2.diff (Φ.map ⟨A, hA⟩).2.compl |>.union
        ((Φ.map ⟨A, hA⟩).2.compl.diff (Φ.map ⟨Aᶜ, hA.compl⟩).2),
        Set.Subset.rfl, hc⟩
    · intro A hA
      have hi := hΦ.1.2.2.2.1 (fun n => ⟨A n, hA n⟩)
      rw [hmap (⋃ n, A n) (MeasurableSet.iUnion hA)]
      simp_rw [hmap (A _) (hA _)]
      exact ⟨_, (Φ.map ⟨⋃ n, A n, MeasurableSet.iUnion hA⟩).2.diff
          (MeasurableSet.iUnion fun n => (Φ.map ⟨A n, hA n⟩).2) |>.union
          ((MeasurableSet.iUnion fun n => (Φ.map ⟨A n, hA n⟩).2).diff
            (Φ.map ⟨⋃ n, A n, MeasurableSet.iUnion hA⟩).2), Set.Subset.rfl, hi⟩
  · intro A B hA hB hAB
    rcases hAB with ⟨C, hC, hsub, hC0⟩
    rw [hmap A hA, hmap B hB] at hsub
    have hP0 : P.μ (Chapter00.symmDiff (Φ.map ⟨A, hA⟩).1 (Φ.map ⟨B, hB⟩).1) = 0 :=
      MeasureTheory.measure_mono_null hsub hC0
    have hrel := hΦ.2.1 ⟨A, hA⟩ ⟨B, hB⟩ hP0
    exact ⟨Chapter00.symmDiff A B, (hA.diff hB).union (hB.diff hA),
      Set.Subset.rfl, hrel⟩
  · intro C hC
    obtain ⟨A, hA⟩ := hΦ.2.2 ⟨C, hC⟩
    refine ⟨A.1, A.2, ?_⟩
    rw [hmap A.1 A.2]
    exact ⟨Chapter00.symmDiff (Φ.map A).1 C,
      (Φ.map A).2.diff hC |>.union (hC.diff (Φ.map A).2), Set.Subset.rfl, hA⟩

end Chapter04.MeasureAlgebraSpatial
