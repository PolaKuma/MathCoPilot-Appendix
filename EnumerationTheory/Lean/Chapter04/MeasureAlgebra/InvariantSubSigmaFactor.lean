import Chapter04.Descriptive.Invertibility
import Mathlib.MeasureTheory.Measure.Trim

noncomputable section

open Classical Filter

namespace Chapter04.InvariantSubSigmaFactor

universe u

/-- The measurable space whose measurable sets are a specified sigma algebra
family. -/
def familyMeasurableSpace {X : Type u} (F : SetFamily X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) : MeasurableSpace X where
  MeasurableSet' := F
  measurableSet_empty := by
    simpa using hF.2.1 Set.univ hF.1
  measurableSet_compl := hF.2.1
  measurableSet_iUnion := hF.2.2

@[simp] theorem measurableSet_familyMeasurableSpace_iff
    {X : Type u} (F : SetFamily X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (A : Set X) :
    @MeasurableSet X (familyMeasurableSpace F hF) A ↔ A ∈ F :=
  Iff.rfl

/-- Regard an invariant sub-sigma-algebra as a system on the same point set.
The ambient measure is trimmed to the smaller measurable space. -/
def system
    (M : System.{u}) (F : SetFamily M.X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧) :
    System.{u} where
  X := M.X
  measurableSpace := familyMeasurableSpace F hF
  μ := M.μ.trim (by
    intro A hA
    exact hsub hA)
  T := M.T

theorem system_measurePreserving
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    Chapter01.IsMeasurePreservingSystem (system M F hF hsub) := by
  let hle :
      familyMeasurableSpace F hF ≤ M.measurableSpace := by
    intro A hA
    exact hsub hA
  constructor
  · apply MeasureTheory.IsProbabilityMeasure.mk
    change (M.μ.trim hle) Set.univ = 1
    rw [MeasureTheory.trim_measurableSet_eq hle MeasurableSet.univ]
    exact hM.1.measure_univ
  · refine ⟨?_, ?_⟩
    · intro A hA
      exact hInv A hA
    · apply MeasureTheory.Measure.ext
      intro A hA
      rw [MeasureTheory.Measure.map_apply]
      · change (M.μ.trim hle) (M.T ⁻¹' A) = (M.μ.trim hle) A
        rw [MeasureTheory.trim_measurableSet_eq hle hA,
          MeasureTheory.trim_measurableSet_eq hle (hInv A hA)]
        exact hM.2.measure_preimage (hsub hA).nullMeasurableSet
      · intro B hB
        exact hInv B hB
      · exact hA

/-- The identity map from the ambient system to its invariant sub-sigma
system is a factor map. -/
theorem id_isFactorMap
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    Chapter01.IsFactorMap M (system M F hF hsub) id := by
  let hle :
      familyMeasurableSpace F hF ≤ M.measurableSpace := by
    intro A hA
    exact hsub hA
  have hN := system_measurePreserving M F hM hF hsub hInv
  refine ⟨hM, hN, Set.univ, Set.univ,
    hM.1.measure_univ, hN.1.measure_univ, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact Set.mem_univ _
  · intro x _
    exact Set.mem_univ _
  · refine ⟨MeasurableSet.univ, hF.1,
      hM.1.measure_univ, hN.1.measure_univ, ?_, ?_⟩
    · intro x _
      exact Set.mem_univ _
    · intro B hB
      constructor
      · simpa using hsub hB
      · simp only [Set.univ_inter, Set.inter_univ, Set.preimage_id]
        change M.μ B = (M.μ.trim hle) B
        exact (MeasureTheory.trim_measurableSet_eq hle hB).symm
  · intro x _
    rfl

/-- The sigma algebra pulled back along the canonical factor map is exactly
the prescribed family, without passing to equivalence modulo null sets. -/
theorem pulledBackSigma_eq
    (M : System.{u}) (F : SetFamily M.X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧) :
    F =
      {A : Set M.X |
        ∃ B : Set (system M F hF hsub).X,
          B ∈ (system M F hF hsub).𝓧 ∧ A = id ⁻¹' B} := by
  ext A
  constructor
  · intro hA
    exact ⟨A, hA, by simp⟩
  · rintro ⟨B, hB, rfl⟩
    simpa using hB

/-- Exact surjectivity of inverse image on the sub-sigma-algebra implies the
mod-null surjectivity condition for the induced system. -/
theorem inducedSigmaAlgebraSurjective_of_strict
    (M : System.{u}) (F : SetFamily M.X)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F)
    (hStrict :
      {A : Set M.X | ∃ B ∈ F, A = M.T ⁻¹' B} = F) :
    IsInducedSigmaAlgebraSurjective (system M F hF hsub) := by
  constructor
  · intro A hA
    exact hInv A hA
  · intro A hA
    have hArange :
        A ∈ {C : Set M.X | ∃ B ∈ F, C = M.T ⁻¹' B} := by
      rw [hStrict]
      exact hA
    rcases hArange with ⟨B, hB, hAB⟩
    refine ⟨B, hB, ?_⟩
    change
      (system M F hF hsub).μ
        (Chapter00.symmDiff (M.T ⁻¹' B) A) = 0
    rw [← hAB]
    simp [Chapter00.symmDiff]

/-- Once the canonical factor is known to be a Lebesgue space, strict
invariance supplies its measurable inverse modulo null sets. -/
theorem invertibleModNull_of_strict
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F)
    (hLeb :
      IsLebesgueProbabilitySpace
        (system M F hF hsub).toProbabilitySpace)
    (hStrict :
      {A : Set M.X | ∃ B ∈ F, A = M.T ⁻¹' B} = F) :
    IsInvertibleModNull (system M F hF hsub) := by
  exact Invertibility.invertibleModNull_of_inducedSigmaAlgebraSurjective
    (system M F hF hsub)
    (system_measurePreserving M F hM hF hsub hInv) hLeb
    (inducedSigmaAlgebraSurjective_of_strict M F hF hsub hInv hStrict)

end Chapter04.InvariantSubSigmaFactor
