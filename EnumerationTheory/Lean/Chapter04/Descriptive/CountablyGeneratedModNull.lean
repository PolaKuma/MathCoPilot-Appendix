import Chapter04.MeasureAlgebra.InducedMeasureAlgebraSeparable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

noncomputable section

open Classical Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter04.CountablyGeneratedModNull

universe u

/-- A separable probability measure algebra is generated modulo null sets by
a countable measurable family.  The conclusion is deliberately modulo null
sets: exact countable generation of an arbitrary sub-sigma-algebra is false in
general. -/
theorem exists_countable_generator_modNull
    (P : ProbabilitySpace.{u}) (hP : Chapter01.IsProbabilitySpace P)
    (hsep : IsSeparableMeasureAlgebra (inducedMeasureAlgebra P)) :
    ∃ D : ℕ → Set P.X,
      (∀ n, MeasurableSet (D n)) ∧
      ∀ A : Set P.X, MeasurableSet A →
        ∃ B : Set P.X,
          B ∈ Chapter00.generatedSigmaAlgebra (Set.range D) ∧
          P.μ (Chapter00.symmDiff A B) = 0 := by
  letI : IsProbabilityMeasure P.μ := hP
  obtain ⟨d, hd⟩ := hsep
  let D : ℕ → Set P.X := fun n => (d n).1
  have hD (n : ℕ) : MeasurableSet (D n) := (d n).2
  refine ⟨D, hD, ?_⟩
  intro A hA
  let ε : ℕ → ℝ := fun n => ((2 : ℝ)⁻¹) ^ (n + 1)
  have hε (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  choose k hk using fun n => hd ⟨A, hA⟩ (ε n) (hε n)
  let C : ℕ → Set P.X := fun n => D (k n)
  have hC (n : ℕ) : MeasurableSet (C n) := hD (k n)
  let E : ℕ → Set P.X := fun n => Chapter00.symmDiff A (C n)
  have hEbound (n : ℕ) :
      P.μ (E n) < (2 : ENNReal)⁻¹ ^ (n + 1) := by
    apply (ENNReal.toReal_lt_toReal
      (measure_ne_top P.μ (E n)) (by simp)).mp
    have hkn := hk n
    change
      (P.μ
        ((A ∩ (D (k n))ᶜ) ∪ (D (k n) ∩ Aᶜ))).toReal < ε n at hkn
    simpa [E, C, D, ε, Chapter00.symmDiff, ENNReal.toReal_pow,
      ENNReal.toReal_inv] using hkn
  have hsum : ∑' n, P.μ (E n) ≠ ∞ := by
    have hle :
        (∑' n, P.μ (E n)) ≤
          ∑' n : ℕ, (2 : ENNReal)⁻¹ ^ (n + 1) :=
      ENNReal.tsum_le_tsum fun n => (hEbound n).le
    have hgeom :
        (∑' n : ℕ, (2 : ENNReal)⁻¹ ^ (n + 1)) ≠ ∞ := by
      rw [show (∑' n : ℕ, (2 : ENNReal)⁻¹ ^ (n + 1)) =
        (2 : ENNReal)⁻¹ * ∑' n : ℕ, (2 : ENNReal)⁻¹ ^ n by
        simp_rw [pow_succ']
        exact ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_geometric]
      norm_num
    exact ne_top_of_le_ne_top hgeom hle
  let B : Set P.X := liminf C atTop
  have hBgen :
      B ∈ Chapter00.generatedSigmaAlgebra (Set.range D) := by
    change @MeasurableSet P.X
      (MeasurableSpace.generateFrom (Set.range D)) B
    dsimp [B]
    rw [liminf_eq_iSup_iInf_of_nat]
    exact MeasurableSet.iUnion fun N =>
      MeasurableSet.iInter fun n =>
        MeasurableSet.iInter fun (_ : n ≥ N) =>
          MeasurableSpace.measurableSet_generateFrom ⟨k n, rfl⟩
  have hlimsup0 : P.μ (limsup E atTop) = 0 :=
    measure_limsup_atTop_eq_zero hsum
  have hsubset :
      Chapter00.symmDiff A B ⊆ limsup E atTop := by
    intro x hx
    by_contra hxlim
    rw [limsup_eq_iInf_iSup_of_nat] at hxlim
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter,
      Set.mem_iUnion, not_forall, not_exists] at hxlim
    obtain ⟨N, hN⟩ := hxlim
    have heventual : ∀ n, N ≤ n → (x ∈ C n ↔ x ∈ A) := by
      intro n hn
      have hnotE : x ∉ E n := hN n hn
      simp only [E, Chapter00.symmDiff, Set.mem_union, Set.mem_diff,
        not_or, not_and] at hnotE
      tauto
    have hxBA : x ∈ B ↔ x ∈ A := by
      dsimp [B]
      rw [liminf_eq_iSup_iInf_of_nat]
      simp only [Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.mem_iUnion,
        Set.mem_iInter]
      constructor
      · rintro ⟨N', hN'⟩
        exact (heventual (max N N') (le_max_left _ _)).mp
          (hN' (max N N') (le_max_right _ _))
      · intro hxA
        exact ⟨N, fun n hn => (heventual n hn).mpr hxA⟩
    simp only [Chapter00.symmDiff, Set.mem_union, Set.mem_diff] at hx
    exact hx.elim
      (fun h => h.2 (hxBA.mpr h.1))
      (fun h => h.2 (hxBA.mp h.1))
  refine ⟨B, hBgen, ?_⟩
  exact measure_mono_null hsubset hlimsup0

/-- Every invariant sub-sigma-algebra of a Lebesgue probability system is
countably generated modulo null sets.  This is the form needed for the spatial
factor construction: an arbitrary sub-sigma-algebra need not be exactly
countably generated. -/
theorem invariantSubSigma_exists_countable_generator_modNull
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧)
    (hInv : ∀ A : Set M.X, A ∈ F → M.T ⁻¹' A ∈ F) :
    ∃ D : ℕ → Set M.X,
      (∀ n, D n ∈ F) ∧
      ∀ A : Set M.X, A ∈ F →
        ∃ B : Set M.X,
          B ∈ Chapter00.generatedSigmaAlgebra (Set.range D) ∧
          M.μ (Chapter00.symmDiff A B) = 0 := by
  let P :=
    (InvariantSubSigmaFactor.system M F hF hsub).toProbabilitySpace
  have hP :
      Chapter01.IsProbabilitySpace P :=
    (InvariantSubSigmaFactor.system_measurePreserving
      M F hM hF hsub hInv).1
  have hsep :
      IsSeparableMeasureAlgebra (inducedMeasureAlgebra P) :=
    Chapter04.InducedMeasureAlgebraSeparable.invariantSubSigma_inducedMeasureAlgebra_separable
      M F hM hLeb hF hsub
  obtain ⟨D, hD, happrox⟩ :=
    exists_countable_generator_modNull P hP hsep
  refine ⟨D, fun n => hD n, ?_⟩
  intro A hA
  obtain ⟨B, hBgen, hzero⟩ := happrox A hA
  refine ⟨B, hBgen, ?_⟩
  let hle :
      InvariantSubSigmaFactor.familyMeasurableSpace F hF ≤
        M.measurableSpace := by
    intro C hC
    exact hsub hC
  have hgenle :
      MeasurableSpace.generateFrom (Set.range D) ≤
        InvariantSubSigmaFactor.familyMeasurableSpace F hF := by
    apply MeasurableSpace.generateFrom_le
    rintro C ⟨n, rfl⟩
    exact hD n
  have hBF : B ∈ F := hgenle B hBgen
  have hsymmF : Chapter00.symmDiff A B ∈ F := by
    have hAms :
        @MeasurableSet M.X
          (InvariantSubSigmaFactor.familyMeasurableSpace F hF) A := hA
    have hBms :
        @MeasurableSet M.X
          (InvariantSubSigmaFactor.familyMeasurableSpace F hF) B := hBF
    rw [Chapter00.symmDiff]
    exact (hAms.inter hBms.compl).union (hBms.inter hAms.compl)
  change
    (M.μ.trim hle) (Chapter00.symmDiff A B) = 0 at hzero
  rwa [MeasureTheory.trim_measurableSet_eq hle hsymmF] at hzero

end Chapter04.CountablyGeneratedModNull
