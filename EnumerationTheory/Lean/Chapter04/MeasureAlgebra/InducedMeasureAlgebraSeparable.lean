import Chapter04.Descriptive.StandardBorel
import Chapter04.MeasureAlgebra.InducedMeasureAlgebra
import Chapter04.MeasureAlgebra.InvariantSubSigmaFactor
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section

open Classical MeasureTheory
open scoped symmDiff

namespace Chapter04.InducedMeasureAlgebraSeparable

universe u

/-- The measure algebra of a standard Borel probability space is separable.
This is the countable mod-null approximation input used when an arbitrary
sub-sigma-algebra is replaced by a standard Borel factor. -/
theorem inducedMeasureAlgebra_separable
    (P : ProbabilitySpace.{u})
    (hP : IsLebesgueProbabilitySpace P) :
    IsSeparableMeasureAlgebra (inducedMeasureAlgebra P) := by
  let PM : MeasurableSpaceData.{u} :=
    { X := P.X, measurableSpace := P.measurableSpace }
  letI : StandardBorelSpace P.X :=
    StandardBorel.instanceOfData PM hP.2
  letI : MeasureTheory.IsProbabilityMeasure P.μ := hP.1
  obtain ⟨𝒜, h𝒜count, h𝒜dense⟩ :=
    MeasureTheory.exists_countable_measureDense P.μ
  have h𝒜nonempty : 𝒜.Nonempty := h𝒜dense.nonempty
  obtain ⟨a, ha⟩ := h𝒜count.exists_surjective h𝒜nonempty
  let d : ℕ → (inducedMeasureAlgebra P).carrier :=
    fun n => ⟨(a n).1, h𝒜dense.measurable (a n).1 (a n).2⟩
  refine ⟨d, ?_⟩
  intro A ε hε
  obtain ⟨B, hB𝒜, hdist⟩ :=
    h𝒜dense.approx A.1 A.2 (MeasureTheory.measure_ne_top P.μ A.1)
      ε hε
  obtain ⟨n, hn⟩ := ha ⟨B, hB𝒜⟩
  have hdn : (d n).1 = B := congrArg Subtype.val hn
  refine ⟨n, ?_⟩
  change
    (P.μ
      (((A.1 ∩ (d n).1ᶜ) ∪ ((d n).1 ∩ A.1ᶜ)))).toReal < ε
  rw [hdn]
  apply ENNReal.toReal_lt_of_lt_ofReal
  simpa [Set.symmDiff_def, Chapter00.symmDiff, Set.union_comm] using hdist

set_option maxHeartbeats 800000 in
/-- Passing to an arbitrary smaller sigma-algebra preserves separability of
the measure algebra.  No countable-generation hypothesis on the smaller
sigma-algebra is needed: a countable family is obtained by choosing one point
from every nonempty intersection with the countable collection of rational
balls around an ambient dense family. -/
theorem invariantSubSigma_inducedMeasureAlgebra_separable
    (M : System.{u}) (F : SetFamily M.X)
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hLeb : IsLebesgueProbabilitySpace M.toProbabilitySpace)
    (hF : Chapter00.IsSigmaAlgebraFamily F) (hsub : F ⊆ M.𝓧) :
    IsSeparableMeasureAlgebra
      (inducedMeasureAlgebra
        (InvariantSubSigmaFactor.system M F hF hsub).toProbabilitySpace) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let P := M.toProbabilitySpace
  obtain ⟨a, ha⟩ := inducedMeasureAlgebra_separable P hLeb
  let r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let good (n k : ℕ) (B : Set M.X) : Prop :=
    B ∈ F ∧ M.μ.real (B ∆ (a n).1) < r k
  let c : ℕ → ℕ → Set M.X := fun n k =>
    if h : ∃ B, good n k B then Classical.choose h else ∅
  have hc_mem : ∀ n k, c n k ∈ F := by
    intro n k
    unfold c
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · simpa using hF.2.1 Set.univ hF.1
  have hc_close : ∀ n k, (∃ B, good n k B) →
      M.μ.real (c n k ∆ (a n).1) < r k := by
    intro n k h
    simp only [c, dif_pos h]
    exact (Classical.choose_spec h).2
  let d : ℕ →
      (inducedMeasureAlgebra
        (InvariantSubSigmaFactor.system M F hF hsub).toProbabilitySpace).carrier :=
    fun m => ⟨c (Nat.unpair m).1 (Nat.unpair m).2,
      (InvariantSubSigmaFactor.measurableSet_familyMeasurableSpace_iff F hF _).2
        (hc_mem (Nat.unpair m).1 (Nat.unpair m).2)⟩
  refine ⟨d, ?_⟩
  intro A ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by linarith)
  have hr_pos : 0 < r k := by
    dsimp [r]
    positivity
  have hAF : A.1 ∈ F := A.2
  have hAambient : @MeasurableSet M.X M.measurableSpace A.1 := hsub hAF
  obtain ⟨n, hn⟩ := ha ⟨A.1, hAambient⟩ (r k) hr_pos
  have hgood : ∃ B, good n k B := by
    refine ⟨A.1, A.2, ?_⟩
    simpa [good, symmDiff_comm] using hn
  refine ⟨Nat.pair n k, ?_⟩
  have htriangle :
      M.μ.real (A.1 ∆ c n k) <
        r k + r k := by
    calc
      M.μ.real (A.1 ∆ c n k)
          ≤ M.μ.real (A.1 ∆ (a n).1) +
              M.μ.real ((a n).1 ∆ c n k) :=
        MeasureTheory.measureReal_symmDiff_le
          (μ := M.μ) (s := A.1) (t := (a n).1) (c n k)
          (measure_ne_top M.μ A.1) (measure_ne_top M.μ (a n).1)
      _ < r k + r k := by
        apply add_lt_add
        · simpa [Set.symmDiff_def, Chapter00.symmDiff, Set.union_comm] using hn
        · simpa [symmDiff_comm] using hc_close n k hgood
  have hr_sum : r k + r k < ε := by
    dsimp [r] at hk ⊢
    linarith
  let hle :
      InvariantSubSigmaFactor.familyMeasurableSpace F hF ≤ M.measurableSpace := by
    intro B hB
    exact hsub hB
  change
    ((M.μ.trim hle)
      (((A.1 ∩ (d (Nat.pair n k)).1ᶜ) ∪
        ((d (Nat.pair n k)).1 ∩ A.1ᶜ)))).toReal < ε
  have hsymmF : A.1 ∆ c n k ∈ F := by
    have hAms :
        @MeasurableSet M.X
          (InvariantSubSigmaFactor.familyMeasurableSpace F hF) A.1 := A.2
    have hcms :
        @MeasurableSet M.X
          (InvariantSubSigmaFactor.familyMeasurableSpace F hF) (c n k) :=
      hc_mem n k
    change @MeasurableSet M.X
      (InvariantSubSigmaFactor.familyMeasurableSpace F hF) (A.1 ∆ c n k)
    rw [Set.symmDiff_def]
    exact (hAms.inter hcms.compl).union (hcms.inter hAms.compl)
  have htargetF :
      (A.1 ∩ (c n k)ᶜ) ∪ (c n k ∩ A.1ᶜ) ∈ F := by
    simpa [Set.symmDiff_def] using hsymmF
  simp only [d, Nat.unpair_pair]
  rw [MeasureTheory.trim_measurableSet_eq hle htargetF]
  simpa [Set.symmDiff_def, Set.union_comm] using
    lt_trans htriangle hr_sum

end Chapter04.InducedMeasureAlgebraSeparable
