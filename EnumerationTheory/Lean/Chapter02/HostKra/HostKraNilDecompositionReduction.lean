import Chapter02.HostKra.HostKraStructuredRecurrence
import Chapter02.Recurrence.MultipleKhintchineAssembly

open Classical MeasureTheory Set

noncomputable section

namespace Chapter02.HostKraNilDecompositionReduction

universe u

/-- The exact remaining structured theorem in the form used in
Bergelson--Host--Kra.

At every positive scale, the canonical fifteen-dual correlation is the sum,
in BHK uniform density, of a pro-minimal sequence and a null sequence; the
pro-minimal component also attains a value within that scale of the sharp
`μ(A)^4` bound.  The first two fields are the nilsequence decomposition
(Theorem 1.9 in the paper), while the last field is the sharp nilsystem
supremum estimate used in Theorem 8.1. -/
def FifteenDualSharpNilDecomposition : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    ∀ (hM : Chapter01.IsMeasurePreservingSystem M),
    IsErgodic M →
    ∀ (A : Set M.X) (hA : MeasurableSet A),
    ∀ δ : ℝ, 0 < δ →
      ∃ c : ℕ → ℝ,
        HostKraStructuredRecurrence.IsUniformLimitOfMinimalOrbitSequences c ∧
        MultipleKhintchineSyndetic.TendsToZeroInUniformDensity
          (fun n ↦
            HostKraFourfoldStructuredReduction.fifteenDualStructuredCorrelation
                M hM A hA n - c n) ∧
        ∃ n : ℕ, (realMeasure M A) ^ 4 - δ < c n

/-- The sharp nil-decomposition statement implies the fourfold BHK theorem
on standard-Borel ergodic systems. -/
theorem standardBorelQuadrupleKhintchine
    (hstructure : FifteenDualSharpNilDecomposition.{u}) :
    MultipleKhintchineAssembly.StandardBorelQuadrupleKhintchine.{u} := by
  intro M instSB hErg A hA hApos ε hε
  exact
    HostKraStructuredRecurrence.quadruple_syndetic_of_structured_nilDecomposition
      M hErg.1 hErg A hA
      (hstructure M hErg.1 hErg A hA)
      ε hε

/-- End-to-end reduction of the exact original axiom, including the complete
triple proof and removal of the standard-Borel hypothesis, to the sharp
fifteen-dual nil-decomposition theorem. -/
theorem multipleKhintchineStatement_firstClause
    (hstructure : FifteenDualSharpNilDecomposition.{u})
    (M : System.{u}) :
    IsErgodic M →
      ∀ A : Set M.X, MeasurableSet A → 0 < M.μ A →
      ∀ ε : ℝ, 0 < ε →
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A) >
            (realMeasure M A) ^ 3 - ε} ∧
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
                preimageIter M (3 * n) A) >
            (realMeasure M A) ^ 4 - ε} :=
  MultipleKhintchineAssembly.multipleKhintchineStatement_firstClause
    (standardBorelQuadrupleKhintchine hstructure) M

end Chapter02.HostKraNilDecompositionReduction
