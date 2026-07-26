import Chapter02.Recurrence.BHKOrbitCoding
import Chapter02.Recurrence.MultipleKhintchineBohrTriple

open Classical Set

noncomputable section

namespace Chapter02.MultipleKhintchineAssembly

universe u

open BHKOrbitCoding

/-- The sole remaining theorem after the checked triple proof and the
checked binary orbit-name reduction: the fourfold BHK conclusion on
standard-Borel systems. -/
def StandardBorelQuadrupleKhintchine : Prop :=
  ∀ (M : System.{u}) [StandardBorelSpace M.X],
    IsErgodic M →
      ∀ A : Set M.X, MeasurableSet A → 0 < M.μ A →
      ∀ ε : ℝ, 0 < ε →
        IsSyndetic {n : ℕ |
          MultipleKhintchineSyndetic.quadrupleCorrelation M A n >
            (realMeasure M A) ^ 4 - ε}

/-- A proof of the fourfold theorem on standard-Borel systems suffices for
the exact original theorem on arbitrary systems.  The forward binary
orbit-name factor is standard Borel, remains ergodic, and preserves the
measure of the base cylinder and every relevant progression intersection
exactly. -/
theorem multipleKhintchine_of_standardBorel_quadruple
    (hfour : StandardBorelQuadrupleKhintchine.{u})
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (hApos : 0 < M.μ A)
    (ε : ℝ) (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      realMeasure M
          (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A) >
        (realMeasure M A) ^ 3 - ε} ∧
    IsSyndetic {n : ℕ |
      realMeasure M
          (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
            preimageIter M (3 * n) A) >
        (realMeasure M A) ^ 4 - ε} := by
  let N := orbitCodeSystem M A
  letI : StandardBorelSpace N.X := by
    dsimp [N, orbitCodeSystem, OrbitCodeTarget]
    infer_instance
  have hNerg : IsErgodic N :=
    orbitCodeSystem_ergodic M hM A hA
  have hCmeas : MeasurableSet (codedSet : Set N.X) := by
    exact codedSet_measurable
  have hCpos : 0 < N.μ codedSet := by
    rw [codedSet_measure M hM.1 A hA]
    exact hApos
  have hthree :
      IsSyndetic {n : ℕ |
        realMeasure N
            (codedSet ∩ preimageIter N n codedSet ∩
              preimageIter N (2 * n) codedSet) >
          (realMeasure N codedSet) ^ 3 - ε} := by
    simpa [N, MultipleKhintchineSyndetic.tripleCorrelation] using
      MultipleKhintchineBohrTriple.triple_syndetic
        N hNerg codedSet hCmeas hCpos ε hε
  have hfour' :
      IsSyndetic {n : ℕ |
        realMeasure N
            (codedSet ∩ preimageIter N n codedSet ∩
              preimageIter N (2 * n) codedSet ∩
              preimageIter N (3 * n) codedSet) >
          (realMeasure N codedSet) ^ 4 - ε} := by
    simpa [N, MultipleKhintchineSyndetic.quadrupleCorrelation] using
      hfour N hNerg codedSet hCmeas hCpos ε hε
  exact multipleKhintchine_transfer M hM A hA ε ⟨hthree, hfour'⟩

/-- Curried form matching the first conjunct of
`Chapter02.MultipleKhintchineStatement`. -/
theorem multipleKhintchineStatement_firstClause
    (hfour : StandardBorelQuadrupleKhintchine.{u})
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
            (realMeasure M A) ^ 4 - ε} := by
  intro hM A hA hApos ε hε
  exact
    multipleKhintchine_of_standardBorel_quadruple
      hfour M hM A hA hApos ε hε

end Chapter02.MultipleKhintchineAssembly
