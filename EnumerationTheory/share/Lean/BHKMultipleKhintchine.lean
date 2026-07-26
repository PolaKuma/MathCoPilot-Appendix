import Chapter02.Common

open Set

noncomputable section

namespace MathCopilotPrior

universe u

/-- **Documented literature input: the Bergelson--Host--Kra multiple
Khintchine theorem for progressions of lengths three and four.**

Source: Vitaly Bergelson, Bernard Host, and Bryna Kra, “Multiple recurrence
and nilsequences”, *Inventiones Mathematicae* 160 (2005), 261--303,
Theorem 1.2, pp. 263--264,
https://people.math.osu.edu/bergelson.1/BHK.pdf,
DOI 10.1007/s00222-004-0428-6.

The cited theorem says that in an ergodic probability-preserving system, for
every positive-measure measurable set `A` and every `ε > 0`, the return times
for the three-term and four-term intersections exceeding respectively
`μ(A)^3 - ε` and `μ(A)^4 - ε` are syndetic.  The two conjuncts below are
exactly those clauses in the chapter's `preimageIter` notation.  No mixing,
invertibility, or other extra dynamical hypothesis is added to the chapter
statement. -/
axiom bergelsonHostKra_multipleKhintchine
    (M : Chapter02.System.{u}) :
    Chapter02.IsErgodic M →
      ∀ A : Set M.X, MeasurableSet A → 0 < M.μ A →
      ∀ ε : ℝ, 0 < ε →
        Chapter02.IsSyndetic {n : ℕ |
          Chapter02.realMeasure M
              (A ∩ Chapter02.preimageIter M n A ∩
                Chapter02.preimageIter M (2 * n) A) >
            (Chapter02.realMeasure M A) ^ 3 - ε} ∧
        Chapter02.IsSyndetic {n : ℕ |
          Chapter02.realMeasure M
              (A ∩ Chapter02.preimageIter M n A ∩
                Chapter02.preimageIter M (2 * n) A ∩
                Chapter02.preimageIter M (3 * n) A) >
            (Chapter02.realMeasure M A) ^ 4 - ε}

end MathCopilotPrior
