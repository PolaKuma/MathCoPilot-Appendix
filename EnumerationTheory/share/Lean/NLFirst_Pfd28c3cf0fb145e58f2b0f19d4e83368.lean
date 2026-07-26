import Chapter04.Common
import share.Lean.NLFirst_Pfd28c3cf0fb145e58f2b0f19d4e83368_Chapter02

noncomputable section

open Classical Filter

namespace MathCopilotPrior

universe u

/--
Exact external mathematical inputs used by Chapter 4, Sections 3--6.

The source-alignment record for every field is
`.mathcopilot/prior_research/MathCopilotPrior.chapter04_results.md`.
The record keeps one explicit and auditable trust boundary for the
research-scale theorems that the textbook itself treats as foundational.
-/
structure Chapter04Results where
  kalikow :
    ∃ M : Chapter04.System.{0},
      Chapter04.IsKolmogorovSystem M ∧ ¬ Chapter04.IsBernoulliSystem M
  kolmogorov_has_countable_lebesgue_spectrum :
    ∀ M : Chapter04.System.{u},
      Chapter04.IsKolmogorovSystem M →
        Chapter04.HasCountableLebesgueSpectrum M
  kolmogorov_iff_uniform_mixing :
    ∀ M : Chapter04.System.{u},
      Chapter04.IsKolmogorovAmbientSystem M →
        (Chapter04.IsKolmogorovSystem M ↔ Chapter02.IsUniformMixing M)
  halmos_von_neumann :
    ∀ M N : Chapter04.System.{u},
      Chapter02.IsErgodic M → Chapter02.IsErgodic N →
      Chapter04.HasDiscreteSpectrum M → Chapter04.HasDiscreteSpectrum N →
        (Chapter04.IsSpectrallyIsomorphic M N ↔
          Chapter04.eigenvalueSet M = Chapter04.eigenvalueSet N) ∧
        (Chapter04.eigenvalueSet M = Chapter04.eigenvalueSet N ↔
          Chapter04.IsSystemConjugate M N) ∧
        (Chapter04.IsSpectrallyIsomorphic M N ↔
          Chapter04.IsSystemConjugate M N)
  discrete_spectrum_conjugate_to_inverse :
    ∀ M : Chapter04.System.{u},
      Chapter04.HasDiscreteSpectrum M →
        Chapter04.IsConjugateToInverseSystem M
  compact_rotation_eigenvalues :
    ∀ (M : Chapter04.System.{u}) (G : Type u)
      [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
      (η : MeasureTheory.Measure G) (e : M.X → G) (inv : G → M.X) (a : G),
      Chapter04.IsCompactAbelianRotationModel M G η e inv a →
      Chapter02.IsErgodic M →
        (∀ lam : ℂ, ∀ f : M.X → ℂ, Chapter02.Eigenfunction M lam f →
          Chapter04.RotationCharacterEigenfunctionForModel e a lam f) ∧
        (∀ lam : ℂ, Chapter02.Eigenvalue M lam ↔
          Chapter04.RotationCharacterEigenvalueForModel a lam) ∧
        Chapter04.HasDiscreteSpectrum M
  discrete_spectrum_iff_compact_rotation :
    ∀ M : Chapter04.System.{u},
      Chapter02.IsErgodic M →
        (Chapter04.HasDiscreteSpectrum M ↔ ∃ N : Chapter04.System.{u},
          Chapter04.IsCompactAbelianRotationSystem N ∧
          Chapter02.IsErgodic N ∧ Chapter04.IsSystemConjugate M N) ∧
        (Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace →
          Chapter04.HasDiscreteSpectrum M →
            ∃ N : Chapter04.System.{u},
              Chapter04.IsMetrizableCompactAbelianRotationSystem N ∧
              Chapter02.IsErgodic N ∧ Chapter04.IsSystemConjugate M N)
  circle_subgroup_realization :
    ∀ H : Set ℂ, Chapter04.IsCircleSubgroup H →
      ∃ M : Chapter04.System.{u},
        Chapter02.IsErgodic M ∧ Chapter04.HasDiscreteSpectrum M ∧
          Chapter04.eigenvalueSet M = H
  local_inversion :
    Chapter04.LocalInversionForCountableFibers.{u}
  rohlin_skew_product :
    Chapter04.RohlinSkewProductTheoremStatement.{u}
  ergodic_decomposition :
    ∀ M : Chapter04.System.{u},
      Chapter01.IsMeasurePreservingSystem M →
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace →
        ∃ D : Chapter04.ErgodicDecompositionData M,
          Chapter04.IsErgodicDecomposition M D
  factor_ergodic_decomposition :
    ∀ M : Chapter04.System.{u},
      Chapter01.IsMeasurePreservingSystem M →
      Chapter04.IsLebesgueProbabilitySpace M.toProbabilitySpace →
        Chapter04.HasFactorErgodicDecomposition M

/--
Documented literature input.  This is the sole new trust boundary for
Chapter 4; all chapter-level declarations are checked consequences of its
exact fields.
-/
axiom chapter04_results : Chapter04Results.{u}

end MathCopilotPrior
