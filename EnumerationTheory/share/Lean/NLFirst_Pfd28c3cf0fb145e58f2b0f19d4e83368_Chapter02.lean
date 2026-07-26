import Chapter02.Common
import Chapter02.Spectral.PontryaginSeparation
import Chapter02.Spectral.TorusDualMatrixBridge

noncomputable section

open Classical MeasureTheory

namespace MathCopilotPrior

universe u

variable {G : Type u} [CommGroup G] [MetricSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

noncomputable def compactAbelianCharacterLp
    (m : Measure G) [IsProbabilityMeasure m]
    (χ : Chapter02.ContinuousMultiplicativeCircleCharacter G) :
    Lp ℂ 2 m := by
  have hχ : MemLp χ.toFun 2 m := by
    apply (memLp_top_of_bound χ.continuous.aestronglyMeasurable 1 ?_).mono_exponent
      (by simp)
    exact .of_forall fun x => le_of_eq (χ.unit_norm x)
  exact hχ.toLp χ.toFun

/-- Peter--Weyl completeness for compact metrizable abelian groups, now
proved internally from Pontryagin point separation and Stone--Weierstrass. -/
theorem compactAbelian_character_span_dense
    (m : Measure G) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    Dense
      (Submodule.span ℂ
        (Set.range (compactAbelianCharacterLp (G := G) m)) :
          Set (Lp ℂ 2 m)) := by
  have hfun :
      compactAbelianCharacterLp (G := G) m =
        Chapter02.CompactAbelianPeterWeyl.characterLp m := by
    funext χ
    rfl
  rw [hfun]
  simpa [Chapter02.CompactAbelianPeterWeyl.lpCharacterSpan] using
    (Chapter02.PontryaginSeparation.character_span_dense m)

/-- **Documented literature input: the torus dual / matrix-spectrum bridge.**

Source: Michel Waldschmidt, “Algebraic Dynamics and Transcendental
Numbers”, §2, pp. 4--5,
https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/adtn.pdf.
See also the explicit Fourier proof in T. Feng, *Ergodic Theory* lecture
notes, Theorem 4.9, pp. 16--17,
https://math.berkeley.edu/~fengt/ergodic_theory.pdf.

For the torus `ℝⁿ/ℤⁿ`, its continuous circle-character group is `ℤⁿ`; the
dual action of the integer matrix is the transpose action on integer
frequencies.  The cited Fourier proof establishes exactly that a nonzero
frequency has a finite positive orbit precisely when the complexified matrix
has an eigenvalue that is a root of unity.  Under the character/frequency
identification, “nonzero frequency” is exactly “nontrivial character”.

The declaration records only this algebraic Pontryagin-dual bridge.  It does
not assume ergodicity, measure preservation, or surjectivity. -/
theorem torus_rootOfUnity_iff_periodic_nontrivial_character
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    Chapter02.HasRootOfUnityEigenvalue A ↔
      ∃ χ : Chapter02.ContinuousCircleCharacter (Chapter01.Torus n),
        (∃ q : ℕ, 0 < q ∧
          (fun x => χ.toFun
            ((Chapter02.torusMatrixMap n A)^[q] x)) = χ.toFun) ∧
        ∃ x, χ.toFun x ≠ 1 :=
  Chapter02.TorusDualMatrixBridge.torus_rootOfUnity_iff_periodic_nontrivial_character
    n A

end MathCopilotPrior
