import Chapter02.Ergodic.CorrelationMean

noncomputable section

open Filter MeasureTheory

namespace Chapter02.ErgodicCorrelations

universe u

/-- Ergodicity is equivalent to Cesàro convergence of all measurable-set
correlations.  This low-dependency version prevents spectral and product
modules from importing the chapter-level `Section03` aggregator. -/
theorem ergodicIffCesaroCorrelations (M : System.{u}) :
    ErgodicIffCesaroCorrelations M := by
  intro hM
  letI : IsProbabilityMeasure M.μ := hM.1
  constructor
  · intro hErg A B hA hB
    exact CorrelationMean.ergodic_cesaroCorrelations M hM hErg A B hA hB
  · intro hcorr
    refine ⟨hM, ?_⟩
    intro A hA hnull
    have hself :=
      CorrelationMean.cesaroCorrelation_self_of_invariant M hM A hnull
    have hprod := hcorr A A hA hA
    have heq : realMeasure M A = productMeasureValue M A A :=
      tendsto_nhds_unique hself hprod
    have hidem : realMeasure M A * (realMeasure M A - 1) = 0 := by
      unfold productMeasureValue at heq
      nlinarith
    rcases mul_eq_zero.mp hidem with hzero | hone
    · left
      have hrealzero : realMeasure M A = 0 := hzero
      apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
        (by simp : (0 : ENNReal) ≠ ⊤)).mp
      simpa [realMeasure] using hrealzero
    · right
      have hrealone : realMeasure M A = 1 := by nlinarith
      apply (ENNReal.toReal_eq_toReal_iff' (by simp : M.μ A ≠ ⊤)
        (by simp : (1 : ENNReal) ≠ ⊤)).mp
      simpa [realMeasure] using hrealone

end Chapter02.ErgodicCorrelations
