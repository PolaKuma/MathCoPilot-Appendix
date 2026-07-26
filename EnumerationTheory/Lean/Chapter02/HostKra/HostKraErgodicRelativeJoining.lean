import Chapter02.HostKra.HostKraRelativeJoiningComplex

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraErgodicRelativeJoining

universe u

open HostKraRelativeJoining
open HostKraStandardRelativeJoining
open HostKraRelativeJoiningComplex

/-- In an ergodic system the invariant mean of an `L²` function is its
ordinary integral, represented as a constant `L²` function. -/
theorem invariantMeanLp_ae_eq_integral_of_ergodic
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    (fun x ↦ HostKraRelativeMean.invariantMeanLp M hM f hf x) =ᵐ[M.μ]
      fun _ ↦ ∫ x, f x ∂M.μ := by
  let result :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  exact (HostKraRelativeMean.invariantMeanLp_coe M hM f hf).trans
    (result.choose_spec.2.2.2.2.2 hErg)

/-- The real invariant conditional probability of a measurable set is the
constant ordinary probability in an ergodic system. -/
theorem invariantIndicatorLp_ae_eq_measureReal_of_ergodic
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    invariantIndicatorLp M hM A hA =ᵐ[M.μ]
      fun _ ↦ (M.μ A).toReal := by
  have hmean :=
    invariantMeanLp_ae_eq_integral_of_ergodic M hM hErg
      (CorrelationMean.indicatorComplex A)
      (CorrelationMean.indicatorComplex_memLp M hM A hA 2)
  have hid :=
    invariantMeanLp_indicatorComplex M hM A hA
  have hcomplex := invariantIndicatorComplexLp_coe M hM A hA
  have hint :
      (∫ x, CorrelationMean.indicatorComplex A x ∂M.μ) =
        ((M.μ A).toReal : ℂ) :=
    CorrelationMean.integral_indicatorComplex M A hA
  filter_upwards [hmean, hcomplex] with x hmx hcx
  rw [hid] at hmx
  rw [hcx, hint] at hmx
  exact Complex.ofReal_injective hmx

/-- On an ergodic system the relative rectangle functional is the product
of the two ordinary probabilities. -/
theorem relativeRectangleMass_eq_mul_of_ergodic
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeRectangleMass M hM A B hA hB =
      (M.μ A).toReal * (M.μ B).toReal := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [relativeRectangleMass, L2.inner_def]
  calc
    (∫ x, @inner ℝ ℝ _
        (invariantIndicatorLp M hM A hA x)
        (invariantIndicatorLp M hM B hB x) ∂M.μ) =
        ∫ _x, (M.μ A).toReal * (M.μ B).toReal ∂M.μ := by
          apply integral_congr_ae
          filter_upwards [
            invariantIndicatorLp_ae_eq_measureReal_of_ergodic
              M hM hErg A hA,
            invariantIndicatorLp_ae_eq_measureReal_of_ergodic
              M hM hErg B hB]
            with x hAx hBx
          rw [hAx, hBx]
          simp only [RCLike.inner_apply, conj_trivial]
          exact mul_comm _ _
    _ = (M.μ A).toReal * (M.μ B).toReal := by simp

/-- For an ergodic standard Borel system, relative independence over the
invariant sigma-algebra is ordinary independence. -/
theorem relativeJoiningMeasure_eq_prod_of_ergodic
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    relativeJoiningMeasure M hM = M.μ.prod M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  apply Measure.ext_prod
  intro A B hA hB
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (relativeJoiningMeasure M hM) (A ×ˢ B))
    (measure_ne_top (M.μ.prod M.μ) (A ×ˢ B))).mp
  rw [relativeJoiningMeasure_apply_prod_toReal M hM A B hA hB,
    relativeRectangleMass_eq_mul_of_ergodic M hM hErg A B hA hB,
    Measure.prod_prod]
  simp only [ENNReal.toReal_mul]

/-- System-level form of `relativeJoiningMeasure_eq_prod_of_ergodic`: the
first relative Host--Kra cube is the ordinary Cartesian square in the
ergodic case. -/
theorem relativeCubeSystemOne_eq_productSystem_of_ergodic
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M) :
    HostKraStandardRelativeJoining.relativeCubeSystemOne M hM =
      MultipleKhintchineCartesian.productSystem M M := by
  unfold HostKraStandardRelativeJoining.relativeCubeSystemOne
  unfold relativeJoiningSystem
  unfold MultipleKhintchineCartesian.productSystem
  rw [relativeJoiningMeasure_eq_prod_of_ergodic M hM hErg]
  unfold relativeJoiningTransform
  congr 1

end Chapter02.HostKraErgodicRelativeJoining
