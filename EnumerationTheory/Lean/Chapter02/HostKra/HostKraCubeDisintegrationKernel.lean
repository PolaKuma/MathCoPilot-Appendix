import Chapter02.HostKra.HostKraCubeDisintegrationMean

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition

/-- Evaluation of the invariant conditional-expectation kernel on a
measurable set is, after the real-to-complex inclusion, the invariant
indicator mean. -/
theorem invariantCondExpKernel_toReal_ae_eq_invariantIndicatorMean
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (B : Set M.X) (hB : MeasurableSet B) :
    (fun x ↦
        (((invariantCondExpKernel M hM) x B).toReal : ℂ))
      =ᵐ[M.μ] invariantIndicatorMean M B := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let mInv := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hmInv : mInv ≤ M.measurableSpace :=
    HostKraRelativeJoining.invariantMeasurableSpace_le M
  let r : M.X → ℝ := HostKraRelativeJoining.indicatorReal B
  let c : M.X → ℂ := CorrelationMean.indicatorComplex B
  have hrint : Integrable r M.μ :=
    (HostKraRelativeJoining.indicatorReal_memLp M hM B hB)
      |>.integrable (by norm_num)
  have hk :
      (fun x ↦ ((invariantCondExpKernel M hM) x B).toReal)
        =ᵐ[M.μ] condExp mInv M.μ r := by
    simpa only [invariantCondExpKernel, mInv, r, Measure.real_def] using
      (@condExpKernel_ae_eq_condExp M.X mInv M.measurableSpace
        inferInstance M.μ inferInstance hmInv B hB)
  have hcomm :
      Complex.ofRealCLM ∘ condExp mInv M.μ r =ᵐ[M.μ]
        condExp mInv M.μ c := by
    have hraw : Complex.ofRealCLM ∘ r = c := by
      funext x
      by_cases hx : x ∈ B <;>
        simp [r, c, HostKraRelativeJoining.indicatorReal,
          CorrelationMean.indicatorComplex, Set.indicator, hx]
    simpa only [hraw] using
      Complex.ofRealCLM.comp_condExp_comm hrint
  filter_upwards [hk, hcomm] with x hxk hxc
  change (((invariantCondExpKernel M hM) x B).toReal : ℂ) =
    condExp mInv M.μ c x
  calc
    (((invariantCondExpKernel M hM) x B).toReal : ℂ) =
        Complex.ofReal (condExp mInv M.μ r x) := by rw [hxk]
    _ = condExp mInv M.μ c x := by
      simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using hxc

set_option maxHeartbeats 160000 in
/-- For a fixed measurable set, the invariant conditional-expectation
kernel of the global first joining restricts to the invariant kernel of
almost every component first joining. -/
theorem relativeJoining_invariantCondExpKernel_ae_component
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (E : Chapter00.ConditionalExpectationData
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (hE : Chapter00.IsConditionalExpectation
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E)
    (hD : Chapter00.IsConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM) E D)
    (hproper : ∀ x ∈ D.fullSet,
      D.measureAt x (invariantCoreAtom M hM x) = 1)
    (hsame : ∀ x ∈ D.fullSet, ∀ y ∈ D.fullSet,
      invariantCoreAtom M hM x = invariantCoreAtom M hM y →
        D.measureAt x = D.measureAt y)
    (B : Set (M.X × M.X)) (hB : MeasurableSet B) :
    ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        (fun q ↦
            (invariantCondExpKernel
              (conditionalComponentRelativeJoiningSystem
                M hM D x hxMps)
              (conditionalComponentRelativeJoiningSystem_mps
                M hM D x hxMps)) q B)
          =ᵐ[(conditionalComponentRelativeJoiningSystem
              M hM D x hxMps).μ]
        fun q ↦
          (invariantCondExpKernel
            (relativeJoiningSystem M hM)
            (relativeJoiningSystem_mps M hM)) q B := by
  let R := relativeJoiningSystem M hM
  have hR : Chapter01.IsMeasurePreservingSystem R :=
    relativeJoiningSystem_mps M hM
  letI : IsMarkovKernel (invariantCondExpKernel R hR) := by
    unfold invariantCondExpKernel
    infer_instance
  have hκR :=
    invariantCondExpKernel_toReal_ae_eq_invariantIndicatorMean
      R hR B hB
  have hκRcomponent :=
    relativeJoining_ae_ae_component
      M hM E D hE hD hproper hsame
      (fun q ↦
        ((((invariantCondExpKernel R hR) q B).toReal : ℂ)) =
          invariantIndicatorMean R B q)
      hκR
  have hmean :=
    relativeJoining_invariantCondExp_indicator_ae_component
      M hM E D hE hD hproper hsame B hB
  filter_upwards [hκRcomponent, hmean] with x hxκR hxmean
  intro hxMps
  let J := conditionalComponentRelativeJoiningSystem M hM D x hxMps
  have hJ : Chapter01.IsMeasurePreservingSystem J :=
    conditionalComponentRelativeJoiningSystem_mps M hM D x hxMps
  letI : IsMarkovKernel (invariantCondExpKernel J hJ) := by
    unfold invariantCondExpKernel
    infer_instance
  have hκJ :=
    invariantCondExpKernel_toReal_ae_eq_invariantIndicatorMean
      J hJ B hB
  have hxκR' := hxκR hxMps
  have hxmean' := hxmean hxMps
  filter_upwards [hκJ, hxκR', hxmean'] with q hqJ hqR hqmean
  have hc :
      ((((invariantCondExpKernel J hJ) q B).toReal : ℂ)) =
        (((invariantCondExpKernel R hR) q B).toReal : ℂ) :=
    hqJ.trans (hqmean.trans hqR.symm)
  have hr :
      ((invariantCondExpKernel J hJ) q B).toReal =
        ((invariantCondExpKernel R hR) q B).toReal :=
    Complex.ofReal_injective hc
  exact
    (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top ((invariantCondExpKernel J hJ) q) B)
      (measure_ne_top ((invariantCondExpKernel R hR) q) B)).mp hr

end Chapter02.HostKraCubeDisintegration
