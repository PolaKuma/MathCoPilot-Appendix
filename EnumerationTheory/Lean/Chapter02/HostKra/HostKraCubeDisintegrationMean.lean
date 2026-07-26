import Chapter02.HostKra.HostKraCubeDisintegrationComponentMean

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition

set_option maxHeartbeats 120000 in
/-- On almost every invariant conditional component, the invariant
conditional expectation on the component's first relative joining agrees
with the restriction of the invariant conditional expectation on the
global first relative joining, for every measurable indicator.  This is
the analytic compatibility step in Host--Kra Lemma 3.1. -/
theorem relativeJoining_invariantCondExp_indicator_ae_component
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
        invariantIndicatorMean
            (conditionalComponentRelativeJoiningSystem M hM D x hxMps) B
          =ᵐ[(conditionalComponentRelativeJoiningSystem
              M hM D x hxMps).μ]
        invariantIndicatorMean (relativeJoiningSystem M hM) B := by
  let R := relativeJoiningSystem M hM
  have hR : Chapter01.IsMeasurePreservingSystem R :=
    relativeJoiningSystem_mps M hM
  let f : M.X × M.X → ℂ := CorrelationMean.indicatorComplex B
  have hfR : R.lpMember 2 f := by
    simpa only [R, f] using
      CorrelationMean.indicatorComplex_memLp R hR B hB 2
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    ergodicAverage_subsequence_tendsto_invariantCondExp R hR f hfR
  have htransfer :=
    relativeJoining_ae_ae_component
      M hM E D hE hD hproper hsame
      (fun q ↦
        Tendsto (fun k ↦ ergodicAverage R f (nseq k) q)
          Filter.atTop
          (nhds (invariantIndicatorMean R B q)))
      hpoint
  filter_upwards [htransfer] with x hx
  intro hxMps
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  have hxpoint :
      ∀ᵐ q ∂(conditionalComponentRelativeJoiningSystem M hM D x hxMps).μ,
        Tendsto (fun k ↦ ergodicAverage R f (nseq k) q)
          Filter.atTop
          (nhds (invariantIndicatorMean R B q)) := by
    change
      ∀ᵐ q ∂(@relativeJoiningMeasure C inferInstance hxMps),
        Tendsto (fun k ↦ ergodicAverage R f (nseq k) q)
          Filter.atTop
          (nhds (invariantIndicatorMean R B q))
    exact hx hxMps
  simpa only [R, f] using
    componentInvariantIndicatorMean_eq_of_global_subsequence
      M hM D x hxMps B hB nseq hnseq hxpoint

end Chapter02.HostKraCubeDisintegration
