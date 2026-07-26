import Chapter02.HostKra.HostKraCubeDisintegration

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition

/-- The invariant conditional expectation of a measurable-set indicator in
a system. -/
def invariantIndicatorMean
    (M : System.{u}) (B : Set M.X) : M.X → ℂ :=
  condExp
    (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
    M.μ (CorrelationMean.indicatorComplex B)

/-- A pointwise-a.e. subsequential limit of indicator Cesàro averages is
the invariant indicator mean. -/
theorem invariantIndicatorMean_ae_eq_of_subsequence
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (B : Set M.X) (hB : MeasurableSet B)
    (g : M.X → ℂ) (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂M.μ,
      Tendsto
        (fun k ↦ ergodicAverage M
          (CorrelationMean.indicatorComplex B) (nseq k) x)
        Filter.atTop (nhds (g x))) :
    invariantIndicatorMean M B =ᵐ[M.μ] g := by
  have hf : M.lpMember 2 (CorrelationMean.indicatorComplex B) :=
    CorrelationMean.indicatorComplex_memLp M hM B hB 2
  simpa only [invariantIndicatorMean] using
    invariantCondExp_ae_eq_of_ergodicAverage_subsequence
      M hM (CorrelationMean.indicatorComplex B) hf
      g nseq hnseq hpoint

/-- The invariant indicator mean for a system obtained by changing only
the measure is identified by Cesàro averages of the unchanged dynamics. -/
theorem invariantIndicatorMean_sameDynamics_ae_eq_of_subsequence
    (M : System.{u}) (ν : Measure M.X)
    (hMν : Chapter01.IsMeasurePreservingSystem (sameDynamicsSystem M ν))
    (B : Set M.X) (hB : MeasurableSet B)
    (g : M.X → ℂ) (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂ν,
      Tendsto
        (fun k ↦ ergodicAverage M
          (CorrelationMean.indicatorComplex B) (nseq k) x)
        Filter.atTop (nhds (g x))) :
    invariantIndicatorMean (sameDynamicsSystem M ν) B =ᵐ[ν] g := by
  apply invariantIndicatorMean_ae_eq_of_subsequence
    (sameDynamicsSystem M ν) hMν B hB g nseq hnseq
  exact hpoint

set_option maxHeartbeats 60000 in
/-- If the global first-joining Cesàro subsequence converges almost
everywhere inside one component joining, its limit is that component's
invariant conditional expectation. -/
theorem componentInvariantIndicatorMean_eq_of_global_subsequence
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X)
    (hxMps : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x))
    (B : Set (M.X × M.X)) (hB : MeasurableSet B)
    (nseq : ℕ → ℕ) (hnseq : StrictMono nseq) :
    let R := relativeJoiningSystem M hM
    let J := conditionalComponentRelativeJoiningSystem M hM D x hxMps
    (∀ᵐ q ∂J.μ,
        Tendsto
          (fun k ↦ ergodicAverage R
            (CorrelationMean.indicatorComplex B) (nseq k) q)
          Filter.atTop
          (nhds (invariantIndicatorMean R B q))) →
      invariantIndicatorMean J B =ᵐ[J.μ]
        invariantIndicatorMean R B := by
  dsimp only
  intro hpoint
  let R := relativeJoiningSystem M hM
  let J := conditionalComponentRelativeJoiningSystem M hM D x hxMps
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  let ν : Measure R.X := @relativeJoiningMeasure C inferInstance hxMps
  have hJ : Chapter01.IsMeasurePreservingSystem J :=
    conditionalComponentRelativeJoiningSystem_mps M hM D x hxMps
  change invariantIndicatorMean (sameDynamicsSystem R ν) B =ᵐ[ν]
    invariantIndicatorMean R B
  apply invariantIndicatorMean_sameDynamics_ae_eq_of_subsequence
      R ν hJ B hB
      (invariantIndicatorMean R B)
      nseq hnseq
  exact hpoint

/-- Invariant conditional expectations are compatible with a change of
invariant probability measure whenever the dynamics are unchanged and
global almost-everywhere statements transfer to the new measure.

This is the function-valued core of the component-disintegration argument;
it is independent of the concrete conditional-measure construction. -/
theorem invariantCondExp_ae_eq_of_ae_transfer
    (R : System.{u}) (ν : Measure R.X)
    (hR : Chapter01.IsMeasurePreservingSystem R)
    (hJ : Chapter01.IsMeasurePreservingSystem (sameDynamicsSystem R ν))
    (f : R.X → ℂ)
    (hfR : R.lpMember 2 f)
    (hfJ : (sameDynamicsSystem R ν).lpMember 2 f)
    (htransfer : ∀ p : R.X → Prop,
      (∀ᵐ x ∂(R.μ), p x) → ∀ᵐ x ∂ν, p x) :
    condExp
        (MeasurableSpace.generateFrom
          (invariantSigmaAlgebra (sameDynamicsSystem R ν)))
        ν f =ᵐ[ν]
      condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
        R.μ f := by
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    ergodicAverage_subsequence_tendsto_invariantCondExp R hR f hfR
  apply invariantCondExp_ae_eq_of_ergodicAverage_subsequence
    (sameDynamicsSystem R ν) hJ f hfJ
      (condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
        R.μ f)
      nseq hnseq
  have hpointJ := htransfer _ hpoint
  exact hpointJ

/-- A pointwise-a.e. subsequential limit remains the invariant conditional
expectation after changing only the invariant probability measure.  The
ergodic averages are written using the original system because the dynamics
are definitionally unchanged. -/
theorem invariantCondExp_sameDynamics_ae_eq_of_subsequence
    (R : System.{u}) (ν : Measure R.X)
    (hJ : Chapter01.IsMeasurePreservingSystem (sameDynamicsSystem R ν))
    (f g : R.X → ℂ)
    (hfJ : (sameDynamicsSystem R ν).lpMember 2 f)
    (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂ν,
      Tendsto
        (fun k ↦ ergodicAverage R f (nseq k) x)
        Filter.atTop (nhds (g x))) :
    condExp
        (MeasurableSpace.generateFrom
          (invariantSigmaAlgebra (sameDynamicsSystem R ν)))
        ν f =ᵐ[ν] g := by
  apply invariantCondExp_ae_eq_of_ergodicAverage_subsequence
    (sameDynamicsSystem R ν) hJ f hfJ g nseq hnseq
  exact hpoint

end Chapter02.HostKraCubeDisintegration
