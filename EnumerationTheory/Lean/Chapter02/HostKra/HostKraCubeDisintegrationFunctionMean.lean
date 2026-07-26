import Chapter02.HostKra.HostKraCubeDisintegrationMean

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition

/-- On almost every invariant conditional component, the invariant
conditional expectation on the component's first relative joining agrees
with the restriction of the global invariant conditional expectation.

The componentwise `L²` hypothesis is kept explicit here; a later bounded
function wrapper supplies it for the Host--Kra cube functions. -/
theorem relativeJoining_invariantCondExp_ae_component
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
    (f : M.X × M.X → ℂ)
    (hfR : (relativeJoiningSystem M hM).lpMember 2 f)
    (hfcomp : ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        (conditionalComponentRelativeJoiningSystem M hM D x hxMps).lpMember 2 f) :
    ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        condExp
            (MeasurableSpace.generateFrom
              (invariantSigmaAlgebra
                (conditionalComponentRelativeJoiningSystem M hM D x hxMps)))
            (conditionalComponentRelativeJoiningSystem M hM D x hxMps).μ f
          =ᵐ[(conditionalComponentRelativeJoiningSystem M hM D x hxMps).μ]
        condExp
            (MeasurableSpace.generateFrom
              (invariantSigmaAlgebra (relativeJoiningSystem M hM)))
            (relativeJoiningSystem M hM).μ f := by
  let R := relativeJoiningSystem M hM
  have hR : Chapter01.IsMeasurePreservingSystem R :=
    relativeJoiningSystem_mps M hM
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    ergodicAverage_subsequence_tendsto_invariantCondExp R hR f hfR
  have htransfer :=
    relativeJoining_ae_ae_component
      M hM E D hE hD hproper hsame
      (fun q ↦
        Tendsto (fun k ↦ ergodicAverage R f (nseq k) q)
          Filter.atTop
          (nhds
            (condExp
              (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
              R.μ f q)))
      hpoint
  filter_upwards [hfcomp, htransfer] with x hxmem hxpoint
  intro hxMps
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  let ν : Measure R.X := @relativeJoiningMeasure C inferInstance hxMps
  have hJ : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentRelativeJoiningSystem M hM D x hxMps) :=
    conditionalComponentRelativeJoiningSystem_mps M hM D x hxMps
  have hxpoint' :
      ∀ᵐ q ∂ν,
        Tendsto (fun k ↦ ergodicAverage R f (nseq k) q)
          Filter.atTop
          (nhds
            (condExp
              (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
              R.μ f q)) := by
    exact hxpoint hxMps
  change
    condExp
        (MeasurableSpace.generateFrom
          (invariantSigmaAlgebra (sameDynamicsSystem R ν)))
        ν f =ᵐ[ν]
      condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
        R.μ f
  apply invariantCondExp_sameDynamics_ae_eq_of_subsequence
    R ν hJ f
      (condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
        R.μ f)
      (by exact hxmem hxMps) nseq hnseq
  exact hxpoint'

end Chapter02.HostKraCubeDisintegration
