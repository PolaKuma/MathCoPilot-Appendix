import Chapter02.HostKra.HostKraU3ComponentFixed

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition
open HostKraCubeSeminorm

/-- Vanishing of the third Host--Kra seminorm passes to almost every
invariant conditional component, without an ergodicity assumption on the
ambient system. -/
theorem hasZeroHostKraU3_ae_component
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
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM f hf) :
    ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        ∀ hfC : MemLp f ⊤ (D.measureAt x),
          @HasZeroHostKraU3
            (conditionalComponentSystem M hM D x)
            (by
              change @StandardBorelSpace M.X M.measurableSpace
              exact instSB)
            hxMps f hfC := by
  obtain ⟨nseq, hnseq, hpointZero⟩ :=
    hasZeroHostKraU3_exists_cubeAverage_subsequence_zero
      M hM f hf hzero
  have htransfer :=
    relativeCubeSystemTwo_ae_ae_component
      M hM E D hE hD hproper hsame
      (fun q ↦
        Tendsto
          (fun k ↦ ergodicAverage
            (relativeCubeSystemTwo M hM)
            (cubeLiftTwo M hM f) (nseq k) q)
          Filter.atTop (nhds 0))
      hpointZero
  filter_upwards [htransfer] with x hxpoint
  intro hxMps hfC
  apply hasZeroHostKraU3_component_of_cubeAverage_subsequence
    M hM D x hxMps f hfC nseq hnseq
  have hmeasure :
      conditionalComponentRelativeJoiningTwoMeasure M hM D x =
        (@relativeCubeSystemTwo
          (conditionalComponentSystem M hM D x)
          (by
            change @StandardBorelSpace M.X M.measurableSpace
            exact instSB) hxMps).μ := by
    unfold conditionalComponentRelativeJoiningTwoMeasure
    simp only [dif_pos hxMps]
    rfl
  rw [hmeasure]
  exact hxpoint hxMps

end Chapter02.HostKraCubeDisintegration
