import Chapter02.HostKra.HostKraCubeComponentDynamics

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition
open HostKraCubeSeminorm

set_option maxHeartbeats 300000 in
/-- A common second-cube ergodic-average subsequence converging to zero
forces `U³` nullity on one conditional component. -/
theorem hasZeroHostKraU3_component_of_cubeAverage_subsequence
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X)
    (hxMps : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x))
    (f : M.X → ℂ) (hfC : MemLp f ⊤ (D.measureAt x))
    (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint :
      ∀ᵐ q ∂(conditionalComponentRelativeJoiningTwoMeasure M hM D x),
        Tendsto
          (fun k ↦ ergodicAverage
            (relativeCubeSystemTwo M hM)
            (cubeLiftTwo M hM f) (nseq k) q)
          Filter.atTop (nhds 0)) :
    @HasZeroHostKraU3
      (conditionalComponentSystem M hM D x)
      (by
        change @StandardBorelSpace M.X M.measurableSpace
        exact instSB)
      hxMps f hfC := by
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  let ν := (relativeCubeSystemTwo C hxMps).μ
  let hC2 := relativeCubeSystemTwo_mps C hxMps
  let hFC := cubeLiftTwo_memLp_two C hxMps f hfC
  have hpointC :
      ∀ᵐ q ∂ν,
        Tendsto
          (fun k ↦ ergodicAverage
            (relativeCubeSystemTwo M hM)
            (cubeLiftTwo M hM f) (nseq k) q)
          Filter.atTop (nhds 0) := by
    have hmeasure :
        conditionalComponentRelativeJoiningTwoMeasure M hM D x = ν := by
      unfold conditionalComponentRelativeJoiningTwoMeasure
      simp only [dif_pos hxMps, ν, C]
      rfl
    rw [← hmeasure]
    exact hpoint
  have hpointJ :
      ∀ᵐ q ∂(relativeCubeSystemTwo C hxMps).μ,
        Tendsto
          (fun k ↦ ergodicAverage
            (relativeCubeSystemTwo C hxMps)
            (cubeLiftTwo C hxMps f) (nseq k) q)
          Filter.atTop (nhds 0) := by
    filter_upwards [hpointC] with q hq
    apply hq.congr'
    exact Filter.Eventually.of_forall fun k ↦ by
      unfold ergodicAverage
      rw [relativeCubeSystemTwo_transform_eq_explicit C hxMps,
        relativeCubeSystemTwo_transform_eq_explicit M hM,
        cubeLiftTwo_eq_explicit C hxMps f,
        cubeLiftTwo_eq_explicit M hM f]
      rw [show C.T = M.T by rfl]
  apply (hasZeroHostKraU3_iff_invariantMean C hxMps f hfC).2
  exact invariantMeanLp_eq_zero_of_subsequence
    (relativeCubeSystemTwo C hxMps) hC2
    (cubeLiftTwo C hxMps f) hFC nseq hnseq hpointJ

end Chapter02.HostKraCubeDisintegration
