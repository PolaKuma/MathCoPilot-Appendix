import Chapter02.HostKra.HostKraCubeDisintegrationNull

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraCubeSeminorm

/-- A `U³`-null bounded function has a common pointwise-a.e. subsequence
of its second-cube ergodic averages converging to zero. -/
theorem hasZeroHostKraU3_exists_cubeAverage_subsequence_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM f hf) :
    ∃ nseq : ℕ → ℕ, StrictMono nseq ∧
      ∀ᵐ q ∂(relativeCubeSystemTwo M hM).μ,
        Tendsto
          (fun k ↦ ergodicAverage
            (relativeCubeSystemTwo M hM)
            (cubeLiftTwo M hM f) (nseq k) q)
          Filter.atTop (nhds 0) := by
  let R := relativeCubeSystemTwo M hM
  let hR := relativeCubeSystemTwo_mps M hM
  let F := cubeLiftTwo M hM f
  let hF := cubeLiftTwo_memLp_two M hM f hf
  have hmeanZero :
      HostKraRelativeMean.invariantMeanLp R hR F hF = 0 := by
    simpa only [R, hR, F, hF] using
      (hasZeroHostKraU3_iff_invariantMean M hM f hf).1 hzero
  have hmeanAe :
      (fun q ↦ HostKraRelativeMean.invariantMeanLp R hR F hF q)
        =ᵐ[R.μ] 0 := by
    rw [hmeanZero]
    exact Lp.coeFn_zero ℂ 2 R.μ
  have hcondZero :
      condExp
          (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
          R.μ F =ᵐ[R.μ] 0 := by
    exact
      (HostKraRelativeMean.invariantMeanLp_ae_eq_condExp R hR F hF).symm.trans
        hmeanAe
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    ergodicAverage_subsequence_tendsto_invariantCondExp R hR F hF
  refine ⟨nseq, hnseq, ?_⟩
  filter_upwards [hpoint, hcondZero] with q hq hqzero
  have hqzero' :
      condExp
          (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
          R.μ F q = (0 : ℂ) := by
    simpa using hqzero
  change Tendsto (fun k ↦ ergodicAverage R F (nseq k) q)
    Filter.atTop
    (nhds
      (condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra R))
        R.μ F q)) at hq
  rw [hqzero'] at hq
  simpa only [R, F] using hq

end Chapter02.HostKraCubeDisintegration
