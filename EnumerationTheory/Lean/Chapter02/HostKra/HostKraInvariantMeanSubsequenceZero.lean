import Chapter02.HostKra.HostKraU3ZeroSubsequence

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

/-- A pointwise-a.e. Cesàro subsequence converging to zero forces the
checked invariant mean to be zero. -/
theorem invariantMeanLp_eq_zero_of_subsequence
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂M.μ,
      Tendsto (fun k ↦ ergodicAverage M f (nseq k) x)
        Filter.atTop (nhds 0)) :
    HostKraRelativeMean.invariantMeanLp M hM f hf = 0 := by
  have hcond :
      condExp
          (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
          M.μ f =ᵐ[M.μ] 0 := by
    apply invariantCondExp_ae_eq_of_ergodicAverage_subsequence
      M hM f hf 0 nseq hnseq
    exact hpoint
  apply Lp.ext
  have hmean :=
    HostKraRelativeMean.invariantMeanLp_ae_eq_condExp M hM f hf
  have hzeroCoe := Lp.coeFn_zero ℂ 2 M.μ
  filter_upwards [hmean, hcond, hzeroCoe] with x hxmean hxcond hxzero
  have hxcond' :
      M.μ[f | MeasurableSpace.generateFrom (invariantSigmaAlgebra M)] x =
        (0 : ℂ) := by
    simpa using hxcond
  rw [hxmean, hxcond']
  exact hxzero.symm

/-- A pointwise-a.e. common subsequence converging to zero identifies the
invariant mean on any probability measure with the same dynamics as zero. -/
theorem invariantMeanLp_sameDynamics_eq_zero_of_subsequence
    (R : System.{u}) (ν : Measure R.X)
    (hJ : Chapter01.IsMeasurePreservingSystem (sameDynamicsSystem R ν))
    (f : R.X → ℂ)
    (hf : (sameDynamicsSystem R ν).lpMember 2 f)
    (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂ν,
      Tendsto (fun k ↦ ergodicAverage R f (nseq k) x)
        Filter.atTop (nhds 0)) :
    HostKraRelativeMean.invariantMeanLp
      (sameDynamicsSystem R ν) hJ f hf = 0 := by
  have hcond :
      condExp
          (MeasurableSpace.generateFrom
            (invariantSigmaAlgebra (sameDynamicsSystem R ν)))
          ν f =ᵐ[ν] 0 := by
    apply invariantCondExp_sameDynamics_ae_eq_of_subsequence
      R ν hJ f 0 hf nseq hnseq
    exact hpoint
  apply Lp.ext
  have hmean :=
    HostKraRelativeMean.invariantMeanLp_ae_eq_condExp
      (sameDynamicsSystem R ν) hJ f hf
  have hzeroCoe := Lp.coeFn_zero ℂ 2 ν
  filter_upwards [hmean, hcond, hzeroCoe] with x hxmean hxcond hxzero
  have hxcond' :
      (sameDynamicsSystem R ν).μ[
        f | MeasurableSpace.generateFrom
          (invariantSigmaAlgebra (sameDynamicsSystem R ν))] x = 0 := by
    change ν[
      f | MeasurableSpace.generateFrom
        (invariantSigmaAlgebra (sameDynamicsSystem R ν))] x = 0
    simpa using hxcond
  rw [hxmean, hxcond']
  exact hxzero.symm

end Chapter02.HostKraCubeDisintegration
