import Chapter02.HostKra.HostKraErgodicDecomposition

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition

/-- Replace only the measure of a system, retaining its measurable space
and transformation definitionally. -/
def sameDynamicsSystem
    (M : System.{u}) (ν : Measure M.X) : System.{u} where
  X := M.X
  measurableSpace := M.measurableSpace
  μ := ν
  T := M.T

/-- The first relative joining of one invariant conditional component,
packaged with the ambient standard-Borel instance. -/
def conditionalComponentRelativeJoiningSystem
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X)
    (hxMps : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x)) : System.{u} :=
  sameDynamicsSystem
    (relativeJoiningSystem M hM)
    (@relativeJoiningMeasure
      (conditionalComponentSystem M hM D x)
      (by
        change @StandardBorelSpace M.X M.measurableSpace
        exact instSB)
      hxMps)

theorem conditionalComponentRelativeJoiningSystem_mps
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X)
    (hxMps : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x)) :
    Chapter01.IsMeasurePreservingSystem
      (conditionalComponentRelativeJoiningSystem M hM D x hxMps) := by
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  exact relativeJoiningSystem_mps C hxMps

instance conditionalComponentRelativeJoiningSystem_standardBorel
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X)
    (hxMps : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x)) :
    StandardBorelSpace
      (conditionalComponentRelativeJoiningSystem M hM D x hxMps).X := by
  change StandardBorelSpace (M.X × M.X)
  infer_instance

/-- On almost every ergodic conditional component, the guarded component
joining mass is exactly the product of the invariant conditional-expectation
kernel with itself.  This makes the component-mass field measurable without
requiring a measurable proof-valued branch. -/
theorem conditionalComponentRelativeJoiningMass_ae_eq_kernelProd
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
    (s : Set (M.X × M.X)) :
    (fun x ↦ conditionalComponentRelativeJoiningMass M hM D x s)
        =ᵐ[M.μ]
      fun x ↦
        ((Kernel.prod
          (HostKraStandardRelativeJoining.invariantCondExpKernel M hM)
          (HostKraStandardRelativeJoining.invariantCondExpKernel M hM)) x) s := by
  letI : IsMarkovKernel
      (HostKraStandardRelativeJoining.invariantCondExpKernel M hM) := by
    unfold HostKraStandardRelativeJoining.invariantCondExpKernel
    infer_instance
  let κ := HostKraStandardRelativeJoining.invariantCondExpKernel M hM
  filter_upwards [
    invariantCondExpKernel_ae_eq_coreConditionalMeasure
      M hM E D hE hD,
    conditionalComponentSystem_mps_ae M hM E D hE hD,
    conditionalComponent_isErgodic_ae
      M hM E D hE hD hproper hsame] with x hxκ hxMps hxErg
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  have hprod :
      (Kernel.prod κ κ) x =
        (D.measureAt x).prod (D.measureAt x) := by
    rw [Kernel.prod_apply, hxκ]
  simp only [conditionalComponentRelativeJoiningMass, dif_pos hxMps]
  rw [HostKraErgodicRelativeJoining.relativeJoiningMeasure_eq_prod_of_ergodic
    C hxMps hxErg]
  exact congrArg (fun ν : Measure (M.X × M.X) ↦ ν s) hprod.symm

/-- A null set for the global relative joining is null in almost every
ergodic component joining.  This is the null-set transfer used in the
pointwise-ergodic induction of Host--Kra Lemma 3.1. -/
theorem relativeJoining_null_ae_component
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
    (s : Set (M.X × M.X)) (hs : MeasurableSet s)
    (hzero : relativeJoiningMeasure M hM s = 0) :
    ∀ᵐ x ∂M.μ,
      conditionalComponentRelativeJoiningMass M hM D x s = 0 := by
  let κ := HostKraStandardRelativeJoining.invariantCondExpKernel M hM
  let K := Kernel.prod κ κ
  have hEq :=
    conditionalComponentRelativeJoiningMass_ae_eq_kernelProd
      M hM E D hE hD hproper hsame s
  have hmix :=
    relativeJoiningMeasure_apply_eq_lintegral_component_joinings
      M hM E D hE hD hproper hsame s hs
  have hKmeas : Measurable (fun x ↦ (K x) s) := by
    let mInv :=
      MeasurableSpace.generateFrom
        (invariantSigmaAlgebra M)
    have hmInv : mInv ≤ M.measurableSpace :=
      HostKraRelativeJoining.invariantMeasurableSpace_le M
    have hsmall : @Measurable M.X ENNReal mInv inferInstance
        (fun x ↦ (K x) s) :=
      Kernel.measurable_coe K hs
    exact hsmall.mono hmInv le_rfl
  have hKint : ∫⁻ x, (K x) s ∂M.μ = 0 := by
    rw [← lintegral_congr_ae hEq]
    exact hmix.symm.trans hzero
  have hKzero : (fun x ↦ (K x) s) =ᵐ[M.μ] 0 :=
    (lintegral_eq_zero_iff hKmeas).mp hKint
  filter_upwards [hEq, hKzero] with x hx hxzero
  change (K x) s = 0 at hxzero
  exact hx.trans hxzero

/-- Every almost-everywhere statement for the global relative joining holds
almost everywhere for the relative joining of almost every invariant
conditional component.  The component measure is exposed only after a proof
that the component system is measure preserving, so no proof-valued
measurability choice is needed. -/
theorem relativeJoining_ae_ae_component
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
    (p : M.X × M.X → Prop)
    (hp : ∀ᵐ q ∂relativeJoiningMeasure M hM, p q) :
    ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        ∀ᵐ q ∂(@relativeJoiningMeasure
          (conditionalComponentSystem M hM D x)
          (by
            change @StandardBorelSpace M.X M.measurableSpace
            exact instSB)
          hxMps), p q := by
  let N : Set (M.X × M.X) := {q | ¬ p q}
  have hNzero : relativeJoiningMeasure M hM N = 0 := by
    rw [ae_iff] at hp
    exact hp
  let H : Set (M.X × M.X) :=
    toMeasurable (relativeJoiningMeasure M hM) N
  have hNH : N ⊆ H :=
    subset_toMeasurable (relativeJoiningMeasure M hM) N
  have hHmeas : MeasurableSet H :=
    measurableSet_toMeasurable (relativeJoiningMeasure M hM) N
  have hHzero : relativeJoiningMeasure M hM H = 0 :=
    (measure_toMeasurable N).trans hNzero
  have hcomp :=
    relativeJoining_null_ae_component
      M hM E D hE hD hproper hsame H hHmeas hHzero
  filter_upwards [hcomp] with x hx
  intro hxMps
  rw [ae_iff]
  apply measure_mono_null hNH
  simpa only [conditionalComponentRelativeJoiningMass, dif_pos hxMps] using hx

/-- If a strictly increasing subsequence of Koopman averages converges
almost everywhere to a function, then the whole sequence converges to that
same function in `L²`.  This is the nonconstant uniqueness form needed when
the first Host--Kra joining is not ergodic. -/
theorem ergodicAverage_tendsto_of_subsequence_ae
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (g : M.X → ℂ) (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂M.μ,
      Tendsto (fun k ↦ ergodicAverage M f (nseq k) x)
        Filter.atTop (nhds (g x))) :
    Tendsto
      (fun n ↦ eLpNorm
        (fun x ↦ ergodicAverage M f n x - g x) 2 M.μ)
      Filter.atTop (nhds 0) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨fstar, hfstar, _, hconv, _, _, _⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  have hconvSub :
      Tendsto
        (fun k ↦ eLpNorm
          (fun x ↦ ergodicAverage M f (nseq k) x - fstar x)
          2 M.μ)
        Filter.atTop (nhds 0) :=
    hconv.comp hnseq.tendsto_atTop
  obtain ⟨kseq, hkseq, hstarPoint⟩ :=
    Chapter00.Section01.lpNormConvergenceHasAeConvergentSubsequence
      ({ X := M.X
         measurableSpace := M.measurableSpace
         μ := M.μ
         isProbability := hM.1 } :
        Chapter00.BasicProbabilitySpaceData)
      2 (by norm_num)
      (fun k ↦ ergodicAverage M f (nseq k)) fstar
      (fun k ↦ ErgodicAverageLp.ergodicAverage_memLp
        M hM 2 f hf (nseq k))
      hfstar hconvSub
  have hgPoint :
      ∀ᵐ x ∂M.μ,
        Tendsto
          (fun j ↦ ergodicAverage M f (nseq (kseq j)) x)
          Filter.atTop (nhds (g x)) := by
    filter_upwards [hpoint] with x hx
    exact hx.comp hkseq.tendsto_atTop
  have hstarEq : fstar =ᵐ[M.μ] g := by
    filter_upwards [hstarPoint, hgPoint] with x hxstar hxg
    change Tendsto
      (fun j ↦ ergodicAverage M f (nseq (kseq j)) x)
      Filter.atTop (nhds (fstar x)) at hxstar
    exact tendsto_nhds_unique hxstar hxg
  apply hconv.congr'
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards [hstarEq] with x hx
  rw [hx]

/-- Every `L²` function admits one pointwise-a.e. subsequence of its
Koopman Cesàro averages converging to the invariant conditional
expectation. -/
theorem ergodicAverage_subsequence_tendsto_invariantCondExp
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    ∃ nseq : ℕ → ℕ, StrictMono nseq ∧
      ∀ᵐ x ∂M.μ,
        Tendsto (fun k ↦ ergodicAverage M f (nseq k) x)
          Filter.atTop
          (nhds
            (condExp
              (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
              M.μ f x)) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨fstar, hfstar, _, hconv, hInv, _, _⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  obtain ⟨nseq, hnseq, hpoint⟩ :=
    Chapter00.Section01.lpNormConvergenceHasAeConvergentSubsequence
      ({ X := M.X
         measurableSpace := M.measurableSpace
         μ := M.μ
         isProbability := hM.1 } :
        Chapter00.BasicProbabilitySpaceData)
      2 (by norm_num)
      (fun n ↦ ergodicAverage M f n) fstar
      (fun n ↦ ErgodicAverageLp.ergodicAverage_memLp M hM 2 f hf n)
      hfstar hconv
  refine ⟨nseq, hnseq, ?_⟩
  filter_upwards [hpoint, hInv] with x hx hxeq
  change Tendsto (fun k ↦ ergodicAverage M f (nseq k) x)
    Filter.atTop (nhds (fstar x)) at hx
  simpa only [hxeq] using hx

/-- A pointwise-a.e. limit along one strictly increasing Cesàro
subsequence is the invariant conditional expectation. -/
theorem invariantCondExp_ae_eq_of_ergodicAverage_subsequence
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (g : M.X → ℂ) (nseq : ℕ → ℕ) (hnseq : StrictMono nseq)
    (hpoint : ∀ᵐ x ∂M.μ,
      Tendsto (fun k ↦ ergodicAverage M f (nseq k) x)
        Filter.atTop (nhds (g x))) :
    condExp
        (MeasurableSpace.generateFrom (invariantSigmaAlgebra M))
        M.μ f =ᵐ[M.μ] g := by
  letI : IsProbabilityMeasure M.μ := hM.1
  obtain ⟨fstar, hfstar, _, hconv, hInv, _, _⟩ :=
    MeanErgodicL2.vonNeumannMeanErgodicTheorem_proof M hM f hf
  have hconvSub :
      Tendsto
        (fun k ↦ eLpNorm
          (fun x ↦ ergodicAverage M f (nseq k) x - fstar x)
          2 M.μ)
        Filter.atTop (nhds 0) :=
    hconv.comp hnseq.tendsto_atTop
  obtain ⟨kseq, hkseq, hstarPoint⟩ :=
    Chapter00.Section01.lpNormConvergenceHasAeConvergentSubsequence
      ({ X := M.X
         measurableSpace := M.measurableSpace
         μ := M.μ
         isProbability := hM.1 } :
        Chapter00.BasicProbabilitySpaceData)
      2 (by norm_num)
      (fun k ↦ ergodicAverage M f (nseq k)) fstar
      (fun k ↦ ErgodicAverageLp.ergodicAverage_memLp
        M hM 2 f hf (nseq k))
      hfstar hconvSub
  have hgPoint :
      ∀ᵐ x ∂M.μ,
        Tendsto
          (fun j ↦ ergodicAverage M f (nseq (kseq j)) x)
          Filter.atTop (nhds (g x)) := by
    filter_upwards [hpoint] with x hx
    exact hx.comp hkseq.tendsto_atTop
  have hstarEq : fstar =ᵐ[M.μ] g := by
    filter_upwards [hstarPoint, hgPoint] with x hxstar hxg
    change Tendsto
      (fun j ↦ ergodicAverage M f (nseq (kseq j)) x)
      Filter.atTop (nhds (fstar x)) at hxstar
    exact tendsto_nhds_unique hxstar hxg
  exact hInv.trans hstarEq

end Chapter02.HostKraCubeDisintegration
