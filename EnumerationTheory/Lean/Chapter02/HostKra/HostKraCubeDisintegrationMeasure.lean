import Chapter02.HostKra.HostKraCubeDisintegrationKernel
import Mathlib.Probability.Kernel.MeasurableLIntegral

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition

/-- Almost every component first-joining measure is the value of the
product invariant-conditional kernel used to construct the global first
joining. -/
theorem conditionalComponentRelativeJoiningMeasure_ae_eq_kernelProd
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
        D.measureAt x = D.measureAt y) :
    ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        (conditionalComponentRelativeJoiningSystem M hM D x hxMps).μ =
          (Kernel.prod
            (invariantCondExpKernel M hM)
            (invariantCondExpKernel M hM)) x := by
  letI : IsMarkovKernel (invariantCondExpKernel M hM) := by
    unfold invariantCondExpKernel
    infer_instance
  let κ := invariantCondExpKernel M hM
  filter_upwards [
    invariantCondExpKernel_ae_eq_coreConditionalMeasure
      M hM E D hE hD,
    conditionalComponentSystem_mps_ae M hM E D hE hD,
    conditionalComponent_isErgodic_ae
      M hM E D hE hD hproper hsame] with x hxκ hxMps0 hxErg
  intro hxMps
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  have hprod :
      (Kernel.prod κ κ) x =
        (D.measureAt x).prod (D.measureAt x) := by
    rw [Kernel.prod_apply, hxκ]
  change relativeJoiningMeasure C hxMps =
    (Kernel.prod κ κ) x
  rw [HostKraErgodicRelativeJoining.relativeJoiningMeasure_eq_prod_of_ergodic
    C hxMps hxErg]
  exact hprod.symm

/-- The rectangle formula for a relative joining, written over the ambient
measure rather than its invariant trim. -/
theorem relativeJoiningMeasure_apply_prod_eq_lintegral_ambient
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set M.X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeJoiningMeasure M hM (A ×ˢ B) =
      ∫⁻ x, (invariantCondExpKernel M hM x) A *
        (invariantCondExpKernel M hM x) B ∂M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsMarkovKernel (invariantCondExpKernel M hM) := by
    unfold invariantCondExpKernel
    infer_instance
  let κ := invariantCondExpKernel M hM
  let mInv := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hmInv : mInv ≤ M.measurableSpace :=
    HostKraRelativeJoining.invariantMeasurableSpace_le M
  have hκA : @Measurable M.X ENNReal mInv inferInstance
      (fun x ↦ κ x A) :=
    Kernel.measurable_coe κ hA
  have hκB : @Measurable M.X ENNReal mInv inferInstance
      (fun x ↦ κ x B) :=
    Kernel.measurable_coe κ hB
  have hκmul : @Measurable M.X ENNReal mInv inferInstance
      (fun x ↦ κ x A * κ x B) :=
    hκA.mul hκB
  rw [relativeJoiningMeasure_apply_prod M hM A B hA hB]
  exact lintegral_trim hmInv hκmul

/-- The second relative-joining mass of one invariant conditional
component, with zero on the exceptional non-preserving components. -/
def conditionalComponentRelativeJoiningTwoMass
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X)
    (s : Set ((M.X × M.X) × (M.X × M.X))) : ENNReal :=
  if hxMps : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x) then
    let J := conditionalComponentRelativeJoiningSystem M hM D x hxMps
    relativeJoiningMeasure J
      (conditionalComponentRelativeJoiningSystem_mps M hM D x hxMps) s
  else 0

set_option maxHeartbeats 220000 in
/-- On almost every component, a second-joining rectangle mass is the
integral of the global first-joining invariant kernels against the
component's first-joining measure. -/
theorem conditionalComponentRelativeJoiningTwoMass_ae_eq_kernelIntegral
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
    (A B : Set (M.X × M.X))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (fun x ↦ conditionalComponentRelativeJoiningTwoMass
        M hM D x (A ×ˢ B))
      =ᵐ[M.μ]
    fun x ↦
      ∫⁻ q,
        (invariantCondExpKernel
          (relativeJoiningSystem M hM)
          (relativeJoiningSystem_mps M hM) q) A *
        (invariantCondExpKernel
          (relativeJoiningSystem M hM)
          (relativeJoiningSystem_mps M hM) q) B
      ∂(Kernel.prod
        (invariantCondExpKernel M hM)
        (invariantCondExpKernel M hM)) x := by
  have hmps :=
    conditionalComponentSystem_mps_ae M hM E D hE hD
  have hmeasure :=
    conditionalComponentRelativeJoiningMeasure_ae_eq_kernelProd
      M hM E D hE hD hproper hsame
  have hκA :=
    relativeJoining_invariantCondExpKernel_ae_component
      M hM E D hE hD hproper hsame A hA
  have hκB :=
    relativeJoining_invariantCondExpKernel_ae_component
      M hM E D hE hD hproper hsame B hB
  filter_upwards [hmps, hmeasure, hκA, hκB]
    with x hxMps hxmeasure hxκA hxκB
  let J := conditionalComponentRelativeJoiningSystem M hM D x hxMps
  have hJ : Chapter01.IsMeasurePreservingSystem J :=
    conditionalComponentRelativeJoiningSystem_mps M hM D x hxMps
  let R := relativeJoiningSystem M hM
  have hR : Chapter01.IsMeasurePreservingSystem R :=
    relativeJoiningSystem_mps M hM
  simp only [conditionalComponentRelativeJoiningTwoMass, dif_pos hxMps]
  rw [relativeJoiningMeasure_apply_prod_eq_lintegral_ambient
    J hJ A B hA hB]
  have hxκA' :
      (fun q ↦ (invariantCondExpKernel J hJ q) A)
        =ᵐ[(Kernel.prod
          (invariantCondExpKernel M hM)
          (invariantCondExpKernel M hM)) x]
      fun q ↦ (invariantCondExpKernel R hR q) A := by
    rw [← hxmeasure hxMps]
    exact hxκA hxMps
  have hxκB' :
      (fun q ↦ (invariantCondExpKernel J hJ q) B)
        =ᵐ[(Kernel.prod
          (invariantCondExpKernel M hM)
          (invariantCondExpKernel M hM)) x]
      fun q ↦ (invariantCondExpKernel R hR q) B := by
    rw [← hxmeasure hxMps]
    exact hxκB hxMps
  rw [hxmeasure hxMps]
  apply lintegral_congr_ae
  filter_upwards [hxκA', hxκB'] with q hqA hqB
  rw [hqA, hqB]

set_option maxHeartbeats 260000 in
/-- Host--Kra Lemma 3.1 at the second cube level, first on measurable
rectangles: the global second joining is the mixture of the component
second joinings. -/
theorem relativeCubeSystemTwo_measure_prod_eq_lintegral_components
    (M : System.{u}) [StandardBorelSpace M.X]
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
    (A B : Set (M.X × M.X))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    relativeJoiningMeasure
        (relativeJoiningSystem M hM)
        (relativeJoiningSystem_mps M hM) (A ×ˢ B) =
      ∫⁻ x, conditionalComponentRelativeJoiningTwoMass
        M hM D x (A ×ˢ B) ∂M.μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  letI : IsMarkovKernel (invariantCondExpKernel M hM) := by
    unfold invariantCondExpKernel
    infer_instance
  let κ := invariantCondExpKernel M hM
  let K := Kernel.prod κ κ
  let mInvM := MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
  have hmInvM : mInvM ≤ M.measurableSpace :=
    HostKraRelativeJoining.invariantMeasurableSpace_le M
  let R := relativeJoiningSystem M hM
  have hR : Chapter01.IsMeasurePreservingSystem R :=
    relativeJoiningSystem_mps M hM
  letI : IsMarkovKernel (invariantCondExpKernel R hR) := by
    unfold invariantCondExpKernel
    infer_instance
  let κR := invariantCondExpKernel R hR
  let F : R.X → ENNReal := fun q ↦ κR q A * κR q B
  let mInvR := MeasurableSpace.generateFrom (invariantSigmaAlgebra R)
  have hmInvR : mInvR ≤ R.measurableSpace :=
    HostKraRelativeJoining.invariantMeasurableSpace_le R
  have hκRA : @Measurable R.X ENNReal mInvR inferInstance
      (fun q ↦ κR q A) :=
    Kernel.measurable_coe κR hA
  have hκRB : @Measurable R.X ENNReal mInvR inferInstance
      (fun q ↦ κR q B) :=
    Kernel.measurable_coe κR hB
  have hF : @Measurable R.X ENNReal R.measurableSpace inferInstance F := by
    exact (hκRA.mul hκRB).mono hmInvR le_rfl
  have hG : @Measurable M.X ENNReal mInvM inferInstance
      (fun x ↦ ∫⁻ q, F q ∂K x) := by
    have huncurry :
        @Measurable (M.X × R.X) ENNReal
          (@Prod.instMeasurableSpace M.X R.X mInvM R.measurableSpace)
          inferInstance
          (Function.uncurry (fun (_ : M.X) (q : R.X) ↦ F q)) :=
      hF.comp measurable_snd
    exact huncurry.lintegral_kernel_prod_right (κ := K)
  have hmass :=
    conditionalComponentRelativeJoiningTwoMass_ae_eq_kernelIntegral
      M hM E D hE hD hproper hsame A B hA hB
  rw [relativeJoiningMeasure_apply_prod_eq_lintegral_ambient
    R hR A B hA hB]
  change (∫⁻ q, F q ∂relativeJoiningMeasure M hM) =
    ∫⁻ x, conditionalComponentRelativeJoiningTwoMass
      M hM D x (A ×ˢ B) ∂M.μ
  unfold relativeJoiningMeasure
  have hFae : AEMeasurable F
      ((fun x ↦ K x) ∘ₘ
        M.μ.trim (HostKraRelativeJoining.invariantMeasurableSpace_le M)) :=
    hF.aemeasurable
  rw [Measure.lintegral_bind K.aemeasurable hFae]
  rw [lintegral_trim hmInvM hG]
  exact lintegral_congr_ae hmass.symm

end Chapter02.HostKraCubeDisintegration
