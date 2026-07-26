import Chapter02.HostKra.HostKraCubeDisintegrationMeasure

open Classical Filter Set MeasureTheory ProbabilityTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition
open HostKraRelativeJoining

/-- The invariant conditional kernel, regarded as a kernel whose source
has the ambient measurable space. -/
def ambientInvariantCondExpKernel
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    @Kernel M.X M.X M.measurableSpace M.measurableSpace :=
  (invariantCondExpKernel M hM).comap id
    (measurable_id.mono (invariantMeasurableSpace_le M) le_rfl)

instance ambientInvariantCondExpKernel_isMarkov
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsMarkovKernel (ambientInvariantCondExpKernel M hM) := by
  unfold ambientInvariantCondExpKernel invariantCondExpKernel
  infer_instance

/-- The explicit fourfold kernel obtained by first choosing a base
ergodic component and then taking its second relative cube. -/
def secondCubeComponentKernel
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    @Kernel M.X
      ((M.X × M.X) × (M.X × M.X))
      (invariantMeasurableSpace M)
      inferInstance := by
  let κ := invariantCondExpKernel M hM
  let R := relativeJoiningSystem M hM
  let hR := relativeJoiningSystem_mps M hM
  let κR := ambientInvariantCondExpKernel R hR
  exact (Kernel.prod κR κR).comp (Kernel.prod κ κ)

instance secondCubeComponentKernel_isMarkov
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsMarkovKernel (secondCubeComponentKernel M hM) := by
  let κ := invariantCondExpKernel M hM
  letI : IsMarkovKernel κ := by
    dsimp only [κ]
    unfold invariantCondExpKernel
    infer_instance
  let R := relativeJoiningSystem M hM
  let hR := relativeJoiningSystem_mps M hM
  let κR := ambientInvariantCondExpKernel R hR
  letI : IsMarkovKernel κR := by
    dsimp only [κR]
    infer_instance
  change IsMarkovKernel ((Kernel.prod κR κR).comp (Kernel.prod κ κ))
  letI : IsMarkovKernel (Kernel.prod κ κ) := by infer_instance
  letI : IsMarkovKernel (Kernel.prod κR κR) := by infer_instance
  infer_instance

lemma secondCubeComponentKernel_apply_prod
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B : Set (M.X × M.X))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (x : M.X) :
    secondCubeComponentKernel M hM x (A ×ˢ B) =
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
  rw [secondCubeComponentKernel, Kernel.comp_apply' _ _ _ (hA.prod hB)]
  apply lintegral_congr
  intro q
  calc
    ((Kernel.prod
        (ambientInvariantCondExpKernel
          (relativeJoiningSystem M hM)
          (relativeJoiningSystem_mps M hM))
        (ambientInvariantCondExpKernel
          (relativeJoiningSystem M hM)
          (relativeJoiningSystem_mps M hM))) q) (A ×ˢ B) =
        (ambientInvariantCondExpKernel
          (relativeJoiningSystem M hM)
          (relativeJoiningSystem_mps M hM) q) A *
        (ambientInvariantCondExpKernel
          (relativeJoiningSystem M hM)
          (relativeJoiningSystem_mps M hM) q) B :=
      Kernel.prod_apply_prod
    _ = _ := by
      simp only [ambientInvariantCondExpKernel, Kernel.comap_apply']
      rfl

/-- The guarded second-cube component as an actual measure, with the zero
measure on exceptional non-preserving components. -/
def conditionalComponentRelativeJoiningTwoMeasure
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X) :
    Measure ((M.X × M.X) × (M.X × M.X)) :=
  if hxMps : Chapter01.IsMeasurePreservingSystem
      (conditionalComponentSystem M hM D x) then
    @relativeJoiningMeasure
      (conditionalComponentRelativeJoiningSystem M hM D x hxMps)
      (by
        change StandardBorelSpace ((M.X × M.X))
        infer_instance)
      (conditionalComponentRelativeJoiningSystem_mps M hM D x hxMps)
  else 0

lemma conditionalComponentRelativeJoiningTwoMeasure_apply
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (D : Chapter00.ConditionalMeasureFamily
      (invariantBaseProbabilitySpace M hM)
      (invariantCoreSigmaAlgebra M hM))
    (x : M.X) (s : Set ((M.X × M.X) × (M.X × M.X))) :
    conditionalComponentRelativeJoiningTwoMeasure M hM D x s =
      conditionalComponentRelativeJoiningTwoMass M hM D x s := by
  unfold conditionalComponentRelativeJoiningTwoMeasure
    conditionalComponentRelativeJoiningTwoMass
  split <;> rfl

set_option maxHeartbeats 180000 in
/-- Almost every component second-cube measure is the value of the
explicit second-cube component kernel.  The passage from rectangles to all
measurable sets is a countable pi-system argument. -/
theorem conditionalComponentRelativeJoiningTwoMeasure_ae_eq_kernel
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
        (@relativeCubeSystemTwo
          (conditionalComponentSystem M hM D x)
          (by
            change @StandardBorelSpace M.X M.measurableSpace
            exact instSB) hxMps).μ =
          secondCubeComponentKernel M hM x := by
  let R := relativeJoiningSystem M hM
  let B : Set (Set R.X) := ambientCountableAlgebra R
  let S : Set (Set (R.X × R.X)) :=
    Set.image2 (· ×ˢ ·) B B
  have hBcount : B.Countable :=
    ambientCountableAlgebra_countable R
  have hScount : S.Countable :=
    hBcount.image2 hBcount (· ×ˢ ·)
  have hBmeas : ∀ A ∈ B, MeasurableSet A :=
    fun _ hA ↦ ambientCountableAlgebra_measurable R hA
  have hBgen :
      MeasurableSpace.generateFrom B = R.measurableSpace := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro A hA
      exact hBmeas A hA
    · calc
        R.measurableSpace =
            MeasurableSpace.generateFrom
              (MeasurableSpace.countableGeneratingSet R.X) :=
          MeasurableSpace.generateFrom_countableGeneratingSet.symm
        _ ≤ MeasurableSpace.generateFrom B :=
          MeasurableSpace.generateFrom_mono
            MeasureTheory.self_subset_generateSetAlgebra
  have hBspan : IsCountablySpanning B := by
    let hAlg := ambientCountableAlgebra_isAlgebra R
    refine ⟨fun _ ↦ Set.univ, ?_, ?_⟩
    intro n
    simpa using hAlg.2.2 ∅ hAlg.1
    ext x
    simp
  have hSgen :
      MeasurableSpace.generateFrom S =
        (relativeCubeSystemTwo M hM).measurableSpace := by
    change MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) B B) =
      @Prod.instMeasurableSpace R.X R.X R.measurableSpace R.measurableSpace
    exact generateFrom_eq_prod hBgen hBgen hBspan hBspan
  have hSpi : IsPiSystem S := by
    apply IsPiSystem.prod
    · intro A hA B₀ hB₀ _
      have hAlg := ambientCountableAlgebra_isAlgebra R
      have hdiff := hAlg.2.1 A hA B₀ᶜ (hAlg.2.2 B₀ hB₀)
      simpa [Set.diff_eq] using hdiff
    · intro A hA B₀ hB₀ _
      have hAlg := ambientCountableAlgebra_isAlgebra R
      have hdiff := hAlg.2.1 A hA B₀ᶜ (hAlg.2.2 B₀ hB₀)
      simpa [Set.diff_eq] using hdiff
  have hrect (A B₀ : Set R.X) (hA : MeasurableSet A)
      (hB₀ : MeasurableSet B₀) :
      ∀ᵐ x ∂M.μ,
        secondCubeComponentKernel M hM x (A ×ˢ B₀) =
          conditionalComponentRelativeJoiningTwoMeasure
            M hM D x (A ×ˢ B₀) := by
    have hmass :=
      conditionalComponentRelativeJoiningTwoMass_ae_eq_kernelIntegral
        M hM E D hE hD hproper hsame A B₀ hA hB₀
    filter_upwards [hmass] with x hx
    rw [secondCubeComponentKernel_apply_prod M hM A B₀ hA hB₀ x]
    rw [conditionalComponentRelativeJoiningTwoMeasure_apply]
    exact hx.symm
  have hbasic :
      ∀ᵐ x ∂M.μ, ∀ s ∈ S,
        secondCubeComponentKernel M hM x s =
          conditionalComponentRelativeJoiningTwoMeasure M hM D x s := by
    letI : Countable S := hScount.to_subtype
    have hsubtype : ∀ t : S, ∀ᵐ x ∂M.μ,
        secondCubeComponentKernel M hM x t.1 =
          conditionalComponentRelativeJoiningTwoMeasure M hM D x t.1 := by
      intro t
      rcases t.2 with ⟨A, hA, B₀, hB₀, ht⟩
      rw [← ht]
      exact hrect A B₀ (hBmeas A hA) (hBmeas B₀ hB₀)
    have hall := ae_all_iff.mpr hsubtype
    filter_upwards [hall] with x hx
    intro s hs
    exact hx ⟨s, hs⟩
  have hmps :=
    conditionalComponentSystem_mps_ae M hM E D hE hD
  have hallsets :
      ∀ᵐ x ∂M.μ, ∀ {s : Set ((M.X × M.X) × (M.X × M.X))},
        MeasurableSet s →
          secondCubeComponentKernel M hM x s =
            conditionalComponentRelativeJoiningTwoMeasure M hM D x s := by
    apply MeasurableSpace.ae_induction_on_inter hSgen.symm hSpi
    · simp [conditionalComponentRelativeJoiningTwoMeasure]
    · exact hbasic
    · filter_upwards [hmps] with x hxMps
      intro s hs heq
      letI : IsProbabilityMeasure (secondCubeComponentKernel M hM x) :=
        inferInstance
      letI : IsProbabilityMeasure
          (conditionalComponentRelativeJoiningTwoMeasure M hM D x) := by
        unfold conditionalComponentRelativeJoiningTwoMeasure
        simp only [dif_pos hxMps]
        exact relativeJoiningMeasure_isProbabilityMeasure _ _
      rw [measure_compl (μ := secondCubeComponentKernel M hM x)
          hs (measure_ne_top _ _),
        measure_compl
          (μ := conditionalComponentRelativeJoiningTwoMeasure M hM D x)
          hs (measure_ne_top _ _), heq,
        measure_univ, measure_univ]
    · filter_upwards [hmps] with x hxMps
      intro f hdisj hfmeas heq
      letI : IsProbabilityMeasure (secondCubeComponentKernel M hM x) :=
        inferInstance
      letI : IsProbabilityMeasure
          (conditionalComponentRelativeJoiningTwoMeasure M hM D x) := by
        unfold conditionalComponentRelativeJoiningTwoMeasure
        simp only [dif_pos hxMps]
        exact relativeJoiningMeasure_isProbabilityMeasure _ _
      rw [measure_iUnion (μ := secondCubeComponentKernel M hM x)
          hdisj hfmeas,
        measure_iUnion
          (μ := conditionalComponentRelativeJoiningTwoMeasure M hM D x)
          hdisj hfmeas]
      congr 1
      funext n
      exact heq n
  filter_upwards [hallsets] with x hx
  intro hxMps
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  apply Measure.ext
  intro s hs
  have hxs := hx hs
  simp only [conditionalComponentRelativeJoiningTwoMeasure, dif_pos hxMps] at hxs
  exact hxs.symm

/-- The global second cube is the bind of the ambient measure with the
explicit second-cube component kernel. -/
theorem relativeCubeSystemTwo_measure_eq_bind_componentKernel
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
        D.measureAt x = D.measureAt y) :
    (relativeCubeSystemTwo M hM).μ =
      M.μ.bind (fun x ↦ secondCubeComponentKernel M hM x) := by
  let hC2 := relativeCubeSystemTwo_mps M hM
  letI : IsProbabilityMeasure (relativeCubeSystemTwo M hM).μ := hC2.1
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.bind_apply (hA.prod hB)]
  · change
      relativeJoiningMeasure
          (relativeJoiningSystem M hM)
          (relativeJoiningSystem_mps M hM) (A ×ˢ B) =
        ∫⁻ x, secondCubeComponentKernel M hM x (A ×ˢ B) ∂M.μ
    rw [relativeCubeSystemTwo_measure_prod_eq_lintegral_components
      M hM E D hE hD hproper hsame A B hA hB]
    apply lintegral_congr_ae
    have hrect :=
      conditionalComponentRelativeJoiningTwoMass_ae_eq_kernelIntegral
        M hM E D hE hD hproper hsame A B hA hB
    filter_upwards [hrect] with x hx
    rw [secondCubeComponentKernel_apply_prod M hM A B hA hB x]
    exact hx
  · exact
      ((secondCubeComponentKernel M hM).measurable.mono
        (invariantMeasurableSpace_le M) le_rfl).aemeasurable

/-- A null set for the global second cube is null for the second cube of
almost every invariant conditional component. -/
theorem relativeCubeSystemTwo_null_ae_component
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
    (s : Set ((M.X × M.X) × (M.X × M.X)))
    (hs : MeasurableSet s)
    (hzero : (relativeCubeSystemTwo M hM).μ s = 0) :
    ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        (@relativeCubeSystemTwo
          (conditionalComponentSystem M hM D x)
          (by
            change @StandardBorelSpace M.X M.measurableSpace
            exact instSB) hxMps).μ s = 0 := by
  have hmeasure :=
    conditionalComponentRelativeJoiningTwoMeasure_ae_eq_kernel
      M hM E D hE hD hproper hsame
  have hglobal :=
    relativeCubeSystemTwo_measure_eq_bind_componentKernel
      M hM E D hE hD hproper hsame
  rw [hglobal] at hzero
  change
    (M.μ.bind (fun x ↦ secondCubeComponentKernel M hM x)) s = 0 at hzero
  rw [Measure.bind_apply hs
      (((secondCubeComponentKernel M hM).measurable.mono
        (invariantMeasurableSpace_le M) le_rfl).aemeasurable)] at hzero
  have hkernel :
      (fun x ↦ secondCubeComponentKernel M hM x s) =ᵐ[M.μ] 0 := by
    rw [lintegral_eq_zero_iff
      (((secondCubeComponentKernel M hM).measurable_coe hs).mono
        (invariantMeasurableSpace_le M) le_rfl)] at hzero
    exact hzero
  filter_upwards [hmeasure, hkernel] with x hxmeasure hxzero
  intro hxMps
  rw [hxmeasure hxMps]
  exact hxzero

/-- Any almost-everywhere statement on the global second cube holds on
the second cube of almost every invariant conditional component.  The
measurable-hull step avoids imposing a measurability hypothesis on the
predicate. -/
theorem relativeCubeSystemTwo_ae_ae_component
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
    (p : ((M.X × M.X) × (M.X × M.X)) → Prop)
    (hp : ∀ᵐ q ∂(relativeCubeSystemTwo M hM).μ, p q) :
    ∀ᵐ x ∂M.μ,
      ∀ hxMps : Chapter01.IsMeasurePreservingSystem
          (conditionalComponentSystem M hM D x),
        ∀ᵐ q ∂(@relativeCubeSystemTwo
          (conditionalComponentSystem M hM D x)
          (by
            change @StandardBorelSpace M.X M.measurableSpace
            exact instSB) hxMps).μ,
          p q := by
  let bad : Set ((M.X × M.X) × (M.X × M.X)) := {q | ¬ p q}
  let s := toMeasurable (relativeCubeSystemTwo M hM).μ bad
  have hbad : (relativeCubeSystemTwo M hM).μ bad = 0 := by
    exact ae_iff.mp hp
  have hs : MeasurableSet s := measurableSet_toMeasurable _ _
  have hszero : (relativeCubeSystemTwo M hM).μ s = 0 := by
    exact (measure_toMeasurable bad).trans hbad
  have hnull :=
    relativeCubeSystemTwo_null_ae_component
      M hM E D hE hD hproper hsame s hs hszero
  filter_upwards [hnull] with x hx
  intro hxMps
  rw [ae_iff]
  apply measure_mono_null _ (hx hxMps)
  intro q hq
  exact subset_toMeasurable _ _ hq

end Chapter02.HostKraCubeDisintegration
