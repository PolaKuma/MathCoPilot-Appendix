import Chapter02.HostKra.HostKraCubeDisintegrationMeasure
import Chapter02.HostKra.HostKraCubeSymmetry

open Classical Filter Set MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegrationSymmetry

universe u

open HostKraStandardRelativeJoining
open HostKraErgodicDecomposition
open HostKraCubeDisintegration
open HostKraCubeSymmetry

/-- The middle-coordinate transposition preserves the second Host--Kra
cube measure for every standard Borel probability-preserving system.

The global second cube is first disintegrated over the ergodic components
of the base system.  On almost every component this is the already checked
ergodic square-transposition theorem. -/
theorem squareTranspose_measurePreserving
    (M : System.{u}) [instSB : StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (HostKraCubeSymmetry.squareTranspose :
        (M.X × M.X) × (M.X × M.X) →
          (M.X × M.X) × (M.X × M.X))
      (relativeCubeSystemTwo M hM).μ
      (relativeCubeSystemTwo M hM).μ := by
  obtain ⟨E, D, hE, hD, hproper, hsame⟩ :=
    invariantCoreConditionalMeasure_exists M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  letI : IsProbabilityMeasure (relativeCubeSystemTwo M hM).μ := hC2.1
  refine ⟨HostKraCubeSymmetry.squareTranspose_measurable, ?_⟩
  apply Measure.ext_fourfold
  intro A00 A01 A10 A11 hA00 hA01 hA10 hA11
  rw [Measure.map_apply HostKraCubeSymmetry.squareTranspose_measurable
    ((hA00.prod hA01).prod (hA10.prod hA11))]
  have hpre :
      HostKraCubeSymmetry.squareTranspose ⁻¹'
          ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)) =
        (A00 ×ˢ A10) ×ˢ (A01 ×ˢ A11) := by
    ext q
    simp only [HostKraCubeSymmetry.squareTranspose, Set.mem_preimage,
      Set.mem_prod]
    tauto
  rw [hpre]
  change
    relativeJoiningMeasure
        (relativeJoiningSystem M hM)
        (relativeJoiningSystem_mps M hM)
        ((A00 ×ˢ A10) ×ˢ (A01 ×ˢ A11)) =
      relativeJoiningMeasure
        (relativeJoiningSystem M hM)
        (relativeJoiningSystem_mps M hM)
        ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11))
  rw [
    relativeCubeSystemTwo_measure_prod_eq_lintegral_components
      M hM E D hE hD hproper hsame
      (A00 ×ˢ A10) (A01 ×ˢ A11)
      (hA00.prod hA10) (hA01.prod hA11),
    relativeCubeSystemTwo_measure_prod_eq_lintegral_components
      M hM E D hE hD hproper hsame
      (A00 ×ˢ A01) (A10 ×ˢ A11)
      (hA00.prod hA01) (hA10.prod hA11)]
  apply lintegral_congr_ae
  filter_upwards [
    conditionalComponentSystem_mps_ae M hM E D hE hD,
    conditionalComponent_isErgodic_ae
      M hM E D hE hD hproper hsame] with x hxMps hxErg
  simp only [conditionalComponentRelativeJoiningTwoMass, dif_pos hxMps]
  let C := conditionalComponentSystem M hM D x
  letI : StandardBorelSpace C.X := by
    change @StandardBorelSpace M.X M.measurableSpace
    exact instSB
  let hσ :=
    HostKraCubeSymmetry.squareTranspose_measurePreserving C hxMps hxErg
  have hbox :
      MeasurableSet ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)) :=
    (hA00.prod hA01).prod (hA10.prod hA11)
  have hμ := hσ.measure_preimage hbox.nullMeasurableSet
  have hpreC :
      (HostKraCubeSymmetry.squareTranspose :
          (C.X × C.X) × (C.X × C.X) →
            (C.X × C.X) × (C.X × C.X)) ⁻¹'
          ((A00 ×ˢ A01) ×ˢ (A10 ×ˢ A11)) =
        (A00 ×ˢ A10) ×ˢ (A01 ×ˢ A11) := by
    ext q
    simp only [HostKraCubeSymmetry.squareTranspose, Set.mem_preimage,
      Set.mem_prod]
    tauto
  rw [hpreC] at hμ
  exact hμ

/-- The outer and middle cube directions may be exchanged in the third
Host--Kra cube of every standard Borel probability-preserving system. -/
theorem cubeThreeOuterMiddleTranspose_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose :
        (relativeCubeSystemThree M hM).X →
          (relativeCubeSystemThree M hM).X)
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  apply
    HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose_measurePreserving_of_cubeOne_squareTranspose
      M hM
  exact squareTranspose_measurePreserving
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)

/-- Applying the second-cube transposition on both outer faces exchanges
the middle and inner directions of the third cube. -/
theorem cubeThreeMiddleTranspose_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (HostKraCubeSymmetry.cubeThreeMiddleTranspose :
        (relativeCubeSystemThree M hM).X →
          (relativeCubeSystemThree M hM).X)
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  apply HostKraCubeSymmetry.relativeJoining_diagonal_measurePreserving
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    HostKraCubeSymmetry.squareTranspose
    (squareTranspose_measurePreserving M hM)
    HostKraCubeSymmetry.squareTranspose_involutive
  intro q
  rfl

/-- Exchange the outer and inner directions of an eight-vertex cube. -/
def cubeThreeOuterInnerTranspose {X : Type u} :
    ((X × X) × (X × X)) × ((X × X) × (X × X)) →
      ((X × X) × (X × X)) × ((X × X) × (X × X)) :=
  fun r ↦
    (((r.1.1.1, r.2.1.1), (r.1.2.1, r.2.2.1)),
      ((r.1.1.2, r.2.1.2), (r.1.2.2, r.2.2.2)))

theorem cubeThreeOuterInnerTranspose_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (cubeThreeOuterInnerTranspose :
        (relativeCubeSystemThree M hM).X →
          (relativeCubeSystemThree M hM).X)
      (relativeCubeSystemThree M hM).μ
      (relativeCubeSystemThree M hM).μ := by
  have hOM := cubeThreeOuterMiddleTranspose_measurePreserving M hM
  have hMI := cubeThreeMiddleTranspose_measurePreserving M hM
  have hcomp := hOM.comp (hMI.comp hOM)
  simpa only [Function.comp_apply, cubeThreeOuterInnerTranspose,
    HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose,
    HostKraCubeSymmetry.cubeThreeMiddleTranspose] using hcomp

end Chapter02.HostKraCubeDisintegrationSymmetry
