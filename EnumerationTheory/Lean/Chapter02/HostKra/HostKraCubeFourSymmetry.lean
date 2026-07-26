import Chapter02.HostKra.HostKraDualFunctionFour

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeFourSymmetry

universe u

open HostKraStandardRelativeJoining

/-- Swap the two deepest directions simultaneously on both outer faces of
a four-dimensional cube. -/
def cubeFourInnerTranspose {X : Type u} :
    ((((X × X) × (X × X)) × ((X × X) × (X × X))) ×
      (((X × X) × (X × X)) × ((X × X) × (X × X)))) →
    ((((X × X) × (X × X)) × ((X × X) × (X × X))) ×
      (((X × X) × (X × X)) × ((X × X) × (X × X)))) :=
  fun r ↦
    (HostKraCubeSymmetry.cubeThreeMiddleTranspose r.1,
      HostKraCubeSymmetry.cubeThreeMiddleTranspose r.2)

lemma cubeFourInnerTranspose_involutive {X : Type u} :
    Function.Involutive (cubeFourInnerTranspose (X := X)) := by
  intro r
  simp only [cubeFourInnerTranspose,
    HostKraCubeSymmetry.cubeThreeMiddleTranspose,
    HostKraCubeSymmetry.squareTranspose]

lemma cubeFourInnerTranspose_commutes
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (r : (relativeCubeSystemThree M hM).X ×
      (relativeCubeSystemThree M hM).X) :
    cubeFourInnerTranspose
        ((relativeJoiningTransform
          (relativeCubeSystemThree M hM)) r) =
      relativeJoiningTransform
        (relativeCubeSystemThree M hM)
        (cubeFourInnerTranspose r) := by
  rfl

/-- Exchange the outermost and deepest directions of a four-dimensional
cube, leaving the two middle directions fixed. -/
def cubeFourOuterInnerTranspose {X : Type u} :
    ((((X × X) × (X × X)) × ((X × X) × (X × X))) ×
      (((X × X) × (X × X)) × ((X × X) × (X × X)))) →
    ((((X × X) × (X × X)) × ((X × X) × (X × X))) ×
      (((X × X) × (X × X)) × ((X × X) × (X × X)))) :=
  fun r ↦
    ((((r.1.1.1.1, r.2.1.1.1), (r.1.1.2.1, r.2.1.2.1)),
        ((r.1.2.1.1, r.2.2.1.1), (r.1.2.2.1, r.2.2.2.1))),
      (((r.1.1.1.2, r.2.1.1.2), (r.1.1.2.2, r.2.1.2.2)),
        ((r.1.2.1.2, r.2.2.1.2), (r.1.2.2.2, r.2.2.2.2))))

theorem cubeFourInnerTranspose_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (cubeFourInnerTranspose :
        ((relativeCubeSystemThree M hM).X ×
          (relativeCubeSystemThree M hM).X) →
        ((relativeCubeSystemThree M hM).X ×
          (relativeCubeSystemThree M hM).X))
      (relativeJoiningMeasure
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM))
      (relativeJoiningMeasure
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM)) := by
  apply HostKraCubeSymmetry.relativeJoining_diagonal_measurePreserving
    (relativeCubeSystemThree M hM)
    (relativeCubeSystemThree_mps M hM)
    HostKraCubeSymmetry.cubeThreeMiddleTranspose
    (HostKraCubeDisintegrationSymmetry.cubeThreeMiddleTranspose_measurePreserving
      M hM)
    (by
      intro r
      rcases r with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      rfl)
  intro r
  rfl

theorem cubeFourOuterInnerTranspose_measurePreserving
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    MeasurePreserving
      (cubeFourOuterInnerTranspose :
        ((relativeCubeSystemThree M hM).X ×
          (relativeCubeSystemThree M hM).X) →
        ((relativeCubeSystemThree M hM).X ×
          (relativeCubeSystemThree M hM).X))
      (relativeJoiningMeasure
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM))
      (relativeJoiningMeasure
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM)) := by
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  have h12 :=
    HostKraCubeDisintegrationSymmetry.cubeThreeOuterMiddleTranspose_measurePreserving
      C1 hC1
  have h23 :=
    HostKraCubeDisintegrationSymmetry.cubeThreeMiddleTranspose_measurePreserving
      C1 hC1
  have h34 := cubeFourInnerTranspose_measurePreserving M hM
  have hcomp := h12.comp (h23.comp (h34.comp (h23.comp h12)))
  simpa only [Function.comp_apply,
    cubeFourOuterInnerTranspose, cubeFourInnerTranspose,
    HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose,
    HostKraCubeSymmetry.cubeThreeMiddleTranspose,
    HostKraCubeSymmetry.squareTranspose] using hcomp

end Chapter02.HostKraCubeFourSymmetry
