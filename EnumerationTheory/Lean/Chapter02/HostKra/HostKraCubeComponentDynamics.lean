import Chapter02.HostKra.HostKraInvariantMeanSubsequenceZero

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraCubeDisintegration

universe u

open HostKraStandardRelativeJoining
open HostKraCubeSeminorm

/-- The coordinatewise transformation underlying every second relative
cube; it depends only on the original transformation. -/
def relativeCubeTransformTwo {X : Type u} (T : X → X) :
    ((X × X) × (X × X)) → ((X × X) × (X × X)) :=
  fun q ↦
    ((T q.1.1, T q.1.2), (T q.2.1, T q.2.2))

/-- The second relative cube transformation has the explicit
coordinatewise form and therefore contains no measure data. -/
lemma relativeCubeSystemTwo_transform_eq_explicit
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    (relativeCubeSystemTwo M hM).T =
      relativeCubeTransformTwo M.T := by
  rfl

/-- The second cube lift is the twice-iterated algebraic cube operation
and therefore contains no measure data. -/
lemma cubeLiftTwo_eq_explicit
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftTwo M hM f = cubeLift (cubeLift f) := by
  rfl

end Chapter02.HostKraCubeDisintegration
