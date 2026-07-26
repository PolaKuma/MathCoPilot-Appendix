import Chapter02.HostKra.HostKraU4Nullspace
import Chapter02.HostKra.HostKraErgodicRelativeJoining
import Chapter02.Recurrence.MultipleKhintchineCartesian

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraU4CartesianComponent

universe u

open HostKraCubeSeminorm

/-- The first Host--Kra cube lift is pointwise the tensor-conjugate square
used in the Cartesian mean-square identity. -/
lemma cubeLiftOne_eq_cartesianSquare
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    HostKraCubeSeminorm.cubeLiftOne M hM f =
      MultipleKhintchineCartesian.cartesianSquare f := by
  rfl

/-- On an ergodic base system, a `U⁴`-null function has a `U³`-null
tensor-conjugate square on the first relative cube. Together with
`relativeCubeSystemOne_eq_productSystem_of_ergodic`, this records the global
(before ergodic disintegration) part of the BHK order drop without a
dependent rewrite of the whole system structure. -/
theorem cartesianSquare_hasZeroHostKraU3_on_relativeCube_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM f hf) :
    HasZeroHostKraU3
      (HostKraStandardRelativeJoining.relativeCubeSystemOne M hM)
      (HostKraStandardRelativeJoining.relativeCubeSystemOne_mps M hM)
      (MultipleKhintchineCartesian.cartesianSquare f)
      (by
        simpa only [← cubeLiftOne_eq_cartesianSquare M hM f] using
          HostKraCubeSeminorm.cubeLiftOne_memLp_top M hM f hf) := by
  have _hsystem :=
    Chapter02.HostKraErgodicRelativeJoining.relativeCubeSystemOne_eq_productSystem_of_ergodic
      M hM hErg
  simpa only [← cubeLiftOne_eq_cartesianSquare M hM f] using
    (Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_iff_cubeLiftOne_hasZeroHostKraU3
      M hM f hf).1 hzero

end Chapter02.HostKraU4CartesianComponent
