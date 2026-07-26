import Chapter02.HostKra.HostKraU4CartesianComponent
import Chapter02.HostKra.HostKraU3Component

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraU4CartesianProduct

universe u

open HostKraCubeSeminorm
open Chapter02.HostKraCubeDisintegration

/-- Transport `U³`-nullity across equality of bundled systems.  The
measure-preserving and boundedness witnesses are propositions, so after
equality elimination their particular proofs are immaterial. -/
theorem hasZeroHostKraU3_congr_system
    (R P : System.{u})
    [StandardBorelSpace R.X] [StandardBorelSpace P.X]
    (hR : Chapter01.IsMeasurePreservingSystem R)
    (hP : Chapter01.IsMeasurePreservingSystem P)
    (gR : R.X → ℂ) (gP : P.X → ℂ)
    (hgR : MemLp gR ⊤ R.μ) (hgP : MemLp gP ⊤ P.μ)
    (hsystem : R = P) (hg : HEq gR gP)
    (hzero : HasZeroHostKraU3 R hR gR hgR) :
    HasZeroHostKraU3 P hP gP hgP := by
  subst P
  have hfun : gR = gP := eq_of_heq hg
  subst gP
  exact hzero

set_option maxHeartbeats 600000 in
/-- On an ergodic base system, the tensor-conjugate square of a bounded
`U⁴`-null function is `U³`-null on the ordinary Cartesian product system. -/
theorem cartesianSquare_hasZeroHostKraU3_on_product_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM f hf) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let hsq : MemLp
        (MultipleKhintchineCartesian.cartesianSquare f) ⊤ P.μ := by
      letI : IsProbabilityMeasure M.μ := hM.1
      simpa only [P, MultipleKhintchineCartesian.productSystem,
        MultipleKhintchineCartesian.cartesianSquare] using
        (hf.star.comp_snd M.μ).mul (r := ⊤) (hf.comp_fst M.μ)
    @HasZeroHostKraU3 P
      (by
        dsimp only [P, MultipleKhintchineCartesian.productSystem]
        infer_instance)
      hP
      (MultipleKhintchineCartesian.cartesianSquare f) hsq := by
  dsimp only
  letI : StandardBorelSpace
      (MultipleKhintchineCartesian.productSystem M M).X := by
    dsimp only [MultipleKhintchineCartesian.productSystem]
    infer_instance
  apply hasZeroHostKraU3_congr_system
    (HostKraStandardRelativeJoining.relativeCubeSystemOne M hM)
    (MultipleKhintchineCartesian.productSystem M M)
    (HostKraStandardRelativeJoining.relativeCubeSystemOne_mps M hM)
    (MultipleKhintchineCartesian.productSystem_mps M M hM hM)
    (MultipleKhintchineCartesian.cartesianSquare f)
    (MultipleKhintchineCartesian.cartesianSquare f)
  · exact
      Chapter02.HostKraErgodicRelativeJoining.relativeCubeSystemOne_eq_productSystem_of_ergodic
        M hM hErg
  · rfl
  · exact
      HostKraU4CartesianComponent.cartesianSquare_hasZeroHostKraU3_on_relativeCube_of_hasZeroHostKraU4
        M hM hErg f hf hzero

end Chapter02.HostKraU4CartesianProduct
