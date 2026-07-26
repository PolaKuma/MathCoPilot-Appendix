import Chapter02.HostKra.HostKraGowersCauchySchwarz
import Chapter02.HostKra.HostKraU4Nullspace

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraU4GowersRecursion

universe u

open HostKraCubeSeminorm
open HostKraDualFunction
open HostKraStandardRelativeJoining

/-- An order-four-null base function supplies an order-three-null test
vector on the first relative cube.  Hence every seven-vertex dual function
on that cube is orthogonal to its canonical first cube lift. -/
theorem inner_cubeLiftOne_sevenVertexDualFunction_eq_zero_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM f hf)
    (F001 F010 F011 F100 F101 F110 F111 :
      Lp ℂ 2 (relativeCubeSystemOne M hM).μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤
      (relativeCubeSystemOne M hM).μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤
      (relativeCubeSystemOne M hM).μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤
      (relativeCubeSystemOne M hM).μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤
      (relativeCubeSystemOne M hM).μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤
      (relativeCubeSystemOne M hM).μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤
      (relativeCubeSystemOne M hM).μ) :
    let H :=
      (cubeLiftOne_memLp_two M hM f hf).toLp
        (cubeLiftOne M hM f)
    @inner ℂ (Lp ℂ 2 (relativeCubeSystemOne M hM).μ) _ H
        (sevenVertexDualFunction
          (relativeCubeSystemOne M hM)
          (relativeCubeSystemOne_mps M hM)
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top) = 0 := by
  dsimp only
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  let hLiftTop := cubeLiftOne_memLp_top M hM f hf
  let hLiftTwo := cubeLiftOne_memLp_two M hM f hf
  let H := hLiftTwo.toLp (cubeLiftOne M hM f)
  have hHcoe :
      (fun x ↦ H x) =ᵐ[C1.μ] cubeLiftOne M hM f :=
    hLiftTwo.coeFn_toLp
  have hHtop : MemLp (fun x ↦ H x) ⊤ C1.μ :=
    (memLp_congr_ae hHcoe).mpr hLiftTop
  have hrawZero :
      HasZeroHostKraU3 C1 hC1
        (cubeLiftOne M hM f) hLiftTop :=
    (Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_iff_cubeLiftOne_hasZeroHostKraU3
        M hM f hf).1 hzero
  have hHZero : HasZeroHostKraU3 C1 hC1 (fun x ↦ H x) hHtop :=
    Chapter02.HostKraU3Nullspace.hasZeroHostKraU3_congr
      C1 hC1 (cubeLiftOne M hM f) (fun x ↦ H x)
      hLiftTop hHtop hHcoe.symm hrawZero
  exact
    Chapter02.HostKraGowersCauchySchwarz.inner_sevenVertexDualFunction_eq_zero_of_hasZeroHostKraU3
        C1 hC1 F001 F010 F011 F100 F101 F110 F111 H
        hF001top hF010top hF011top
        hF100top hF101top hF110top hHtop hHZero

end Chapter02.HostKraU4GowersRecursion
