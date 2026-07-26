import Chapter02.HostKra.HostKraCubeFourSymmetry

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraGowersCauchySchwarzFour

universe u

open HostKraStandardRelativeJoining
open HostKraDualFunction
open HostKraRelativeJoiningComplex
open HostKraDualFunctionFour

/-- The intrinsic alternating edge representative of a `U⁴`-null vector
is `U³`-null on the first relative cube. -/
theorem alternatingEdgeProduct_hasZeroHostKraU3_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero :
      HostKraCubeSeminorm.HasZeroHostKraU4 M hM
        (fun x ↦ H x) hHtop) :
    HostKraCubeSeminorm.HasZeroHostKraU3
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (fun p ↦ alternatingEdgeProduct M hM H hHtop p)
      (alternatingEdgeProduct_memLp_top M hM H hHtop) := by
  have hraw :
      HostKraCubeSeminorm.HasZeroHostKraU3
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)
        (HostKraCubeSeminorm.cubeLiftOne M hM (fun x ↦ H x))
        (HostKraCubeSeminorm.cubeLiftOne_memLp_top
          M hM (fun x ↦ H x) hHtop) :=
    (Chapter02.HostKraU4Nullspace.hasZeroHostKraU4_iff_cubeLiftOne_hasZeroHostKraU3
        M hM (fun x ↦ H x) hHtop).1 hzero
  apply Chapter02.HostKraU3Nullspace.hasZeroHostKraU3_congr
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (HostKraCubeSeminorm.cubeLiftOne M hM (fun x ↦ H x))
    (fun p ↦ alternatingEdgeProduct M hM H hHtop p)
    (HostKraCubeSeminorm.cubeLiftOne_memLp_top
      M hM (fun x ↦ H x) hHtop)
    (alternatingEdgeProduct_memLp_top M hM H hHtop)
    _ hraw
  simpa [HostKraCubeSeminorm.cubeLiftOne,
    HostKraCubeSeminorm.cubeLift] using
      (alternatingEdgeProduct_coe M hM H hHtop).symm

/-- The new order-four Cauchy--Schwarz rotation.  Swapping the outermost
and deepest directions turns the doubled seven-vertex first face into the
order-three mixed pairing on the first relative cube, with every input
replaced by its alternating edge lift. -/
theorem inner_mixedSevenFaceCopies_eq_cubeLiftOne_sevenVertexPairing
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0001 F0010 F0011 F0100 F0101 F0110 F0111 H :
      Lp ℂ 2 M.μ)
    (hF0001top : MemLp (fun x ↦ F0001 x) ⊤ M.μ)
    (hF0010top : MemLp (fun x ↦ F0010 x) ⊤ M.μ)
    (hF0011top : MemLp (fun x ↦ F0011 x) ⊤ M.μ)
    (hF0100top : MemLp (fun x ↦ F0100 x) ⊤ M.μ)
    (hF0101top : MemLp (fun x ↦ F0101 x) ⊤ M.μ)
    (hF0110top : MemLp (fun x ↦ F0110 x) ⊤ M.μ)
    (hF0111top : MemLp (fun x ↦ F0111 x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ) :
    let C3 := relativeCubeSystemThree M hM
    let hC3 := relativeCubeSystemThree_mps M hM
    let A := sevenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top
    let hAtop := sevenVertexCubeProduct_memLp_top M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top
    let H0 := baseVertexPullbackThree M hM H
    let K := mixedFaceWithBase C3 A H0 hAtop
    let C1 := relativeCubeSystemOne M hM
    let hC1 := relativeCubeSystemOne_mps M hM
    let E0001 := alternatingEdgeProduct M hM F0001 hF0001top
    let E0010 := alternatingEdgeProduct M hM F0010 hF0010top
    let E0011 := alternatingEdgeProduct M hM F0011 hF0011top
    let E0100 := alternatingEdgeProduct M hM F0100 hF0100top
    let E0101 := alternatingEdgeProduct M hM F0101 hF0101top
    let E0110 := alternatingEdgeProduct M hM F0110 hF0110top
    let E0111 := alternatingEdgeProduct M hM F0111 hF0111top
    let EH := alternatingEdgeProduct M hM H hHtop
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure C3 hC3)) _
        (relativeSndCLM C3 hC3 K)
        (relativeFstCLM C3 hC3 K) =
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree C1 hC1).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo C1 hC1)
          (relativeCubeSystemTwo_mps C1 hC1)
          (baseVertexPullbackTwo C1 hC1 EH))
        (sevenVertexCubeProduct C1 hC1
          E0010 E0100 E0110 E0001 E0011 E0101 E0111
          (alternatingEdgeProduct_memLp_top M hM F0010 hF0010top)
          (alternatingEdgeProduct_memLp_top M hM F0100 hF0100top)
          (alternatingEdgeProduct_memLp_top M hM F0110 hF0110top)
          (alternatingEdgeProduct_memLp_top M hM F0001 hF0001top)
          (alternatingEdgeProduct_memLp_top M hM F0011 hF0011top)
          (alternatingEdgeProduct_memLp_top M hM F0101 hF0101top)) := by
  dsimp only
  let C3 := relativeCubeSystemThree M hM
  let hC3 := relativeCubeSystemThree_mps M hM
  let A := sevenVertexCubeProduct M hM
    F0001 F0010 F0011 F0100 F0101 F0110 F0111
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top
  let hAtop := sevenVertexCubeProduct_memLp_top M hM
    F0001 F0010 F0011 F0100 F0101 F0110 F0111
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top hF0111top
  let H0 := baseVertexPullbackThree M hM H
  let K := mixedFaceWithBase C3 A H0 hAtop
  let L := relativeSndCLM C3 hC3 K
  let R := relativeFstCLM C3 hC3 K
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  let E0001 := alternatingEdgeProduct M hM F0001 hF0001top
  let E0010 := alternatingEdgeProduct M hM F0010 hF0010top
  let E0011 := alternatingEdgeProduct M hM F0011 hF0011top
  let E0100 := alternatingEdgeProduct M hM F0100 hF0100top
  let E0101 := alternatingEdgeProduct M hM F0101 hF0101top
  let E0110 := alternatingEdgeProduct M hM F0110 hF0110top
  let E0111 := alternatingEdgeProduct M hM F0111 hF0111top
  let EH := alternatingEdgeProduct M hM H hHtop
  let HP := baseVertexPullbackTwo C1 hC1 EH
  let W := sevenVertexCubeProduct C1 hC1
    E0010 E0100 E0110 E0001 E0011 E0101 E0111
    (alternatingEdgeProduct_memLp_top M hM F0010 hF0010top)
    (alternatingEdgeProduct_memLp_top M hM F0100 hF0100top)
    (alternatingEdgeProduct_memLp_top M hM F0110 hF0110top)
    (alternatingEdgeProduct_memLp_top M hM F0001 hF0001top)
    (alternatingEdgeProduct_memLp_top M hM F0011 hF0011top)
    (alternatingEdgeProduct_memLp_top M hM F0101 hF0101top)
  let LP := relativeFstCLM
    (relativeCubeSystemTwo C1 hC1)
    (relativeCubeSystemTwo_mps C1 hC1) HP
  have hmeas :
      AEStronglyMeasurable
        (fun r ↦ @inner ℂ ℂ _ (L r) (R r))
        (relativeJoiningMeasure C3 hC3) :=
    (L2.integrable_inner (𝕜 := ℂ) L R).aestronglyMeasurable
  have hinv :=
    HilbertSchmidtInvariant.integral_comp_measurePreserving
      HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose
      (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose_measurePreserving
        M hM)
      (fun r ↦ @inner ℂ ℂ _ (L r) (R r)) hmeas
  have hinv' :
      (∫ r, @inner ℂ ℂ _ (L r) (R r)
          ∂(relativeJoiningMeasure C3 hC3)) =
        ∫ r, @inner ℂ ℂ _
          (L (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r))
          (R (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r))
          ∂(relativeJoiningMeasure C3 hC3) :=
    hinv.symm
  rw [L2.inner_def, L2.inner_def]
  change
    (∫ r, @inner ℂ ℂ _ (L r) (R r)
      ∂(relativeJoiningMeasure C3 hC3)) =
      ∫ r, @inner ℂ ℂ _ (LP r) (W r)
        ∂(relativeJoiningMeasure C3 hC3)
  rw [hinv']
  apply integral_congr_ae
  have hL := relativeSndCLM_coe C3 hC3 K
  have hR := relativeFstCLM_coe C3 hC3 K
  have hK := mixedFaceWithBase_coe C3 A H0 hAtop
  have hA := sevenVertexCubeProduct_coe M hM
    F0001 F0010 F0011 F0100 F0101 F0110 F0111
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top
  have hH0 := baseVertexPullbackThree_coe M hM H
  have hfst :=
    HostKraCubeFactors.relativeJoining_fst_measurePreserving C3 hC3
  have hsnd :=
    HostKraCubeFactors.relativeJoining_snd_measurePreserving C3 hC3
  have hKfst := hfst.quasiMeasurePreserving.ae_eq hK
  have hKsnd := hsnd.quasiMeasurePreserving.ae_eq hK
  have hAfst := hfst.quasiMeasurePreserving.ae_eq hA
  have hAsnd := hsnd.quasiMeasurePreserving.ae_eq hA
  have hHfst := hfst.quasiMeasurePreserving.ae_eq hH0
  have hHsnd := hsnd.quasiMeasurePreserving.ae_eq hH0
  have hσ :=
    (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose_measurePreserving
      M hM).quasiMeasurePreserving
  have hLσ := hσ.ae_eq hL
  have hRσ := hσ.ae_eq hR
  have hKfstσ := hσ.ae_eq hKfst
  have hKsndσ := hσ.ae_eq hKsnd
  have hAfstσ := hσ.ae_eq hAfst
  have hAsndσ := hσ.ae_eq hAsnd
  have hHfstσ := hσ.ae_eq hHfst
  have hHsndσ := hσ.ae_eq hHsnd
  have hLP := relativeFstCLM_coe
    (relativeCubeSystemTwo C1 hC1)
    (relativeCubeSystemTwo_mps C1 hC1) HP
  have hHP :=
    Chapter02.HostKraGowersCauchySchwarz.baseVertexPullbackTwo_coe
      C1 hC1 EH
  have hHPfst :=
    hfst.quasiMeasurePreserving.ae_eq hHP
  have hW := sevenVertexCubeProduct_coe C1 hC1
    E0010 E0100 E0110 E0001 E0011 E0101 E0111
    (alternatingEdgeProduct_memLp_top M hM F0010 hF0010top)
    (alternatingEdgeProduct_memLp_top M hM F0100 hF0100top)
    (alternatingEdgeProduct_memLp_top M hM F0110 hF0110top)
    (alternatingEdgeProduct_memLp_top M hM F0001 hF0001top)
    (alternatingEdgeProduct_memLp_top M hM F0011 hF0011top)
    (alternatingEdgeProduct_memLp_top M hM F0101 hF0101top)
  let C2' := relativeCubeSystemOne C1 hC1
  let hC2' := relativeCubeSystemOne_mps C1 hC1
  let C3' := relativeCubeSystemTwo C1 hC1
  let hC3' := relativeCubeSystemTwo_mps C1 hC1
  have hE0010 := alternatingEdgeProduct_coe M hM F0010 hF0010top
  have hE0100 := alternatingEdgeProduct_coe M hM F0100 hF0100top
  have hE0110 := alternatingEdgeProduct_coe M hM F0110 hF0110top
  have hE0001 := alternatingEdgeProduct_coe M hM F0001 hF0001top
  have hE0011 := alternatingEdgeProduct_coe M hM F0011 hF0011top
  have hE0101 := alternatingEdgeProduct_coe M hM F0101 hF0101top
  have hE0111 := alternatingEdgeProduct_coe M hM F0111 hF0111top
  have hEH := alternatingEdgeProduct_coe M hM H hHtop
  have hE0010_1 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hE0010
  have hE0010_2 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hE0010_1
  have hE0010_001 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hE0010_2
  have hE0100_1 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hE0100
  have hE0100_2 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hE0100_1
  have hE0100_010 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hE0100_2
  have hE0110_1 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hE0110
  have hE0110_2 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hE0110_1
  have hE0110_011 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hE0110_2
  have hE0001_1 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hE0001
  have hE0001_2 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hE0001_1
  have hE0001_100 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hE0001_2
  have hE0011_1 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hE0011
  have hE0011_2 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hE0011_1
  have hE0011_101 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hE0011_2
  have hE0101_1 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hE0101
  have hE0101_2 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hE0101_1
  have hE0101_110 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hE0101_2
  have hE0111_1 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hE0111
  have hE0111_2 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hE0111_1
  have hE0111_111 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hE0111_2
  have hEH_1 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq hEH
  have hEH_2 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2' hC2')
      |>.quasiMeasurePreserving.ae_eq hEH_1
  have hEH_000 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C3' hC3')
      |>.quasiMeasurePreserving.ae_eq hEH_2
  filter_upwards [hLσ, hRσ, hKfstσ, hKsndσ,
      hAfstσ, hAsndσ, hHfstσ, hHsndσ,
      hLP, hHPfst, hW,
      hE0010_001, hE0100_010, hE0110_011,
      hE0001_100, hE0011_101, hE0101_110, hE0111_111,
      hEH_000] with
      r hrL hrR hrKfst hrKsnd
        hrAfst hrAsnd hrHfst hrHsnd
        hrLP hrHP hrW
        hrE0010 hrE0100 hrE0110
        hrE0001 hrE0011 hrE0101 hrE0111 hrEH
  simp only [Function.comp_apply] at hrL hrR hrKfst hrKsnd hrAfst hrAsnd hrHfst hrHsnd
  change L (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r) =
    K (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r).2 at hrL
  change R (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r) =
    K (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r).1 at hrR
  change K (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r).1 =
    _ at hrKfst
  change K (HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose r).2 =
    _ at hrKsnd
  change LP r = HP r.1 at hrLP
  change HP r.1 = EH r.1.1.1 at hrHP
  rw [hrL, hrR, hrKfst, hrKsnd,
    hrAfst, hrAsnd, hrHfst, hrHsnd,
    hrLP, hrHP, hrW]
  simp only [HostKraCubeFourSymmetry.cubeFourOuterInnerTranspose,
    RCLike.inner_apply, starRingEnd_apply, star_mul, star_star]
  simp only [Function.comp_apply] at hrE0010 hrE0100 hrE0110 hrE0001 hrE0011 hrE0101 hrE0111 hrEH
  rw [hrE0010, hrE0100, hrE0110,
    hrE0001, hrE0011, hrE0101, hrE0111, hrEH]
  simp only [star_mul, star_star]
  ring

/-- The doubled mixed first face vanishes whenever the base test vector is
`U⁴`-null. -/
theorem inner_mixedSevenFaceCopies_eq_zero_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0001 F0010 F0011 F0100 F0101 F0110 F0111 H :
      Lp ℂ 2 M.μ)
    (hF0001top : MemLp (fun x ↦ F0001 x) ⊤ M.μ)
    (hF0010top : MemLp (fun x ↦ F0010 x) ⊤ M.μ)
    (hF0011top : MemLp (fun x ↦ F0011 x) ⊤ M.μ)
    (hF0100top : MemLp (fun x ↦ F0100 x) ⊤ M.μ)
    (hF0101top : MemLp (fun x ↦ F0101 x) ⊤ M.μ)
    (hF0110top : MemLp (fun x ↦ F0110 x) ⊤ M.μ)
    (hF0111top : MemLp (fun x ↦ F0111 x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero :
      HostKraCubeSeminorm.HasZeroHostKraU4 M hM
        (fun x ↦ H x) hHtop) :
    let C3 := relativeCubeSystemThree M hM
    let hC3 := relativeCubeSystemThree_mps M hM
    let A := sevenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top
    let hAtop := sevenVertexCubeProduct_memLp_top M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top
    let H0 := baseVertexPullbackThree M hM H
    let K := mixedFaceWithBase C3 A H0 hAtop
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure C3 hC3)) _
        (relativeSndCLM C3 hC3 K)
        (relativeFstCLM C3 hC3 K) = 0 := by
  dsimp only
  rw [inner_mixedSevenFaceCopies_eq_cubeLiftOne_sevenVertexPairing
    M hM F0001 F0010 F0011 F0100 F0101 F0110 F0111 H
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top hF0111top hHtop]
  exact
    Chapter02.HostKraGowersCauchySchwarz.inner_sevenVertexCubeProduct_eq_zero_of_hasZeroHostKraU3
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)
        (alternatingEdgeProduct M hM F0010 hF0010top)
        (alternatingEdgeProduct M hM F0100 hF0100top)
        (alternatingEdgeProduct M hM F0110 hF0110top)
        (alternatingEdgeProduct M hM F0001 hF0001top)
        (alternatingEdgeProduct M hM F0011 hF0011top)
        (alternatingEdgeProduct M hM F0101 hF0101top)
        (alternatingEdgeProduct M hM F0111 hF0111top)
        (alternatingEdgeProduct M hM H hHtop)
        (alternatingEdgeProduct_memLp_top M hM F0010 hF0010top)
        (alternatingEdgeProduct_memLp_top M hM F0100 hF0100top)
        (alternatingEdgeProduct_memLp_top M hM F0110 hF0110top)
        (alternatingEdgeProduct_memLp_top M hM F0001 hF0001top)
        (alternatingEdgeProduct_memLp_top M hM F0011 hF0011top)
        (alternatingEdgeProduct_memLp_top M hM F0101 hF0101top)
        (alternatingEdgeProduct_memLp_top M hM H hHtop)
        (alternatingEdgeProduct_hasZeroHostKraU3_of_hasZeroHostKraU4
          M hM H hHtop hzero)

/-- Every fifteen-vertex dual function is orthogonal to every bounded
`U⁴`-null test vector. -/
theorem inner_fifteenVertexDualFunction_eq_zero_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 H :
      Lp ℂ 2 M.μ)
    (hF0001top : MemLp (fun x ↦ F0001 x) ⊤ M.μ)
    (hF0010top : MemLp (fun x ↦ F0010 x) ⊤ M.μ)
    (hF0011top : MemLp (fun x ↦ F0011 x) ⊤ M.μ)
    (hF0100top : MemLp (fun x ↦ F0100 x) ⊤ M.μ)
    (hF0101top : MemLp (fun x ↦ F0101 x) ⊤ M.μ)
    (hF0110top : MemLp (fun x ↦ F0110 x) ⊤ M.μ)
    (hF0111top : MemLp (fun x ↦ F0111 x) ⊤ M.μ)
    (hF1000top : MemLp (fun x ↦ F1000 x) ⊤ M.μ)
    (hF1001top : MemLp (fun x ↦ F1001 x) ⊤ M.μ)
    (hF1010top : MemLp (fun x ↦ F1010 x) ⊤ M.μ)
    (hF1011top : MemLp (fun x ↦ F1011 x) ⊤ M.μ)
    (hF1100top : MemLp (fun x ↦ F1100 x) ⊤ M.μ)
    (hF1101top : MemLp (fun x ↦ F1101 x) ⊤ M.μ)
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero :
      HostKraCubeSeminorm.HasZeroHostKraU4 M hM
        (fun x ↦ H x) hHtop) :
    @inner ℂ (Lp ℂ 2 M.μ) _ H
        (fifteenVertexDualFunction M hM
          F0001 F0010 F0011 F0100 F0101 F0110 F0111
          F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
          hF0001top hF0010top hF0011top
          hF0100top hF0101top hF0110top hF0111top
          hF1000top hF1001top hF1010top hF1011top
          hF1100top hF1101top hF1110top) = 0 := by
  let C3 := relativeCubeSystemThree M hM
  let hC3 := relativeCubeSystemThree_mps M hM
  let A := sevenVertexCubeProduct M hM
    F0001 F0010 F0011 F0100 F0101 F0110 F0111
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top
  let hAtop := sevenVertexCubeProduct_memLp_top M hM
    F0001 F0010 F0011 F0100 F0101 F0110 F0111
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top hF0111top
  let B := eightVertexCubeProduct M hM
    F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
    hF1000top hF1001top hF1010top hF1011top
    hF1100top hF1101top hF1110top
  let H0 := baseVertexPullbackThree M hM H
  let K := mixedFaceWithBase C3 A H0 hAtop
  have hKzero :
      invariantProjectionCLM C3 hC3 K = 0 :=
    (invariantProjection_eq_zero_iff_inner_coordinateCopies_eq_zero
      C3 hC3 K).2
        (inner_mixedSevenFaceCopies_eq_zero_of_hasZeroHostKraU4
          M hM F0001 F0010 F0011 F0100 F0101 F0110 F0111 H
          hF0001top hF0010top hF0011top
          hF0100top hF0101top hF0110top hF0111top
          hHtop hzero)
  rw [inner_fifteenVertexDualFunction
    M hM
    F0001 F0010 F0011 F0100 F0101 F0110 F0111
    F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 H
    hF0001top hF0010top hF0011top
    hF0100top hF0101top hF0110top hF0111top
    hF1000top hF1001top hF1010top hF1011top
    hF1100top hF1101top hF1110top]
  exact inner_relativeEdgeProduct_eq_zero_of_mixedProjection_eq_zero
    C3 hC3 A B H0 hAtop hKzero

end Chapter02.HostKraGowersCauchySchwarzFour
