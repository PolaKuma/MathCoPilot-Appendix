import Chapter02.HostKra.HostKraCubeDisintegrationSymmetry
import Chapter02.HostKra.HostKraU3Nullspace

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraGowersCauchySchwarz

universe u

open HostKraStandardRelativeJoining
open HostKraDualFunction
open HostKraRelativeJoiningComplex
open HostKraCubeSeminorm

lemma baseVertexPullbackTwo_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ) :
    (fun q ↦ baseVertexPullbackTwo M hM H q) =ᵐ[
        (relativeCubeSystemTwo M hM).μ]
      fun q ↦ H q.1.1 := by
  let C := relativeCubeSystemOne M hM
  let hC := relativeCubeSystemOne_mps M hM
  have houter :=
    relativeFstCLM_coe C hC (relativeFstCLM M hM H)
  have hinner :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C hC)
      |>.quasiMeasurePreserving.ae_eq
        (relativeFstCLM_coe M hM H)
  filter_upwards [houter, hinner] with q hq hqinner
  change baseVertexPullbackTwo M hM H q =
    relativeFstCLM M hM H q.1 at hq
  change relativeFstCLM M hM H q.1 = H q.1.1 at hqinner
  exact hq.trans hqinner

/-- After exchanging the outer and middle cube directions, doubling the
first mixed face becomes another outer-cube pairing.  This is the second
Cauchy--Schwarz stage in coordinate form. -/
theorem inner_firstFaceCopies_eq_rotated_outerCube
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B C H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hBtop : MemLp (fun x ↦ B x) ⊤ M.μ)
    (hCtop : MemLp (fun x ↦ C x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ) :
    let K :=
      firstFaceWithBase M hM A B C H hAtop hBtop hCtop
    let Astar := ForwardKroneckerFactor.lpStar M A
    let Bstar := ForwardKroneckerFactor.lpStar M B
    let Cstar := ForwardKroneckerFactor.lpStar M C
    @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeSndCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) K)
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) K) =
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (baseVertexPullbackTwo M hM H))
        (sevenVertexCubeProduct M hM
          A H Astar B C Bstar Cstar
          hAtop hHtop
          ((memLp_congr_ae
            (ForwardKroneckerFactor.lpStar_coe M A)).mpr
              (ForwardKroneckerFactor.memLp_pointwiseStar hAtop))
          hBtop hCtop
          ((memLp_congr_ae
            (ForwardKroneckerFactor.lpStar_coe M B)).mpr
              (ForwardKroneckerFactor.memLp_pointwiseStar hBtop))) := by
  dsimp only
  let C2 := relativeCubeSystemTwo M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  let K := firstFaceWithBase M hM A B C H hAtop hBtop hCtop
  let Astar := ForwardKroneckerFactor.lpStar M A
  let Bstar := ForwardKroneckerFactor.lpStar M B
  let Cstar := ForwardKroneckerFactor.lpStar M C
  let hAstarTop : MemLp (fun x ↦ Astar x) ⊤ M.μ :=
    (memLp_congr_ae
      (ForwardKroneckerFactor.lpStar_coe M A)).mpr
        (ForwardKroneckerFactor.memLp_pointwiseStar hAtop)
  let hBstarTop : MemLp (fun x ↦ Bstar x) ⊤ M.μ :=
    (memLp_congr_ae
      (ForwardKroneckerFactor.lpStar_coe M B)).mpr
        (ForwardKroneckerFactor.memLp_pointwiseStar hBtop)
  let hCstarTop : MemLp (fun x ↦ Cstar x) ⊤ M.μ :=
    (memLp_congr_ae
      (ForwardKroneckerFactor.lpStar_coe M C)).mpr
        (ForwardKroneckerFactor.memLp_pointwiseStar hCtop)
  let L :=
    relativeSndCLM C2 hC2 K
  let R :=
    relativeFstCLM C2 hC2 K
  let H0 := baseVertexPullbackTwo M hM H
  let W :=
    sevenVertexCubeProduct M hM
      A H Astar B C Bstar Cstar
      hAtop hHtop hAstarTop hBtop hCtop hBstarTop
  have hmeas :
      AEStronglyMeasurable
        (fun r ↦ @inner ℂ ℂ _ (L r) (R r))
        (relativeCubeSystemThree M hM).μ :=
    (L2.integrable_inner (𝕜 := ℂ) L R).aestronglyMeasurable
  have hinv :=
    HilbertSchmidtInvariant.integral_comp_measurePreserving
      HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose
      (HostKraCubeDisintegrationSymmetry.cubeThreeOuterMiddleTranspose_measurePreserving
        M hM)
      (fun r ↦ @inner ℂ ℂ _ (L r) (R r)) hmeas
  have hinv' :
      (∫ r : (relativeCubeSystemThree M hM).X,
          @inner ℂ ℂ _ (L r) (R r)
          ∂(relativeCubeSystemThree M hM).μ) =
        ∫ r : (relativeCubeSystemThree M hM).X,
          @inner ℂ ℂ _
            (L (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r))
            (R (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r))
          ∂(relativeCubeSystemThree M hM).μ :=
    hinv.symm
  rw [L2.inner_def, L2.inner_def]
  change
    (∫ r, @inner ℂ ℂ _ (L r) (R r)
      ∂(relativeCubeSystemThree M hM).μ) =
      ∫ r, @inner ℂ ℂ _
        (relativeFstCLM C2 hC2 H0 r) (W r)
        ∂(relativeCubeSystemThree M hM).μ
  rw [hinv']
  apply integral_congr_ae
  have hL := relativeSndCLM_coe C2 hC2 K
  have hR := relativeFstCLM_coe C2 hC2 K
  have hK := firstFaceWithBase_coe M hM A B C H hAtop hBtop hCtop
  have hKfst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hK
  have hKsnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hK
  have hFace :=
    threeNonzeroFaceProduct_coe M hM A B C hAtop hBtop
  have hFacefst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hFace
  have hFacesnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hFace
  have hBase := baseVertexPullbackTwo_coe M hM H
  have hBasefst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hBase
  have hBasesnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hBase
  have hσ :=
    (HostKraCubeDisintegrationSymmetry.cubeThreeOuterMiddleTranspose_measurePreserving
      M hM)
      |>.quasiMeasurePreserving
  have hLσ := hσ.ae_eq hL
  have hRσ := hσ.ae_eq hR
  have hKfstσ := hσ.ae_eq hKfst
  have hKsndσ := hσ.ae_eq hKsnd
  have hFacefstσ := hσ.ae_eq hFacefst
  have hFacesndσ := hσ.ae_eq hFacesnd
  have hBasefstσ := hσ.ae_eq hBasefst
  have hBasesndσ := hσ.ae_eq hBasesnd
  have hH0 := baseVertexPullbackTwo_coe M hM H
  have hH0fst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hH0
  have hHpull := relativeFstCLM_coe C2 hC2 H0
  have hW := sevenVertexCubeProduct_coe M hM
    A H Astar B C Bstar Cstar
    hAtop hHtop hAstarTop hBtop hCtop hBstarTop
  have hAstar := ForwardKroneckerFactor.lpStar_coe M A
  have hBstar := ForwardKroneckerFactor.lpStar_coe M B
  have hCstar := ForwardKroneckerFactor.lpStar_coe M C
  have hAstar1 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq hAstar
  have hAstar2 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM))
      |>.quasiMeasurePreserving.ae_eq hAstar1
  have hAstar011 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hAstar2
  have hBstar1 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq hBstar
  have hBstar2 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM))
      |>.quasiMeasurePreserving.ae_eq hBstar1
  have hBstar110 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hBstar2
  have hCstar1 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq hCstar
  have hCstar2 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM))
      |>.quasiMeasurePreserving.ae_eq hCstar1
  have hCstar111 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hCstar2
  filter_upwards [hLσ, hRσ, hKfstσ, hKsndσ,
      hFacefstσ, hFacesndσ, hBasefstσ, hBasesndσ,
      hHpull, hH0fst, hW, hAstar011, hBstar110, hCstar111] with
      r hrL hrR hrKfst hrKsnd
        hrFacefst hrFacesnd hrBasefst hrBasesnd
        hrHpull hrH0 hrW
        hrAstar hrBstar hrCstar
  simp only [Function.comp_apply] at hrL hrR hrKfst hrKsnd
  change L (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r) =
    K (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r).2 at hrL
  change R (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r) =
    K (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r).1 at hrR
  change
    K (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r).1 =
      _ at hrKfst
  change
    K (HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose r).2 =
      _ at hrKsnd
  simp only [Function.comp_apply] at hrFacefst hrFacesnd hrBasefst hrBasesnd
  change relativeFstCLM C2 hC2 H0 r = H0 r.1 at hrHpull
  change H0 r.1 = H r.1.1.1 at hrH0
  change W r =
    (A r.1.1.2 * (H r.1.2.1 * Astar r.1.2.2)) *
      ((B r.2.1.1 * C r.2.1.2) *
        (Bstar r.2.2.1 * Cstar r.2.2.2)) at hrW
  rw [hrL, hrR, hrKfst, hrKsnd,
    hrFacefst, hrFacesnd, hrBasefst, hrBasesnd,
    hrHpull, hrH0, hrW]
  simp only [HostKraCubeSymmetry.cubeThreeOuterMiddleTranspose,
    RCLike.inner_apply, starRingEnd_apply, star_mul, star_star]
  simp only [Function.comp_apply] at hrAstar hrBstar hrCstar
  rw [hrAstar, hrBstar, hrCstar]
  ring

/-- Exchanging the outer and inner cube directions turns the doubled
second-stage face into the pairing of the two four-vertex cube lifts. -/
theorem inner_secondFaceCopies_eq_cubeLiftPairing
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ) :
    let Astar := ForwardKroneckerFactor.lpStar M A
    let hAstarTop : MemLp (fun x ↦ Astar x) ⊤ M.μ :=
      (memLp_congr_ae
        (ForwardKroneckerFactor.lpStar_coe M A)).mpr
          (ForwardKroneckerFactor.memLp_pointwiseStar hAtop)
    let K :=
      firstFaceWithBase M hM A H Astar H
        hAtop hHtop hAstarTop
    let FA :=
      (cubeLiftTwo_memLp_two M hM (fun x ↦ A x) hAtop).toLp
        (cubeLiftTwo M hM (fun x ↦ A x))
    let FH :=
      (cubeLiftTwo_memLp_two M hM (fun x ↦ H x) hHtop).toLp
        (cubeLiftTwo M hM (fun x ↦ H x))
    @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeSndCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) K)
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) K) =
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) FH)
        (relativeSndCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) FA) := by
  dsimp only
  let C2 := relativeCubeSystemTwo M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  let Astar := ForwardKroneckerFactor.lpStar M A
  let hAstarTop : MemLp (fun x ↦ Astar x) ⊤ M.μ :=
    (memLp_congr_ae
      (ForwardKroneckerFactor.lpStar_coe M A)).mpr
        (ForwardKroneckerFactor.memLp_pointwiseStar hAtop)
  let K :=
    firstFaceWithBase M hM A H Astar H
      hAtop hHtop hAstarTop
  let hFA := cubeLiftTwo_memLp_two M hM (fun x ↦ A x) hAtop
  let hFH := cubeLiftTwo_memLp_two M hM (fun x ↦ H x) hHtop
  let FA := hFA.toLp (cubeLiftTwo M hM (fun x ↦ A x))
  let FH := hFH.toLp (cubeLiftTwo M hM (fun x ↦ H x))
  let L := relativeSndCLM C2 hC2 K
  let R := relativeFstCLM C2 hC2 K
  let LF := relativeFstCLM C2 hC2 FH
  let RS := relativeSndCLM C2 hC2 FA
  have hmeas :
      AEStronglyMeasurable
        (fun r ↦ @inner ℂ ℂ _ (L r) (R r))
        (relativeCubeSystemThree M hM).μ :=
    (L2.integrable_inner (𝕜 := ℂ) L R).aestronglyMeasurable
  have hinv :=
    HilbertSchmidtInvariant.integral_comp_measurePreserving
      HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose
      (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose_measurePreserving
        M hM)
      (fun r ↦ @inner ℂ ℂ _ (L r) (R r)) hmeas
  have hinv' :
      (∫ r : (relativeCubeSystemThree M hM).X,
          @inner ℂ ℂ _ (L r) (R r)
          ∂(relativeCubeSystemThree M hM).μ) =
        ∫ r : (relativeCubeSystemThree M hM).X,
          @inner ℂ ℂ _
            (L (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r))
            (R (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r))
          ∂(relativeCubeSystemThree M hM).μ :=
    hinv.symm
  rw [L2.inner_def, L2.inner_def]
  change
    (∫ r, @inner ℂ ℂ _ (L r) (R r)
      ∂(relativeCubeSystemThree M hM).μ) =
      ∫ r, @inner ℂ ℂ _ (LF r) (RS r)
        ∂(relativeCubeSystemThree M hM).μ
  rw [hinv']
  apply integral_congr_ae
  have hL := relativeSndCLM_coe C2 hC2 K
  have hR := relativeFstCLM_coe C2 hC2 K
  have hK :=
    firstFaceWithBase_coe M hM A H Astar H
      hAtop hHtop hAstarTop
  have hKfst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hK
  have hKsnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hK
  have hFace :=
    threeNonzeroFaceProduct_coe M hM A H Astar hAtop hHtop
  have hFacefst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hFace
  have hFacesnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hFace
  have hBase := baseVertexPullbackTwo_coe M hM H
  have hBasefst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hBase
  have hBasesnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hBase
  have hσ :=
    (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose_measurePreserving
      M hM).quasiMeasurePreserving
  have hLσ := hσ.ae_eq hL
  have hRσ := hσ.ae_eq hR
  have hKfstσ := hσ.ae_eq hKfst
  have hKsndσ := hσ.ae_eq hKsnd
  have hFacefstσ := hσ.ae_eq hFacefst
  have hFacesndσ := hσ.ae_eq hFacesnd
  have hBasefstσ := hσ.ae_eq hBasefst
  have hBasesndσ := hσ.ae_eq hBasesnd
  have hLF := relativeFstCLM_coe C2 hC2 FH
  have hRS := relativeSndCLM_coe C2 hC2 FA
  have hFHcoe := hFH.coeFn_toLp
  have hFAcoe := hFA.coeFn_toLp
  have hFHfst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hFHcoe
  have hFAsnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hFAcoe
  have hAstar := ForwardKroneckerFactor.lpStar_coe M A
  have hAstarFst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq hAstar
  have hAstarSnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq hAstar
  have hAstarSndFst :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM))
      |>.quasiMeasurePreserving.ae_eq hAstarFst
  have hAstarSndSnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM))
      |>.quasiMeasurePreserving.ae_eq hAstarSnd
  have hAstar221 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hAstarSndFst
  have hAstar222 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq hAstarSndSnd
  filter_upwards [hLσ, hRσ, hKfstσ, hKsndσ,
      hFacefstσ, hFacesndσ, hBasefstσ, hBasesndσ,
      hLF, hRS, hFHfst, hFAsnd, hAstar221, hAstar222] with
      r hrL hrR hrKfst hrKsnd
        hrFacefst hrFacesnd hrBasefst hrBasesnd
        hrLF hrRS hrFH hrFA hrAstar221 hrAstar222
  simp only [Function.comp_apply] at hrL hrR hrKfst hrKsnd
  change L
      (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r) =
    K (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r).2
      at hrL
  change R
      (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r) =
    K (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r).1
      at hrR
  change
    K (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r).1 =
      _ at hrKfst
  change
    K (HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose r).2 =
      _ at hrKsnd
  simp only [Function.comp_apply] at hrFacefst hrFacesnd hrBasefst hrBasesnd
  change LF r = FH r.1 at hrLF
  change RS r = FA r.2 at hrRS
  change FH r.1 = cubeLiftTwo M hM (fun x ↦ H x) r.1 at hrFH
  change FA r.2 = cubeLiftTwo M hM (fun x ↦ A x) r.2 at hrFA
  simp only [Function.comp_apply] at hrAstar221 hrAstar222
  rw [hrL, hrR, hrKfst, hrKsnd,
    hrFacefst, hrFacesnd, hrBasefst, hrBasesnd,
    hrLF, hrRS, hrFH, hrFA]
  simp only [
    HostKraCubeDisintegrationSymmetry.cubeThreeOuterInnerTranspose]
  rw [hrAstar221, hrAstar222]
  simp only [
    cubeLiftTwo, cubeLiftOne, cubeLift, RCLike.inner_apply,
    starRingEnd_apply, star_mul, star_star]
  ring

/-- The terminal four-vertex pairing vanishes when the test vector has
zero order-two Host--Kra seminorm. -/
theorem cubeLiftPairing_eq_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop) :
    let FA :=
      (cubeLiftTwo_memLp_two M hM (fun x ↦ A x) hAtop).toLp
        (cubeLiftTwo M hM (fun x ↦ A x))
    let FH :=
      (cubeLiftTwo_memLp_two M hM (fun x ↦ H x) hHtop).toLp
        (cubeLiftTwo M hM (fun x ↦ H x))
    @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) FH)
        (relativeSndCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM) FA) = 0 := by
  dsimp only
  let C2 := relativeCubeSystemTwo M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  let hFA := cubeLiftTwo_memLp_two M hM (fun x ↦ A x) hAtop
  let hFH := cubeLiftTwo_memLp_two M hM (fun x ↦ H x) hHtop
  let FA := hFA.toLp (cubeLiftTwo M hM (fun x ↦ A x))
  let FH := hFH.toLp (cubeLiftTwo M hM (fun x ↦ H x))
  have hmean :=
    (hasZeroHostKraU3_iff_invariantMean
      M hM (fun x ↦ H x) hHtop).1 hzero
  have hproj : invariantProjectionCLM C2 hC2 FH = 0 := by
    rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection] at hmean
    exact hmean
  have hreverse :
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
          (relativeSndCLM C2 hC2 FA)
          (relativeFstCLM C2 hC2 FH) = 0 := by
    rw [inner_pullback_eq_invariantProjection C2 hC2 FA FH,
      hproj, inner_zero_right]
  exact inner_eq_zero_symm.mpr hreverse

/-- The second Cauchy--Schwarz face has zero invariant projection when its
base test vector is `U³`-null. -/
theorem secondFaceProjection_eq_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop) :
    let Astar := ForwardKroneckerFactor.lpStar M A
    let hAstarTop : MemLp (fun x ↦ Astar x) ⊤ M.μ :=
      (memLp_congr_ae
        (ForwardKroneckerFactor.lpStar_coe M A)).mpr
          (ForwardKroneckerFactor.memLp_pointwiseStar hAtop)
    invariantProjectionCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (firstFaceWithBase M hM A H Astar H
          hAtop hHtop hAstarTop) = 0 := by
  dsimp only
  let Astar := ForwardKroneckerFactor.lpStar M A
  let hAstarTop : MemLp (fun x ↦ Astar x) ⊤ M.μ :=
    (memLp_congr_ae
      (ForwardKroneckerFactor.lpStar_coe M A)).mpr
        (ForwardKroneckerFactor.memLp_pointwiseStar hAtop)
  rw [firstFaceProjection_eq_zero_iff
    M hM A H Astar H hAtop hHtop hAstarTop]
  rw [inner_secondFaceCopies_eq_cubeLiftPairing
    M hM A H hAtop hHtop]
  exact cubeLiftPairing_eq_zero_of_hasZeroHostKraU3
    M hM A H hAtop hHtop hzero

/-- The full three-weight first face has zero invariant projection against
every `U³`-null base test vector. -/
theorem firstFaceProjection_eq_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B C H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hBtop : MemLp (fun x ↦ B x) ⊤ M.μ)
    (hCtop : MemLp (fun x ↦ C x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop) :
    invariantProjectionCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (firstFaceWithBase M hM A B C H
          hAtop hBtop hCtop) = 0 := by
  let Astar := ForwardKroneckerFactor.lpStar M A
  let Bstar := ForwardKroneckerFactor.lpStar M B
  let Cstar := ForwardKroneckerFactor.lpStar M C
  let hAstarTop : MemLp (fun x ↦ Astar x) ⊤ M.μ :=
    (memLp_congr_ae
      (ForwardKroneckerFactor.lpStar_coe M A)).mpr
        (ForwardKroneckerFactor.memLp_pointwiseStar hAtop)
  let hBstarTop : MemLp (fun x ↦ Bstar x) ⊤ M.μ :=
    (memLp_congr_ae
      (ForwardKroneckerFactor.lpStar_coe M B)).mpr
        (ForwardKroneckerFactor.memLp_pointwiseStar hBtop)
  rw [firstFaceProjection_eq_zero_iff
    M hM A B C H hAtop hBtop hCtop]
  rw [inner_firstFaceCopies_eq_rotated_outerCube
    M hM A B C H hAtop hBtop hCtop hHtop]
  exact inner_outerCube_eq_zero_of_firstFaceProjection_eq_zero
    M hM A H Astar B C Bstar Cstar H
    hAtop hHtop hAstarTop hBtop hCtop hBstarTop
    (secondFaceProjection_eq_zero_of_hasZeroHostKraU3
      M hM A H hAtop hHtop hzero)

/-- Every eight-vertex mixed pairing with a `U³`-null base vector is zero. -/
theorem inner_sevenVertexCubeProduct_eq_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop) :
    @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (baseVertexPullbackTwo M hM H))
        (sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top) = 0 := by
  exact inner_outerCube_eq_zero_of_firstFaceProjection_eq_zero
    M hM F001 F010 F011 F100 F101 F110 F111 H
    hF001top hF010top hF011top
    hF100top hF101top hF110top
    (firstFaceProjection_eq_zero_of_hasZeroHostKraU3
      M hM F001 F010 F011 H
      hF001top hF010top hF011top hHtop hzero)

/-- The seven-vertex dual function is orthogonal to every bounded
`U³`-null test vector. -/
theorem inner_sevenVertexDualFunction_eq_zero_of_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM (fun x ↦ H x) hHtop) :
    @inner ℂ (Lp ℂ 2 M.μ) _ H
        (sevenVertexDualFunction M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top) = 0 := by
  rw [inner_sevenVertexDualFunction
    M hM F001 F010 F011 F100 F101 F110 F111 H
    hF001top hF010top hF011top
    hF100top hF101top hF110top]
  exact inner_sevenVertexCubeProduct_eq_zero_of_hasZeroHostKraU3
    M hM F001 F010 F011 F100 F101 F110 F111 H
    hF001top hF010top hF011top
    hF100top hF101top hF110top hHtop hzero

end Chapter02.HostKraGowersCauchySchwarz
