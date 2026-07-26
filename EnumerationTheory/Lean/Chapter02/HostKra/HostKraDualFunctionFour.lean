import Chapter02.HostKra.HostKraU4GowersRecursion

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraDualFunctionFour

universe u

open HostKraStandardRelativeJoining
open HostKraDualFunction
open HostKraRelativeJoiningComplex
open HostKraCubeFactors

lemma lpStar_lpStar
    (M : System.{u}) (F : Lp ℂ 2 M.μ) :
    ForwardKroneckerFactor.lpStar M
        (ForwardKroneckerFactor.lpStar M F) = F := by
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M
      (ForwardKroneckerFactor.lpStar M F),
    ForwardKroneckerFactor.lpStar_coe M F] with x hss hs
  rw [hss, hs, star_star]

/-- A bounded first face multiplied by the conjugate of a base test vector. -/
def mixedFaceWithBase
    (M : System.{u}) [StandardBorelSpace M.X]
    (A H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ) :
    Lp ℂ 2 M.μ :=
  MultipleKhintchineKronecker.lpPointwiseMul
    A (ForwardKroneckerFactor.lpStar M H) hAtop

lemma mixedFaceWithBase_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (A H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ) :
    (fun x ↦ mixedFaceWithBase M A H hAtop x) =ᵐ[M.μ]
      fun x ↦ A x * star (H x) := by
  filter_upwards [
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      A (ForwardKroneckerFactor.lpStar M H) hAtop,
    ForwardKroneckerFactor.lpStar_coe M H] with x hprod hstar
  change mixedFaceWithBase M A H hAtop x =
    A x * ForwardKroneckerFactor.lpStar M H x at hprod
  rw [hprod, hstar]

/-- Generic outer Cauchy--Schwarz identity for one relative edge. -/
theorem inner_relativeEdgeProduct_eq_invariantProjections
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ) :
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeFstCLM M hM H)
        (relativeEdgeProduct M hM A B hAtop) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (invariantProjectionCLM M hM
          (ForwardKroneckerFactor.lpStar M B))
        (invariantProjectionCLM M hM
          (mixedFaceWithBase M A H hAtop)) := by
  let K := mixedFaceWithBase M A H hAtop
  have hpair :
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
          (relativeFstCLM M hM H)
          (relativeEdgeProduct M hM A B hAtop) =
        @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
          (relativeSndCLM M hM
            (ForwardKroneckerFactor.lpStar M B))
          (relativeFstCLM M hM K) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    have hedge := relativeEdgeProduct_coe M hM A B hAtop
    have hHouter := relativeFstCLM_coe M hM H
    have hKouter := relativeFstCLM_coe M hM K
    have hBouter :=
      relativeSndCLM_coe M hM
        (ForwardKroneckerFactor.lpStar M B)
    have hK :=
      (relativeJoining_fst_measurePreserving M hM)
        |>.quasiMeasurePreserving.ae_eq
          (mixedFaceWithBase_coe M A H hAtop)
    have hB :=
      (relativeJoining_snd_measurePreserving M hM)
        |>.quasiMeasurePreserving.ae_eq
          (ForwardKroneckerFactor.lpStar_coe M B)
    filter_upwards [hedge, hHouter, hKouter, hBouter, hK, hB]
      with r hedge hH hKpull hBpull hKpoint hBpoint
    change relativeEdgeProduct M hM A B hAtop r =
      A r.1 * B r.2 at hedge
    change relativeFstCLM M hM H r = H r.1 at hH
    change relativeFstCLM M hM K r = K r.1 at hKpull
    change
      relativeSndCLM M hM
          (ForwardKroneckerFactor.lpStar M B) r =
        ForwardKroneckerFactor.lpStar M B r.2 at hBpull
    change K r.1 = A r.1 * star (H r.1) at hKpoint
    change ForwardKroneckerFactor.lpStar M B r.2 =
      star (B r.2) at hBpoint
    simp only [RCLike.inner_apply]
    rw [hedge, hH, hKpull, hBpull, hKpoint, hBpoint]
    simp only [starRingEnd_apply, star_star]
    ring
  rw [hpair]
  exact inner_pullback_eq_invariantProjection M hM
    (ForwardKroneckerFactor.lpStar M B) K

theorem inner_relativeEdgeProduct_eq_zero_of_mixedProjection_eq_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A B H : Lp ℂ 2 M.μ)
    (hAtop : MemLp (fun x ↦ A x) ⊤ M.μ)
    (hzero :
      invariantProjectionCLM M hM
        (mixedFaceWithBase M A H hAtop) = 0) :
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeFstCLM M hM H)
        (relativeEdgeProduct M hM A B hAtop) = 0 := by
  rw [inner_relativeEdgeProduct_eq_invariantProjections
    M hM A B H hAtop, hzero, inner_zero_right]

/-- The alternating product `F(x₀) * conj (F(x₁))` on one relative edge,
represented intrinsically in `L²`. -/
def alternatingEdgeProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    Lp ℂ 2 (relativeCubeSystemOne M hM).μ :=
  relativeEdgeProduct M hM F
    (ForwardKroneckerFactor.lpStar M F) hFtop

lemma alternatingEdgeProduct_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    MemLp (fun p ↦ alternatingEdgeProduct M hM F hFtop p) ⊤
      (relativeCubeSystemOne M hM).μ :=
  relativeEdgeProduct_memLp_top M hM F
    (ForwardKroneckerFactor.lpStar M F) hFtop
    (lpStar_memLp_top M F hFtop)

lemma alternatingEdgeProduct_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    (fun p ↦ alternatingEdgeProduct M hM F hFtop p) =ᵐ[
        (relativeCubeSystemOne M hM).μ]
      fun p ↦ F p.1 * star (F p.2) := by
  filter_upwards [
    relativeEdgeProduct_coe M hM F
      (ForwardKroneckerFactor.lpStar M F) hFtop,
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq
        (ForwardKroneckerFactor.lpStar_coe M F)] with p hedge hstar
  simp only [Function.comp_apply] at hstar
  change alternatingEdgeProduct M hM F hFtop p =
    F p.1 * ForwardKroneckerFactor.lpStar M F p.2 at hedge
  rw [hedge, hstar]

/-- The intrinsic alternating edge product is exactly the canonical `L²`
representative of the first Host--Kra cube lift. -/
lemma alternatingEdgeProduct_eq_cubeLiftOne_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    alternatingEdgeProduct M hM F hFtop =
      (HostKraCubeSeminorm.cubeLiftOne_memLp_two
        M hM (fun x ↦ F x) hFtop).toLp
        (HostKraCubeSeminorm.cubeLiftOne M hM (fun x ↦ F x)) := by
  apply Lp.ext
  exact (alternatingEdgeProduct_coe M hM F hFtop).trans
    (HostKraCubeSeminorm.cubeLiftOne_memLp_two
      M hM (fun x ↦ F x) hFtop).coeFn_toLp.symm

/-- The parity-conjugated four-vertex product is the canonical second cube
lift. -/
lemma fourVertexCubeProduct_parity_eq_cubeLiftTwo_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    fourVertexCubeProduct M hM F Fs Fs F
        hFtop hFstop hFstop =
      (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
        M hM (fun x ↦ F x) hFtop).toLp
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x)) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  apply Lp.ext
  have hprod := fourVertexCubeProduct_coe M hM
    F Fs Fs F hFtop hFstop hFstop
  have hstar := ForwardKroneckerFactor.lpStar_coe M F
  have hstar01 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
          |>.quasiMeasurePreserving.ae_eq hstar)
  have hstar10 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
          |>.quasiMeasurePreserving.ae_eq hstar)
  have hlift :=
    (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
      M hM (fun x ↦ F x) hFtop).coeFn_toLp
  filter_upwards [hprod, hstar01, hstar10, hlift] with
      r hr hs01 hs10 hl
  simp only [Function.comp_apply] at hs01 hs10
  rw [hr, hs01, hs10, hl]
  simp only [HostKraCubeSeminorm.cubeLiftTwo,
    HostKraCubeSeminorm.cubeLiftOne,
    HostKraCubeSeminorm.cubeLift, star_mul, star_star]
  ring

/-- The opposite parity square is the second cube lift of the conjugated
base vector. -/
lemma fourVertexCubeProduct_oppositeParity_eq_cubeLiftTwo_star_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    fourVertexCubeProduct M hM Fs F F Fs
        hFstop hFtop hFtop =
      (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
        M hM (fun x ↦ Fs x) hFstop).toLp
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ Fs x)) := by
  dsimp only
  have h :=
    fourVertexCubeProduct_parity_eq_cubeLiftTwo_toLp
      M hM (ForwardKroneckerFactor.lpStar M F)
        (lpStar_memLp_top M F hFtop)
  simpa only [lpStar_lpStar] using h

/-- Filling the base of the parity-conjugated three-vertex square face
recovers the canonical second cube lift. -/
lemma mixedParitySquareFace_eq_cubeLiftTwo_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    let A := threeNonzeroFaceProduct M hM Fs Fs F hFstop hFstop
    let hAtop := threeNonzeroFaceProduct_memLp_top
      M hM Fs Fs F hFstop hFstop hFtop
    mixedFaceWithBase
        (relativeCubeSystemTwo M hM) A
        (baseVertexPullbackTwo M hM Fs) hAtop =
      (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
        M hM (fun x ↦ F x) hFtop).toLp
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x)) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let A := threeNonzeroFaceProduct M hM Fs Fs F hFstop hFstop
  let hAtop := threeNonzeroFaceProduct_memLp_top
    M hM Fs Fs F hFstop hFstop hFtop
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  let C2 := relativeCubeSystemTwo M hM
  apply Lp.ext
  have hmix := mixedFaceWithBase_coe C2 A
    (baseVertexPullbackTwo M hM Fs) hAtop
  have hA := threeNonzeroFaceProduct_coe
    M hM Fs Fs F hFstop hFstop
  have hH :=
    Chapter02.HostKraGowersCauchySchwarz.baseVertexPullbackTwo_coe
      M hM Fs
  have hs := ForwardKroneckerFactor.lpStar_coe M F
  have hs00 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
          |>.quasiMeasurePreserving.ae_eq hs)
  have hs01 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
          |>.quasiMeasurePreserving.ae_eq hs)
  have hs10 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
          |>.quasiMeasurePreserving.ae_eq hs)
  have hlift :=
    (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
      M hM (fun x ↦ F x) hFtop).coeFn_toLp
  filter_upwards [hmix, hA, hH, hs00, hs01, hs10, hlift] with
      r hm ha hb h00 h01 h10 hl
  simp only [Function.comp_apply] at h00 h01 h10
  rw [hm, ha, hb, h00, h01, h10, hl]
  simp only [HostKraCubeSeminorm.cubeLiftTwo,
    HostKraCubeSeminorm.cubeLiftOne,
    HostKraCubeSeminorm.cubeLift, star_mul, star_star]
  ring

/-- Conjugating the second cube lift of the intrinsic conjugate vector
returns the second cube lift of the original vector. -/
lemma lpStar_cubeLiftTwo_star_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    let Qs :=
      (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
        M hM (fun x ↦ Fs x) hFstop).toLp
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ Fs x))
    ForwardKroneckerFactor.lpStar
        (relativeCubeSystemTwo M hM) Qs =
      (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
        M hM (fun x ↦ F x) hFtop).toLp
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x)) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let Qs :=
    (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
      M hM (fun x ↦ Fs x) hFstop).toLp
      (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ Fs x))
  apply Lp.ext
  have hout := ForwardKroneckerFactor.lpStar_coe
    (relativeCubeSystemTwo M hM) Qs
  have hQs :=
    (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
      M hM (fun x ↦ Fs x) hFstop).coeFn_toLp
  have hs := ForwardKroneckerFactor.lpStar_coe M F
  have hlift := Chapter02.HostKraU3Nullspace.cubeLiftTwo_congr_ae
    M hM hs
  have hstar := congrFun
    (Chapter02.HostKraU3Nullspace.cubeLiftTwo_star
      M hM (fun x ↦ F x))
  have hQ :=
    (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
      M hM (fun x ↦ F x) hFtop).coeFn_toLp
  filter_upwards [hout, hQs, hlift, hQ] with r ho hqs hl hq
  rw [ho, hqs, hl, hstar r, hq, star_star]

/-- Product of eight bounded inputs on all vertices of a three-dimensional
relative cube, grouped into four relative edges. -/
def eightVertexCubeProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F000 F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF000top : MemLp (fun x ↦ F000 x) ⊤ M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    Lp ℂ 2 (relativeCubeSystemThree M hM).μ :=
  fourVertexCubeProduct
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeEdgeProduct M hM F000 F001 hF000top)
    (relativeEdgeProduct M hM F010 F011 hF010top)
    (relativeEdgeProduct M hM F100 F101 hF100top)
    (relativeEdgeProduct M hM F110 F111 hF110top)
    (relativeEdgeProduct_memLp_top
      M hM F000 F001 hF000top hF001top)
    (relativeEdgeProduct_memLp_top
      M hM F010 F011 hF010top hF011top)
    (relativeEdgeProduct_memLp_top
      M hM F100 F101 hF100top hF101top)

lemma eightVertexCubeProduct_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F000 F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF000top : MemLp (fun x ↦ F000 x) ⊤ M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ)
    (hF111top : MemLp (fun x ↦ F111 x) ⊤ M.μ) :
    MemLp
      (fun r ↦ eightVertexCubeProduct M hM
        F000 F001 F010 F011 F100 F101 F110 F111
        hF000top hF001top hF010top hF011top
        hF100top hF101top hF110top r)
      ⊤ (relativeCubeSystemThree M hM).μ := by
  exact fourVertexCubeProduct_memLp_top
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeEdgeProduct M hM F000 F001 hF000top)
    (relativeEdgeProduct M hM F010 F011 hF010top)
    (relativeEdgeProduct M hM F100 F101 hF100top)
    (relativeEdgeProduct M hM F110 F111 hF110top)
    (relativeEdgeProduct_memLp_top
      M hM F000 F001 hF000top hF001top)
    (relativeEdgeProduct_memLp_top
      M hM F010 F011 hF010top hF011top)
    (relativeEdgeProduct_memLp_top
      M hM F100 F101 hF100top hF101top)
    (relativeEdgeProduct_memLp_top
      M hM F110 F111 hF110top hF111top)

lemma eightVertexCubeProduct_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F000 F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF000top : MemLp (fun x ↦ F000 x) ⊤ M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    (fun r ↦ eightVertexCubeProduct M hM
      F000 F001 F010 F011 F100 F101 F110 F111
      hF000top hF001top hF010top hF011top
      hF100top hF101top hF110top r) =ᵐ[
        (relativeCubeSystemThree M hM).μ]
      fun r ↦
        ((F000 r.1.1.1 * F001 r.1.1.2) *
          (F010 r.1.2.1 * F011 r.1.2.2)) *
        ((F100 r.2.1.1 * F101 r.2.1.2) *
          (F110 r.2.2.1 * F111 r.2.2.2)) := by
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  have hfour := fourVertexCubeProduct_coe C1 hC1
    (relativeEdgeProduct M hM F000 F001 hF000top)
    (relativeEdgeProduct M hM F010 F011 hF010top)
    (relativeEdgeProduct M hM F100 F101 hF100top)
    (relativeEdgeProduct M hM F110 F111 hF110top)
    (relativeEdgeProduct_memLp_top M hM F000 F001 hF000top hF001top)
    (relativeEdgeProduct_memLp_top M hM F010 F011 hF010top hF011top)
    (relativeEdgeProduct_memLp_top M hM F100 F101 hF100top hF101top)
  have h00 := relativeEdgeProduct_coe M hM F000 F001 hF000top
  have h01 := relativeEdgeProduct_coe M hM F010 F011 hF010top
  have h10 := relativeEdgeProduct_coe M hM F100 F101 hF100top
  have h11 := relativeEdgeProduct_coe M hM F110 F111 hF110top
  have h00' :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)).quasiMeasurePreserving.ae_eq
      ((HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
        |>.quasiMeasurePreserving.ae_eq h00)
  have h01' :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)).quasiMeasurePreserving.ae_eq
      ((HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
        |>.quasiMeasurePreserving.ae_eq h01)
  have h10' :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)).quasiMeasurePreserving.ae_eq
      ((HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
        |>.quasiMeasurePreserving.ae_eq h10)
  have h11' :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)).quasiMeasurePreserving.ae_eq
      ((HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
        |>.quasiMeasurePreserving.ae_eq h11)
  filter_upwards [hfour, h00', h01', h10', h11'] with
      r hr h00r h01r h10r h11r
  change eightVertexCubeProduct M hM
      F000 F001 F010 F011 F100 F101 F110 F111
      hF000top hF001top hF010top hF011top
      hF100top hF101top hF110top r = _ at hr
  simp only [Function.comp_apply] at h00r h01r h10r h11r
  rw [hr, h00r, h01r, h10r, h11r]

/-- The parity-conjugated eight-vertex product is the canonical third cube
lift. -/
lemma eightVertexCubeProduct_parity_eq_cubeLiftThree_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    eightVertexCubeProduct M hM
        F Fs Fs F Fs F F Fs
        hFtop hFstop hFstop hFtop hFstop hFtop hFtop =
      (HostKraCubeSeminorm.cubeLiftThree_memLp_two
        M hM (fun x ↦ F x) hFtop).toLp
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x)) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  let C2 := relativeCubeSystemTwo M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  apply Lp.ext
  have hprod := eightVertexCubeProduct_coe M hM
    F Fs Fs F Fs F F Fs
    hFtop hFstop hFstop hFtop hFstop hFtop hFtop
  have hs := ForwardKroneckerFactor.lpStar_coe M F
  have hs001 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hs010 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hs100 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hs111 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hlift :=
    (HostKraCubeSeminorm.cubeLiftThree_memLp_two
      M hM (fun x ↦ F x) hFtop).coeFn_toLp
  filter_upwards [hprod, hs001, hs010, hs100, hs111, hlift] with
      r hr h001 h010 h100 h111 hl
  simp only [Function.comp_apply] at h001 h010 h100 h111
  rw [hr, h001, h010, h100, h111, hl]
  simp only [HostKraCubeSeminorm.cubeLiftThree,
    HostKraCubeSeminorm.cubeLiftTwo,
    HostKraCubeSeminorm.cubeLiftOne,
    HostKraCubeSeminorm.cubeLift, star_mul, star_star]
  ring

/-- The opposite parity face is the third cube lift of the conjugated base
vector. -/
lemma eightVertexCubeProduct_oppositeParity_eq_cubeLiftThree_star_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    eightVertexCubeProduct M hM
        Fs F F Fs F Fs Fs F
        hFstop hFtop hFtop hFstop hFtop hFstop hFstop =
      (HostKraCubeSeminorm.cubeLiftThree_memLp_two
        M hM (fun x ↦ Fs x) hFstop).toLp
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ Fs x)) := by
  dsimp only
  have h :=
    eightVertexCubeProduct_parity_eq_cubeLiftThree_toLp
      M hM (ForwardKroneckerFactor.lpStar M F)
        (lpStar_memLp_top M F hFtop)
  simpa only [lpStar_lpStar] using h

/-- Product of the fifteen non-base vertices of a four-dimensional relative
cube.  The first outer face contributes seven vertices and the opposite
face contributes all eight. -/
def fifteenVertexCubeProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 :
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
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ) :
    Lp ℂ 2
      (relativeJoiningMeasure
        (relativeCubeSystemThree M hM)
        (relativeCubeSystemThree_mps M hM)) :=
  relativeEdgeProduct
    (relativeCubeSystemThree M hM)
    (relativeCubeSystemThree_mps M hM)
    (sevenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top)
    (eightVertexCubeProduct M hM
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top)
    (sevenVertexCubeProduct_memLp_top M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top)

lemma fifteenVertexCubeProduct_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 :
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
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ) :
    (fun r ↦ fifteenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top r) =ᵐ[
        relativeJoiningMeasure
          (relativeCubeSystemThree M hM)
          (relativeCubeSystemThree_mps M hM)]
      fun r ↦
        ((F0001 r.1.1.1.2 *
          (F0010 r.1.1.2.1 * F0011 r.1.1.2.2)) *
          ((F0100 r.1.2.1.1 * F0101 r.1.2.1.2) *
            (F0110 r.1.2.2.1 * F0111 r.1.2.2.2))) *
        (((F1000 r.2.1.1.1 * F1001 r.2.1.1.2) *
          (F1010 r.2.1.2.1 * F1011 r.2.1.2.2)) *
          ((F1100 r.2.2.1.1 * F1101 r.2.2.1.2) *
            (F1110 r.2.2.2.1 * F1111 r.2.2.2.2))) := by
  let C3 := relativeCubeSystemThree M hM
  let hC3 := relativeCubeSystemThree_mps M hM
  have hedge := relativeEdgeProduct_coe C3 hC3
    (sevenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top)
    (eightVertexCubeProduct M hM
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top)
    (sevenVertexCubeProduct_memLp_top M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top)
  have hleft :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C3 hC3)
      |>.quasiMeasurePreserving.ae_eq
        (sevenVertexCubeProduct_coe M hM
          F0001 F0010 F0011 F0100 F0101 F0110 F0111
          hF0001top hF0010top hF0011top
          hF0100top hF0101top hF0110top)
  have hright :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C3 hC3)
      |>.quasiMeasurePreserving.ae_eq
        (eightVertexCubeProduct_coe M hM
          F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
          hF1000top hF1001top hF1010top hF1011top
          hF1100top hF1101top hF1110top)
  filter_upwards [hedge, hleft, hright] with r hr hl hr'
  change fifteenVertexCubeProduct M hM
      F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
      hF0001top hF0010top hF0011top
      hF0100top hF0101top hF0110top hF0111top
      hF1000top hF1001top hF1010top hF1011top
      hF1100top hF1101top hF1110top r = _ at hr
  simp only [Function.comp_apply] at hl hr'
  rw [hr, hl, hr']

/-- Pull a base vector through the first coordinate at all three existing
cube levels, placing it at vertex `0000` of the four-cube. -/
def baseVertexPullbackThree
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ) :
    Lp ℂ 2 (relativeCubeSystemThree M hM).μ :=
  relativeFstCLM
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (baseVertexPullbackTwo M hM H)

lemma baseVertexPullbackThree_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ) :
    (fun r ↦ baseVertexPullbackThree M hM H r) =ᵐ[
        (relativeCubeSystemThree M hM).μ]
      fun r ↦ H r.1.1.1 := by
  let C2 := relativeCubeSystemTwo M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  have houter := relativeFstCLM_coe C2 hC2
    (baseVertexPullbackTwo M hM H)
  have hinner :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        (Chapter02.HostKraGowersCauchySchwarz.baseVertexPullbackTwo_coe
          M hM H)
  filter_upwards [houter, hinner] with r hr hri
  change baseVertexPullbackThree M hM H r =
    baseVertexPullbackTwo M hM H r.1 at hr
  change baseVertexPullbackTwo M hM H r.1 = H r.1.1.1 at hri
  exact hr.trans hri

/-- Filling the missing base vertex of the parity-conjugated seven-vertex
face with the conjugate test vector recovers the canonical third cube
lift. -/
lemma mixedParityFace_eq_cubeLiftThree_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    let A := sevenVertexCubeProduct M hM
      Fs Fs F Fs F F Fs
      hFstop hFstop hFtop hFstop hFtop hFtop
    let hAtop := sevenVertexCubeProduct_memLp_top M hM
      Fs Fs F Fs F F Fs
      hFstop hFstop hFtop hFstop hFtop hFtop hFstop
    mixedFaceWithBase
        (relativeCubeSystemThree M hM) A
        (baseVertexPullbackThree M hM Fs) hAtop =
      (HostKraCubeSeminorm.cubeLiftThree_memLp_two
        M hM (fun x ↦ F x) hFtop).toLp
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x)) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let A := sevenVertexCubeProduct M hM
    Fs Fs F Fs F F Fs
    hFstop hFstop hFtop hFstop hFtop hFtop
  let hAtop := sevenVertexCubeProduct_memLp_top M hM
    Fs Fs F Fs F F Fs
    hFstop hFstop hFtop hFstop hFtop hFtop hFstop
  let C1 := relativeCubeSystemOne M hM
  let hC1 := relativeCubeSystemOne_mps M hM
  let C2 := relativeCubeSystemTwo M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  let C3 := relativeCubeSystemThree M hM
  apply Lp.ext
  have hmix := mixedFaceWithBase_coe C3 A
    (baseVertexPullbackThree M hM Fs) hAtop
  have hA := sevenVertexCubeProduct_coe M hM
    Fs Fs F Fs F F Fs
    hFstop hFstop hFtop hFstop hFtop hFtop
  have hH := baseVertexPullbackThree_coe M hM Fs
  have hs := ForwardKroneckerFactor.lpStar_coe M F
  have hs000 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hs001 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hs010 :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hs100 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_fst_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hs111 :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving C2 hC2)
      |>.quasiMeasurePreserving.ae_eq
        ((HostKraCubeFactors.relativeJoining_snd_measurePreserving C1 hC1)
          |>.quasiMeasurePreserving.ae_eq
            ((HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
              |>.quasiMeasurePreserving.ae_eq hs))
  have hlift :=
    (HostKraCubeSeminorm.cubeLiftThree_memLp_two
      M hM (fun x ↦ F x) hFtop).coeFn_toLp
  filter_upwards [hmix, hA, hH,
      hs000, hs001, hs010, hs100, hs111, hlift] with
      r hm ha hbase h000 h001 h010 h100 h111 hl
  simp only [Function.comp_apply] at h000 h001 h010 h100 h111
  rw [hm, ha, hbase, h000, h001, h010, h100, h111, hl]
  simp only [HostKraCubeSeminorm.cubeLiftThree,
    HostKraCubeSeminorm.cubeLiftTwo,
    HostKraCubeSeminorm.cubeLiftOne,
    HostKraCubeSeminorm.cubeLift, star_mul, star_star]
  ring

/-- Conjugating the third cube lift of the intrinsic conjugate vector
returns the third cube lift of the original vector. -/
lemma lpStar_cubeLiftThree_star_toLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    let Qs :=
      (HostKraCubeSeminorm.cubeLiftThree_memLp_two
        M hM (fun x ↦ Fs x) hFstop).toLp
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ Fs x))
    ForwardKroneckerFactor.lpStar
        (relativeCubeSystemThree M hM) Qs =
      (HostKraCubeSeminorm.cubeLiftThree_memLp_two
        M hM (fun x ↦ F x) hFtop).toLp
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x)) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let Qs :=
    (HostKraCubeSeminorm.cubeLiftThree_memLp_two
      M hM (fun x ↦ Fs x) hFstop).toLp
      (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ Fs x))
  apply Lp.ext
  have hout := ForwardKroneckerFactor.lpStar_coe
    (relativeCubeSystemThree M hM) Qs
  have hQs :=
    (HostKraCubeSeminorm.cubeLiftThree_memLp_two
      M hM (fun x ↦ Fs x) hFstop).coeFn_toLp
  have hs := ForwardKroneckerFactor.lpStar_coe M F
  have hlift := Chapter02.HostKraU4Nullspace.cubeLiftThree_congr_ae
    M hM hs
  have hstar := congrFun
    (Chapter02.HostKraU4Nullspace.cubeLiftThree_star
      M hM (fun x ↦ F x))
  have hQ :=
    (HostKraCubeSeminorm.cubeLiftThree_memLp_two
      M hM (fun x ↦ F x) hFtop).coeFn_toLp
  filter_upwards [hout, hQs, hlift, hQ] with r ho hqs hl hq
  rw [ho, hqs, hl, hstar r, hq, star_star]

/-- The order-three Host--Kra dual function obtained by conditioning the
fifteen-vertex product successively to vertex `0000`. -/
def fifteenVertexDualFunction
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0001 F0010 F0011 F0100 F0101 F0110 F0111
      F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111 :
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
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ) :
    Lp ℂ 2 M.μ :=
  relativeFstConditionalCLM M hM
    (relativeFstConditionalCLM
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (relativeFstConditionalCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (relativeFstConditionalCLM
          (relativeCubeSystemThree M hM)
          (relativeCubeSystemThree_mps M hM)
          (fifteenVertexCubeProduct M hM
            F0001 F0010 F0011 F0100 F0101 F0110 F0111
            F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
            hF0001top hF0010top hF0011top
            hF0100top hF0101top hF0110top hF0111top
            hF1000top hF1001top hF1010top hF1011top
            hF1100top hF1101top hF1110top))))

/-- Exact sixteen-vertex pairing identity for the order-three dual
function. -/
theorem inner_fifteenVertexDualFunction
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
    (hF1110top : MemLp (fun x ↦ F1110 x) ⊤ M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ H
        (fifteenVertexDualFunction M hM
          F0001 F0010 F0011 F0100 F0101 F0110 F0111
          F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
          hF0001top hF0010top hF0011top
          hF0100top hF0101top hF0110top hF0111top
          hF1000top hF1001top hF1010top hF1011top
          hF1100top hF1101top hF1110top) =
      @inner ℂ
        (Lp ℂ 2
          (relativeJoiningMeasure
            (relativeCubeSystemThree M hM)
            (relativeCubeSystemThree_mps M hM))) _
        (relativeFstCLM
          (relativeCubeSystemThree M hM)
          (relativeCubeSystemThree_mps M hM)
          (baseVertexPullbackThree M hM H))
        (fifteenVertexCubeProduct M hM
          F0001 F0010 F0011 F0100 F0101 F0110 F0111
          F1000 F1001 F1010 F1011 F1100 F1101 F1110 F1111
          hF0001top hF0010top hF0011top
          hF0100top hF0101top hF0110top hF0111top
          hF1000top hF1001top hF1010top hF1011top
          hF1100top hF1101top hF1110top) := by
  rw [fifteenVertexDualFunction]
  rw [inner_relativeFstConditionalCLM M hM H]
  rw [inner_relativeFstConditionalCLM
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeFstCLM M hM H)]
  change
    @inner ℂ (Lp ℂ 2 (relativeCubeSystemTwo M hM).μ) _
      (baseVertexPullbackTwo M hM H) _ = _
  rw [inner_relativeFstConditionalCLM
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (baseVertexPullbackTwo M hM H)]
  change
    @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
      (baseVertexPullbackThree M hM H) _ = _
  rw [inner_relativeFstConditionalCLM
    (relativeCubeSystemThree M hM)
    (relativeCubeSystemThree_mps M hM)
    (baseVertexPullbackThree M hM H)]

/-- The parity-conjugated seven-vertex dual pairing is exactly the
nonnegative `U³` invariant energy. -/
theorem inner_lpStar_paritySevenDual_eq_hostKraU3Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    @inner ℂ (Lp ℂ 2 M.μ) _ Fs
        (sevenVertexDualFunction M hM
          Fs Fs F Fs F F Fs
          hFstop hFstop hFtop hFstop hFtop hFtop) =
      ((HostKraCubeSeminorm.hostKraU3Power
        M hM (fun x ↦ F x) hFtop : ℝ) : ℂ) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let C2 := relativeCubeSystemTwo M hM
  let hC2 := relativeCubeSystemTwo_mps M hM
  let A := threeNonzeroFaceProduct M hM Fs Fs F hFstop hFstop
  let hAtop := threeNonzeroFaceProduct_memLp_top
    M hM Fs Fs F hFstop hFstop hFtop
  let B := fourVertexCubeProduct M hM
    Fs F F Fs hFstop hFtop hFtop
  let H0 := baseVertexPullbackTwo M hM Fs
  let Q :=
    (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
      M hM (fun x ↦ F x) hFtop).toLp
      (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x))
  have hfill :
      mixedFaceWithBase C2 A H0 hAtop = Q :=
    mixedParitySquareFace_eq_cubeLiftTwo_toLp M hM F hFtop
  have hB :
      B =
        (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
          M hM (fun x ↦ Fs x) hFstop).toLp
          (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ Fs x)) :=
    fourVertexCubeProduct_oppositeParity_eq_cubeLiftTwo_star_toLp
      M hM F hFtop
  have hstarB :
      ForwardKroneckerFactor.lpStar C2 B = Q := by
    rw [hB]
    exact lpStar_cubeLiftTwo_star_toLp M hM F hFtop
  rw [HostKraDualFunction.inner_sevenVertexDualFunction
    M hM Fs Fs F Fs F F Fs Fs
    hFstop hFstop hFtop hFstop hFtop hFtop]
  change
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure C2 hC2)) _
      (relativeFstCLM C2 hC2 H0)
      (relativeEdgeProduct C2 hC2 A B hAtop) = _
  rw [inner_relativeEdgeProduct_eq_invariantProjections
    C2 hC2 A B H0 hAtop, hstarB, hfill]
  have hmean :
      invariantProjectionCLM C2 hC2 Q =
        HostKraRelativeMean.invariantMeanLp C2 hC2
          (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x))
          (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
            M hM (fun x ↦ F x) hFtop) := by
    simpa only [Q, invariantProjectionCLM,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
      (HostKraRelativeMean.invariantMeanLp_eq_fixedProjection
        C2 hC2
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
          M hM (fun x ↦ F x) hFtop)).symm
  rw [hmean]
  change
    @inner ℂ (Lp ℂ 2 C2.μ) _
      (HostKraRelativeMean.invariantMeanLp C2 hC2
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
          M hM (fun x ↦ F x) hFtop))
      (HostKraRelativeMean.invariantMeanLp C2 hC2
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
          M hM (fun x ↦ F x) hFtop)) =
      ((HostKraCubeSeminorm.invariantEnergy C2 hC2
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
          M hM (fun x ↦ F x) hFtop) : ℝ) : ℂ)
  simpa only [HostKraCubeSeminorm.invariantEnergy,
    Complex.ofReal_pow] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (HostKraRelativeMean.invariantMeanLp C2 hC2
        (HostKraCubeSeminorm.cubeLiftTwo M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftTwo_memLp_two
          M hM (fun x ↦ F x) hFtop)))

/-- The parity-conjugated fifteen-vertex dual pairing is exactly the
nonnegative `U⁴` invariant energy. -/
theorem inner_lpStar_parityDual_eq_hostKraU4Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    let Fs := ForwardKroneckerFactor.lpStar M F
    let hFstop := lpStar_memLp_top M F hFtop
    @inner ℂ (Lp ℂ 2 M.μ) _ Fs
        (fifteenVertexDualFunction M hM
          Fs Fs F Fs F F Fs
          Fs F F Fs F Fs Fs F
          hFstop hFstop hFtop hFstop hFtop hFtop hFstop
          hFstop hFtop hFtop hFstop hFtop hFstop hFstop) =
      ((HostKraCubeSeminorm.hostKraU4Power
        M hM (fun x ↦ F x) hFtop : ℝ) : ℂ) := by
  dsimp only
  let Fs := ForwardKroneckerFactor.lpStar M F
  let hFstop := lpStar_memLp_top M F hFtop
  let C3 := relativeCubeSystemThree M hM
  let hC3 := relativeCubeSystemThree_mps M hM
  let A := sevenVertexCubeProduct M hM
    Fs Fs F Fs F F Fs
    hFstop hFstop hFtop hFstop hFtop hFtop
  let hAtop := sevenVertexCubeProduct_memLp_top M hM
    Fs Fs F Fs F F Fs
    hFstop hFstop hFtop hFstop hFtop hFtop hFstop
  let B := eightVertexCubeProduct M hM
    Fs F F Fs F Fs Fs F
    hFstop hFtop hFtop hFstop hFtop hFstop hFstop
  let H0 := baseVertexPullbackThree M hM Fs
  let Q :=
    (HostKraCubeSeminorm.cubeLiftThree_memLp_two
      M hM (fun x ↦ F x) hFtop).toLp
      (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x))
  have hfill :
      mixedFaceWithBase C3 A H0 hAtop = Q :=
    mixedParityFace_eq_cubeLiftThree_toLp M hM F hFtop
  have hB :
      B =
        (HostKraCubeSeminorm.cubeLiftThree_memLp_two
          M hM (fun x ↦ Fs x) hFstop).toLp
          (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ Fs x)) :=
    eightVertexCubeProduct_oppositeParity_eq_cubeLiftThree_star_toLp
      M hM F hFtop
  have hstarB :
      ForwardKroneckerFactor.lpStar C3 B = Q := by
    rw [hB]
    exact lpStar_cubeLiftThree_star_toLp M hM F hFtop
  rw [inner_fifteenVertexDualFunction
    M hM
    Fs Fs F Fs F F Fs
    Fs F F Fs F Fs Fs F Fs
    hFstop hFstop hFtop hFstop hFtop hFtop hFstop
    hFstop hFtop hFtop hFstop hFtop hFstop hFstop]
  change
    @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure C3 hC3)) _
      (relativeFstCLM C3 hC3 H0)
      (relativeEdgeProduct C3 hC3 A B hAtop) = _
  rw [inner_relativeEdgeProduct_eq_invariantProjections
    C3 hC3 A B H0 hAtop, hstarB, hfill]
  have hmean :
      invariantProjectionCLM C3 hC3 Q =
        HostKraRelativeMean.invariantMeanLp C3 hC3
          (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x))
          (HostKraCubeSeminorm.cubeLiftThree_memLp_two
            M hM (fun x ↦ F x) hFtop) := by
    simpa only [Q, invariantProjectionCLM,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
      (HostKraRelativeMean.invariantMeanLp_eq_fixedProjection
        C3 hC3
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftThree_memLp_two
          M hM (fun x ↦ F x) hFtop)).symm
  rw [hmean]
  change
    @inner ℂ (Lp ℂ 2 C3.μ) _
      (HostKraRelativeMean.invariantMeanLp C3 hC3
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftThree_memLp_two
          M hM (fun x ↦ F x) hFtop))
      (HostKraRelativeMean.invariantMeanLp C3 hC3
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftThree_memLp_two
          M hM (fun x ↦ F x) hFtop)) =
      ((HostKraCubeSeminorm.invariantEnergy C3 hC3
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftThree_memLp_two
          M hM (fun x ↦ F x) hFtop) : ℝ) : ℂ)
  simpa only [HostKraCubeSeminorm.invariantEnergy,
    Complex.ofReal_pow] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
      (HostKraRelativeMean.invariantMeanLp C3 hC3
        (HostKraCubeSeminorm.cubeLiftThree M hM (fun x ↦ F x))
        (HostKraCubeSeminorm.cubeLiftThree_memLp_two
          M hM (fun x ↦ F x) hFtop)))

end Chapter02.HostKraDualFunctionFour
