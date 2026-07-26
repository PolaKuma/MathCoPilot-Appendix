import Chapter02.HostKra.HostKraRelativeJoiningComplex

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraDualFunction

universe u

open HostKraStandardRelativeJoining
open HostKraRelativeJoiningComplex
open HostKraCubeFactors

/-- Conditional expectation from the relative joining to its first
coordinate, represented intrinsically as the Hilbert adjoint of the first
coordinate pullback.  This definition does not choose pointwise versions. -/
def relativeFstConditionalCLM
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Lp ℂ 2 (relativeJoiningMeasure M hM) →L[ℂ] Lp ℂ 2 M.μ :=
  (relativeFstCLM M hM).adjoint

/-- Conditional expectation from the relative joining to its second
coordinate. -/
def relativeSndConditionalCLM
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    Lp ℂ 2 (relativeJoiningMeasure M hM) →L[ℂ] Lp ℂ 2 M.μ :=
  (relativeSndCLM M hM).adjoint

/-- The defining pairing identity for first-coordinate conditional
expectation on the relative joining. -/
theorem inner_relativeFstConditionalCLM
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (H : Lp ℂ 2 (relativeJoiningMeasure M hM)) :
    @inner ℂ (Lp ℂ 2 M.μ) _ F
        (relativeFstConditionalCLM M hM H) =
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeFstCLM M hM F) H := by
  exact (relativeFstCLM M hM).adjoint_inner_right F H

/-- The defining pairing identity for second-coordinate conditional
expectation on the relative joining. -/
theorem inner_relativeSndConditionalCLM
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (H : Lp ℂ 2 (relativeJoiningMeasure M hM)) :
    @inner ℂ (Lp ℂ 2 M.μ) _ F
        (relativeSndConditionalCLM M hM H) =
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeSndCLM M hM F) H := by
  exact (relativeSndCLM M hM).adjoint_inner_right F H

/-- Pulling a base function to the first coordinate and then conditioning
back loses no information. -/
theorem relativeFstConditionalCLM_pullback
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    relativeFstConditionalCLM M hM (relativeFstCLM M hM F) = F := by
  refine ext_inner_left ℂ fun G => ?_
  rw [inner_relativeFstConditionalCLM]
  exact
    (Lp.compMeasurePreservingₗᵢ ℂ Prod.fst
      (relativeJoining_fst_measurePreserving M hM)).inner_map_map G F

/-- Pulling a base function to the second coordinate and then conditioning
back loses no information. -/
theorem relativeSndConditionalCLM_pullback
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    relativeSndConditionalCLM M hM (relativeSndCLM M hM F) = F := by
  refine ext_inner_left ℂ fun G => ?_
  rw [inner_relativeSndConditionalCLM]
  exact
    (Lp.compMeasurePreservingₗᵢ ℂ Prod.snd
      (relativeJoining_snd_measurePreserving M hM)).inner_map_map G F

/-- Conditioning the second coordinate on the first in the relatively
independent joining is exactly projection onto the invariant Koopman
subspace.  This is the operator form of relative independence and is the
first nontrivial dual-function identity. -/
theorem relativeFstConditionalCLM_snd_eq_invariantProjection
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : Lp ℂ 2 M.μ) :
    relativeFstConditionalCLM M hM (relativeSndCLM M hM G) =
      invariantProjectionCLM M hM G := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  refine ext_inner_left ℂ fun F => ?_
  rw [inner_relativeFstConditionalCLM]
  have hcross :
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
          (relativeFstCLM M hM F) (relativeSndCLM M hM G) =
        @inner ℂ (Lp ℂ 2 M.μ) _
          (invariantProjectionCLM M hM F)
          (invariantProjectionCLM M hM G) := by
    rw [← inner_conj_symm]
    rw [inner_pullback_eq_invariantProjection M hM G F]
    rw [inner_conj_symm]
  rw [hcross]
  let PF : Lp ℂ 2 M.μ := invariantProjectionCLM M hM F
  let PG : Lp ℂ 2 M.μ := invariantProjectionCLM M hM G
  have hPF : PF = (S.orthogonalProjection F).val := by
    rfl
  have hPG : PG = (S.orthogonalProjection G).val := by
    rfl
  have hPGmem : PG ∈ S := by
    rw [hPG]
    exact S.starProjection_apply_mem G
  have horth : F - PF ∈ Sᗮ := by
    rw [hPF]
    exact S.sub_starProjection_mem_orthogonal F
  have hz : @inner ℂ (Lp ℂ 2 M.μ) _ (F - PF) PG = 0 :=
    S.inner_left_of_mem_orthogonal hPGmem horth
  change @inner ℂ (Lp ℂ 2 M.μ) _ PF PG =
    @inner ℂ (Lp ℂ 2 M.μ) _ F PG
  calc
    @inner ℂ (Lp ℂ 2 M.μ) _ PF PG =
        0 + @inner ℂ (Lp ℂ 2 M.μ) _ PF PG := by rw [zero_add]
    _ = @inner ℂ (Lp ℂ 2 M.μ) _ (F - PF) PG +
        @inner ℂ (Lp ℂ 2 M.μ) _ PF PG := by rw [hz]
    _ = @inner ℂ (Lp ℂ 2 M.μ) _ ((F - PF) + PF) PG :=
      (inner_add_left _ _ _).symm
    _ = @inner ℂ (Lp ℂ 2 M.μ) _ F PG := by
      congr 1
      abel

/-- The symmetric cross-coordinate conditional identity. -/
theorem relativeSndConditionalCLM_fst_eq_invariantProjection
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : Lp ℂ 2 M.μ) :
    relativeSndConditionalCLM M hM (relativeFstCLM M hM G) =
      invariantProjectionCLM M hM G := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  refine ext_inner_left ℂ fun F => ?_
  rw [inner_relativeSndConditionalCLM]
  rw [inner_pullback_eq_invariantProjection M hM F G]
  let PF : Lp ℂ 2 M.μ := invariantProjectionCLM M hM F
  let PG : Lp ℂ 2 M.μ := invariantProjectionCLM M hM G
  have hPF : PF = (S.orthogonalProjection F).val := by
    rfl
  have hPG : PG = (S.orthogonalProjection G).val := by
    rfl
  have hPGmem : PG ∈ S := by
    rw [hPG]
    exact S.starProjection_apply_mem G
  have horth : F - PF ∈ Sᗮ := by
    rw [hPF]
    exact S.sub_starProjection_mem_orthogonal F
  have hz : @inner ℂ (Lp ℂ 2 M.μ) _ (F - PF) PG = 0 :=
    S.inner_left_of_mem_orthogonal hPGmem horth
  change @inner ℂ (Lp ℂ 2 M.μ) _ PF PG =
    @inner ℂ (Lp ℂ 2 M.μ) _ F PG
  calc
    @inner ℂ (Lp ℂ 2 M.μ) _ PF PG =
        0 + @inner ℂ (Lp ℂ 2 M.μ) _ PF PG := by rw [zero_add]
    _ = @inner ℂ (Lp ℂ 2 M.μ) _ (F - PF) PG +
        @inner ℂ (Lp ℂ 2 M.μ) _ PF PG := by rw [hz]
    _ = @inner ℂ (Lp ℂ 2 M.μ) _ ((F - PF) + PF) PG :=
      (inner_add_left _ _ _).symm
    _ = @inner ℂ (Lp ℂ 2 M.μ) _ F PG := by
      congr 1
      abel

/-- Essential boundedness is preserved when an `L²` representative is
pulled to the first coordinate of the relative joining. -/
lemma relativeFstCLM_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    MemLp (fun p ↦ relativeFstCLM M hM F p) ⊤
      (relativeJoiningMeasure M hM) := by
  rw [memLp_congr_ae
    (show
      (fun p ↦ relativeFstCLM M hM F p) =ᵐ[
        relativeJoiningMeasure M hM]
        (fun p ↦ F p.1) by
      simpa only [relativeFstCLM,
        LinearIsometry.coe_toContinuousLinearMap] using
        (Lp.coeFn_compMeasurePreserving F
          (relativeJoining_fst_measurePreserving M hM)))]
  exact hFtop.comp_measurePreserving
    (relativeJoining_fst_measurePreserving M hM)

/-- Essential boundedness is preserved when an `L²` representative is
pulled to the second coordinate of the relative joining. -/
lemma relativeSndCLM_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ) :
    MemLp (fun p ↦ relativeSndCLM M hM G p) ⊤
      (relativeJoiningMeasure M hM) := by
  rw [memLp_congr_ae
    (show
      (fun p ↦ relativeSndCLM M hM G p) =ᵐ[
        relativeJoiningMeasure M hM]
        (fun p ↦ G p.2) by
      simpa only [relativeSndCLM,
        LinearIsometry.coe_toContinuousLinearMap] using
        (Lp.coeFn_compMeasurePreserving G
          (relativeJoining_snd_measurePreserving M hM)))]
  exact hGtop.comp_measurePreserving
    (relativeJoining_snd_measurePreserving M hM)

lemma relativeFstCLM_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    (fun p ↦ relativeFstCLM M hM F p) =ᵐ[
      relativeJoiningMeasure M hM] (fun p ↦ F p.1) := by
  simpa only [relativeFstCLM,
    LinearIsometry.coe_toContinuousLinearMap] using
    (Lp.coeFn_compMeasurePreserving F
      (relativeJoining_fst_measurePreserving M hM))

lemma relativeSndCLM_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : Lp ℂ 2 M.μ) :
    (fun p ↦ relativeSndCLM M hM G p) =ᵐ[
      relativeJoiningMeasure M hM] (fun p ↦ G p.2) := by
  simpa only [relativeSndCLM,
    LinearIsometry.coe_toContinuousLinearMap] using
    (Lp.coeFn_compMeasurePreserving G
      (relativeJoining_snd_measurePreserving M hM))

/-- A first bounded relative dual product: multiply the two coordinate
pullbacks on the relative joining and condition the result back to the first
coordinate.  Iterating this construction on `relativeCubeSystemOne` and
`relativeCubeSystemTwo` supplies the low-order Host--Kra dual functions. -/
def relativeDualProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G F : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ) :
    Lp ℂ 2 M.μ :=
  relativeFstConditionalCLM M hM
    (MultipleKhintchineKronecker.lpPointwiseMul
      (M := relativeCubeSystemOne M hM)
      (relativeSndCLM M hM G)
      (relativeFstCLM M hM F)
      (relativeSndCLM_memLp_top M hM G hGtop))

/-- Pairing a relative dual product with a test vector is exactly the
corresponding three-factor pairing upstairs on the relative joining. -/
theorem inner_relativeDualProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G F H : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ H
        (relativeDualProduct M hM G F hGtop) =
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeFstCLM M hM H)
        (MultipleKhintchineKronecker.lpPointwiseMul
          (M := relativeCubeSystemOne M hM)
          (relativeSndCLM M hM G)
          (relativeFstCLM M hM F)
          (relativeSndCLM_memLp_top M hM G hGtop)) := by
  exact inner_relativeFstConditionalCLM M hM H _

/-- For a fixed bounded first input, the relative dual product is linear in
its second input. -/
theorem relativeDualProduct_add_right
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G F H : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ) :
    relativeDualProduct M hM G (F + H) hGtop =
      relativeDualProduct M hM G F hGtop +
        relativeDualProduct M hM G H hGtop := by
  unfold relativeDualProduct
  rw [map_add,
    MultipleKhintchineKronecker.lpPointwiseMul_add_right,
    map_add]

/-- Scalar linearity of the relative dual product in its second input. -/
theorem relativeDualProduct_smul_right
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (G F : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (c : ℂ) :
    relativeDualProduct M hM G (c • F) hGtop =
      c • relativeDualProduct M hM G F hGtop := by
  unfold relativeDualProduct
  rw [map_smul,
    MultipleKhintchineKronecker.lpPointwiseMul_smul_right,
    map_smul]

/-- The chosen `L²` representative of the pointwise product of two bounded
vectors remains essentially bounded. -/
lemma lpPointwiseMul_memLp_top
    {M : System.{u}}
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ) :
    MemLp
      (fun x ↦
        MultipleKhintchineKronecker.lpPointwiseMul F G hFtop x)
      ⊤ M.μ := by
  rw [memLp_congr_ae
    (MultipleKhintchineKronecker.lpPointwiseMul_coe F G hFtop)]
  exact hGtop.mul (r := ⊤) hFtop

lemma lpStar_memLp_top
    (M : System.{u})
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    MemLp (fun x ↦ ForwardKroneckerFactor.lpStar M F x) ⊤ M.μ := by
  rw [memLp_congr_ae (ForwardKroneckerFactor.lpStar_coe M F)]
  exact hFtop.star

/-- Product of two bounded inputs placed on the two coordinate vertices of
one relative edge. -/
def relativeEdgeProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0 F1 : Lp ℂ 2 M.μ)
    (hF0top : MemLp (fun x ↦ F0 x) ⊤ M.μ) :
    Lp ℂ 2 (relativeJoiningMeasure M hM) :=
  MultipleKhintchineKronecker.lpPointwiseMul
    (M := relativeCubeSystemOne M hM)
    (relativeFstCLM M hM F0)
    (relativeSndCLM M hM F1)
    (relativeFstCLM_memLp_top M hM F0 hF0top)

lemma relativeEdgeProduct_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0 F1 : Lp ℂ 2 M.μ)
    (hF0top : MemLp (fun x ↦ F0 x) ⊤ M.μ)
    (hF1top : MemLp (fun x ↦ F1 x) ⊤ M.μ) :
    MemLp
      (fun p ↦ relativeEdgeProduct M hM F0 F1 hF0top p)
      ⊤ (relativeJoiningMeasure M hM) := by
  exact lpPointwiseMul_memLp_top
    (M := relativeCubeSystemOne M hM)
    (relativeFstCLM M hM F0)
    (relativeSndCLM M hM F1)
    (relativeFstCLM_memLp_top M hM F0 hF0top)
    (relativeSndCLM_memLp_top M hM F1 hF1top)

lemma relativeEdgeProduct_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F0 F1 : Lp ℂ 2 M.μ)
    (hF0top : MemLp (fun x ↦ F0 x) ⊤ M.μ) :
    (fun p ↦ relativeEdgeProduct M hM F0 F1 hF0top p) =ᵐ[
      relativeJoiningMeasure M hM]
      (fun p ↦ F0 p.1 * F1 p.2) := by
  filter_upwards [
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (M := relativeCubeSystemOne M hM)
      (relativeFstCLM M hM F0)
      (relativeSndCLM M hM F1)
      (relativeFstCLM_memLp_top M hM F0 hF0top),
    relativeFstCLM_coe M hM F0,
    relativeSndCLM_coe M hM F1] with p hprod hfst hsnd
  change relativeEdgeProduct M hM F0 F1 hF0top p =
    relativeFstCLM M hM F0 p * relativeSndCLM M hM F1 p at hprod
  rw [hprod, hfst, hsnd]

/-- The product on the opposite edge of the first relative cube. -/
def secondEdgeProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F10 F11 : Lp ℂ 2 M.μ)
    (hF10top : MemLp (fun x ↦ F10 x) ⊤ M.μ) :
    Lp ℂ 2 (relativeJoiningMeasure M hM) :=
  MultipleKhintchineKronecker.lpPointwiseMul
    (M := relativeCubeSystemOne M hM)
    (relativeFstCLM M hM F10)
    (relativeSndCLM M hM F11)
    (relativeFstCLM_memLp_top M hM F10 hF10top)

lemma secondEdgeProduct_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F10 F11 : Lp ℂ 2 M.μ)
    (hF10top : MemLp (fun x ↦ F10 x) ⊤ M.μ)
    (hF11top : MemLp (fun x ↦ F11 x) ⊤ M.μ) :
    MemLp
      (fun p ↦ secondEdgeProduct M hM F10 F11 hF10top p)
      ⊤ (relativeJoiningMeasure M hM) := by
  exact lpPointwiseMul_memLp_top
    (M := relativeCubeSystemOne M hM)
    (relativeFstCLM M hM F10)
    (relativeSndCLM M hM F11)
    (relativeFstCLM_memLp_top M hM F10 hF10top)
    (relativeSndCLM_memLp_top M hM F11 hF11top)

/-- Product of four bounded inputs on all vertices of a relative square. -/
def fourVertexCubeProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hF00top : MemLp (fun x ↦ F00 x) ⊤ M.μ)
    (hF01top : MemLp (fun x ↦ F01 x) ⊤ M.μ)
    (hF10top : MemLp (fun x ↦ F10 x) ⊤ M.μ) :
    Lp ℂ 2
      (relativeJoiningMeasure
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)) :=
  relativeEdgeProduct
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeEdgeProduct M hM F00 F01 hF00top)
    (relativeEdgeProduct M hM F10 F11 hF10top)
    (relativeEdgeProduct_memLp_top
      M hM F00 F01 hF00top hF01top)

lemma fourVertexCubeProduct_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hF00top : MemLp (fun x ↦ F00 x) ⊤ M.μ)
    (hF01top : MemLp (fun x ↦ F01 x) ⊤ M.μ)
    (hF10top : MemLp (fun x ↦ F10 x) ⊤ M.μ)
    (hF11top : MemLp (fun x ↦ F11 x) ⊤ M.μ) :
    MemLp
      (fun q ↦
        fourVertexCubeProduct M hM F00 F01 F10 F11
          hF00top hF01top hF10top q)
      ⊤
      (relativeJoiningMeasure
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)) := by
  exact relativeEdgeProduct_memLp_top
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeEdgeProduct M hM F00 F01 hF00top)
    (relativeEdgeProduct M hM F10 F11 hF10top)
    (relativeEdgeProduct_memLp_top
      M hM F00 F01 hF00top hF01top)
    (relativeEdgeProduct_memLp_top
      M hM F10 F11 hF10top hF11top)

lemma fourVertexCubeProduct_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hF00top : MemLp (fun x ↦ F00 x) ⊤ M.μ)
    (hF01top : MemLp (fun x ↦ F01 x) ⊤ M.μ)
    (hF10top : MemLp (fun x ↦ F10 x) ⊤ M.μ) :
    (fun q ↦
      fourVertexCubeProduct M hM F00 F01 F10 F11
        hF00top hF01top hF10top q) =ᵐ[
      (relativeCubeSystemTwo M hM).μ]
      (fun q ↦
        (F00 q.1.1 * F01 q.1.2) *
          (F10 q.2.1 * F11 q.2.2)) := by
  have houter :=
    relativeEdgeProduct_coe
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (relativeEdgeProduct M hM F00 F01 hF00top)
      (relativeEdgeProduct M hM F10 F11 hF10top)
      (relativeEdgeProduct_memLp_top
        M hM F00 F01 hF00top hF01top)
  have hleft :=
    (relativeJoining_fst_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)).quasiMeasurePreserving.ae_eq
      (relativeEdgeProduct_coe M hM F00 F01 hF00top)
  have hright :=
    (relativeJoining_snd_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)).quasiMeasurePreserving.ae_eq
      (relativeEdgeProduct_coe M hM F10 F11 hF10top)
  filter_upwards [houter, hleft, hright] with q ho hl hr
  change
    fourVertexCubeProduct M hM F00 F01 F10 F11
        hF00top hF01top hF10top q =
      relativeEdgeProduct M hM F00 F01 hF00top q.1 *
        relativeEdgeProduct M hM F10 F11 hF10top q.2 at ho
  change
    relativeEdgeProduct M hM F00 F01 hF00top q.1 =
      F00 q.1.1 * F01 q.1.2 at hl
  change
    relativeEdgeProduct M hM F10 F11 hF10top q.2 =
      F10 q.2.1 * F11 q.2.2 at hr
  rw [ho, hl, hr]

/-- Product of the three non-base vertices `001`, `010`, and `011` on the
first square face of the three-dimensional relative cube. -/
def threeNonzeroFaceProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ) :
    Lp ℂ 2
      (relativeJoiningMeasure
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)) :=
  relativeEdgeProduct
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeSndCLM M hM F001)
    (relativeEdgeProduct M hM F010 F011 hF010top)
    (relativeSndCLM_memLp_top M hM F001 hF001top)

lemma threeNonzeroFaceProduct_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ) :
    MemLp
      (fun q ↦
        threeNonzeroFaceProduct M hM F001 F010 F011
          hF001top hF010top q)
      ⊤
      (relativeJoiningMeasure
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)) := by
  exact relativeEdgeProduct_memLp_top
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeSndCLM M hM F001)
    (relativeEdgeProduct M hM F010 F011 hF010top)
    (relativeSndCLM_memLp_top M hM F001 hF001top)
    (relativeEdgeProduct_memLp_top
      M hM F010 F011 hF010top hF011top)

lemma threeNonzeroFaceProduct_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ) :
    (fun q ↦
      threeNonzeroFaceProduct M hM F001 F010 F011
        hF001top hF010top q) =ᵐ[
      (relativeCubeSystemTwo M hM).μ]
      (fun q ↦ F001 q.1.2 * (F010 q.2.1 * F011 q.2.2)) := by
  have houter :=
    relativeEdgeProduct_coe
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (relativeSndCLM M hM F001)
      (relativeEdgeProduct M hM F010 F011 hF010top)
      (relativeSndCLM_memLp_top M hM F001 hF001top)
  have hleft :=
    (relativeJoining_fst_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)).quasiMeasurePreserving.ae_eq
      (relativeSndCLM_coe M hM F001)
  have hright :=
    (relativeJoining_snd_measurePreserving
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)).quasiMeasurePreserving.ae_eq
      (relativeEdgeProduct_coe M hM F010 F011 hF010top)
  filter_upwards [houter, hleft, hright] with q ho hl hr
  change
    threeNonzeroFaceProduct M hM F001 F010 F011
        hF001top hF010top q =
      relativeSndCLM M hM F001 q.1 *
        relativeEdgeProduct M hM F010 F011 hF010top q.2 at ho
  change relativeSndCLM M hM F001 q.1 = F001 q.1.2 at hl
  change
    relativeEdgeProduct M hM F010 F011 hF010top q.2 =
      F010 q.2.1 * F011 q.2.2 at hr
  rw [ho, hl, hr]

/-- Product of the seven non-base vertices of the three-dimensional
relative cube.  The first square contributes `001,010,011`; the opposite
square contributes `100,101,110,111`. -/
def sevenVertexCubeProduct
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    Lp ℂ 2
      (relativeJoiningMeasure
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)) :=
  relativeEdgeProduct
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (threeNonzeroFaceProduct M hM F001 F010 F011
      hF001top hF010top)
    (fourVertexCubeProduct M hM F100 F101 F110 F111
      hF100top hF101top hF110top)
    (threeNonzeroFaceProduct_memLp_top
      M hM F001 F010 F011 hF001top hF010top hF011top)

lemma sevenVertexCubeProduct_memLp_top
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ)
    (hF111top : MemLp (fun x ↦ F111 x) ⊤ M.μ) :
    MemLp
      (fun r ↦
        sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top r)
      ⊤
      (relativeJoiningMeasure
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)) := by
  exact relativeEdgeProduct_memLp_top
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (threeNonzeroFaceProduct M hM F001 F010 F011
      hF001top hF010top)
    (fourVertexCubeProduct M hM F100 F101 F110 F111
      hF100top hF101top hF110top)
    (threeNonzeroFaceProduct_memLp_top
      M hM F001 F010 F011 hF001top hF010top hF011top)
    (fourVertexCubeProduct_memLp_top
      M hM F100 F101 F110 F111
      hF100top hF101top hF110top hF111top)

lemma sevenVertexCubeProduct_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    (fun r ↦
      sevenVertexCubeProduct M hM
        F001 F010 F011 F100 F101 F110 F111
        hF001top hF010top hF011top
        hF100top hF101top hF110top r) =ᵐ[
      (relativeCubeSystemThree M hM).μ]
      (fun r ↦
        (F001 r.1.1.2 *
          (F010 r.1.2.1 * F011 r.1.2.2)) *
        ((F100 r.2.1.1 * F101 r.2.1.2) *
          (F110 r.2.2.1 * F111 r.2.2.2))) := by
  have houter :=
    relativeEdgeProduct_coe
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)
      (threeNonzeroFaceProduct M hM F001 F010 F011
        hF001top hF010top)
      (fourVertexCubeProduct M hM F100 F101 F110 F111
        hF100top hF101top hF110top)
      (threeNonzeroFaceProduct_memLp_top
        M hM F001 F010 F011 hF001top hF010top hF011top)
  have hleft :=
    (relativeJoining_fst_measurePreserving
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)).quasiMeasurePreserving.ae_eq
      (threeNonzeroFaceProduct_coe
        M hM F001 F010 F011 hF001top hF010top)
  have hright :=
    (relativeJoining_snd_measurePreserving
      (relativeCubeSystemTwo M hM)
      (relativeCubeSystemTwo_mps M hM)).quasiMeasurePreserving.ae_eq
      (fourVertexCubeProduct_coe
        M hM F100 F101 F110 F111
        hF100top hF101top hF110top)
  filter_upwards [houter, hleft, hright] with r ho hl hr
  change
    sevenVertexCubeProduct M hM
        F001 F010 F011 F100 F101 F110 F111
        hF001top hF010top hF011top
        hF100top hF101top hF110top r =
      threeNonzeroFaceProduct M hM F001 F010 F011
          hF001top hF010top r.1 *
        fourVertexCubeProduct M hM F100 F101 F110 F111
          hF100top hF101top hF110top r.2 at ho
  change
    threeNonzeroFaceProduct M hM F001 F010 F011
        hF001top hF010top r.1 =
      F001 r.1.1.2 * (F010 r.1.2.1 * F011 r.1.2.2) at hl
  change
    fourVertexCubeProduct M hM F100 F101 F110 F111
        hF100top hF101top hF110top r.2 =
      (F100 r.2.1.1 * F101 r.2.1.2) *
        (F110 r.2.2.1 * F111 r.2.2.2) at hr
  rw [ho, hl, hr]

/-- Pullback of a base vector to vertex `000` of the four-vertex cube. -/
def baseVertexPullbackTwo
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : Lp ℂ 2 M.μ) :
    Lp ℂ 2 (relativeCubeSystemTwo M hM).μ :=
  relativeFstCLM
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeFstCLM M hM H)

/-- The first square face of a mixed cube pairing: the three non-base
weights multiplied by the conjugate of the test vector at vertex `000`. -/
def firstFaceWithBase
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ) :
    Lp ℂ 2 (relativeCubeSystemTwo M hM).μ :=
  MultipleKhintchineKronecker.lpPointwiseMul
    (M := relativeCubeSystemTwo M hM)
    (threeNonzeroFaceProduct M hM F001 F010 F011
      hF001top hF010top)
    (ForwardKroneckerFactor.lpStar
      (relativeCubeSystemTwo M hM)
      (baseVertexPullbackTwo M hM H))
    (threeNonzeroFaceProduct_memLp_top
      M hM F001 F010 F011 hF001top hF010top hF011top)

lemma firstFaceWithBase_coe
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ) :
    (fun q ↦ firstFaceWithBase M hM F001 F010 F011 H
      hF001top hF010top hF011top q) =ᵐ[
        (relativeCubeSystemTwo M hM).μ]
      (fun q ↦
        threeNonzeroFaceProduct M hM F001 F010 F011
            hF001top hF010top q *
          star (baseVertexPullbackTwo M hM H q)) := by
  filter_upwards [
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (M := relativeCubeSystemTwo M hM)
      (threeNonzeroFaceProduct M hM F001 F010 F011
        hF001top hF010top)
      (ForwardKroneckerFactor.lpStar
        (relativeCubeSystemTwo M hM)
        (baseVertexPullbackTwo M hM H))
      (threeNonzeroFaceProduct_memLp_top
        M hM F001 F010 F011 hF001top hF010top hF011top),
    ForwardKroneckerFactor.lpStar_coe
      (relativeCubeSystemTwo M hM)
      (baseVertexPullbackTwo M hM H)] with q hprod hstar
  change
    firstFaceWithBase M hM F001 F010 F011 H
        hF001top hF010top hF011top q =
      threeNonzeroFaceProduct M hM F001 F010 F011
          hF001top hF010top q *
        ForwardKroneckerFactor.lpStar
          (relativeCubeSystemTwo M hM)
          (baseVertexPullbackTwo M hM H) q at hprod
  rw [hprod, hstar]

/-- The first Cauchy--Schwarz stage for an eight-vertex mixed pairing,
before taking norms: relative independence on the outermost joining turns
the pairing into an inner product of two invariant projections on the
four-vertex cube. -/
theorem inner_outerCube_eq_invariantProjections
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    @inner ℂ
        (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (baseVertexPullbackTwo M hM H))
        (sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top) =
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemTwo M hM).μ) _
        (invariantProjectionCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (ForwardKroneckerFactor.lpStar
            (relativeCubeSystemTwo M hM)
            (fourVertexCubeProduct M hM F100 F101 F110 F111
              hF100top hF101top hF110top)))
        (invariantProjectionCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (firstFaceWithBase M hM F001 F010 F011 H
            hF001top hF010top hF011top)) := by
  let C := relativeCubeSystemTwo M hM
  let hC := relativeCubeSystemTwo_mps M hM
  let A :=
    threeNonzeroFaceProduct M hM F001 F010 F011
      hF001top hF010top
  let B :=
    fourVertexCubeProduct M hM F100 F101 F110 F111
      hF100top hF101top hF110top
  let H₀ := baseVertexPullbackTwo M hM H
  let K :=
    firstFaceWithBase M hM F001 F010 F011 H
      hF001top hF010top hF011top
  have hpair :
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
          (relativeFstCLM C hC H₀)
          (sevenVertexCubeProduct M hM
            F001 F010 F011 F100 F101 F110 F111
            hF001top hF010top hF011top
            hF100top hF101top hF110top) =
        @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
          (relativeSndCLM C hC
            (ForwardKroneckerFactor.lpStar C B))
          (relativeFstCLM C hC K) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    have hAouter :=
      relativeEdgeProduct_coe C hC A B
        (threeNonzeroFaceProduct_memLp_top
          M hM F001 F010 F011 hF001top hF010top hF011top)
    have hHouter := relativeFstCLM_coe C hC H₀
    have hKouter := relativeFstCLM_coe C hC K
    have hBouter :=
      relativeSndCLM_coe C hC
        (ForwardKroneckerFactor.lpStar C B)
    have hK :=
      (relativeJoining_fst_measurePreserving C hC)
        |>.quasiMeasurePreserving.ae_eq
          (firstFaceWithBase_coe M hM F001 F010 F011 H
            hF001top hF010top hF011top)
    have hB :=
      (relativeJoining_snd_measurePreserving C hC)
        |>.quasiMeasurePreserving.ae_eq
          (ForwardKroneckerFactor.lpStar_coe C B)
    filter_upwards [hAouter, hHouter, hKouter, hBouter, hK, hB]
      with r hedge hH hKpull hBpull hKpoint hBpoint
    change
      sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top r =
        A r.1 * B r.2 at hedge
    change relativeFstCLM C hC H₀ r = H₀ r.1 at hH
    change relativeFstCLM C hC K r = K r.1 at hKpull
    change
      relativeSndCLM C hC
          (ForwardKroneckerFactor.lpStar C B) r =
        ForwardKroneckerFactor.lpStar C B r.2 at hBpull
    change K r.1 = A r.1 * star (H₀ r.1) at hKpoint
    change
      ForwardKroneckerFactor.lpStar C B r.2 =
        star (B r.2) at hBpoint
    simp only [RCLike.inner_apply]
    rw [hedge, hH, hKpull, hBpull, hKpoint, hBpoint]
    simp only [starRingEnd_apply, star_star]
    ring
  rw [hpair]
  exact inner_pullback_eq_invariantProjection C hC
    (ForwardKroneckerFactor.lpStar C B) K

/-- A vector has zero invariant projection exactly when the pairing of its
two coordinate copies on the next relative joining vanishes. -/
theorem invariantProjection_eq_zero_iff_inner_coordinateCopies_eq_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    invariantProjectionCLM M hM F = 0 ↔
      @inner ℂ (Lp ℂ 2 (relativeJoiningMeasure M hM)) _
        (relativeSndCLM M hM F) (relativeFstCLM M hM F) = 0 := by
  rw [inner_pullback_eq_invariantProjection M hM F F]
  exact ⟨fun h ↦ by rw [h, inner_zero_left],
    fun h ↦ inner_self_eq_zero.mp h⟩

/-- The remaining first-face projection obligation is equivalently a
single doubled-face pairing on the eight-vertex cube. -/
theorem firstFaceProjection_eq_zero_iff
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ) :
    invariantProjectionCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (firstFaceWithBase M hM F001 F010 F011 H
          hF001top hF010top hF011top) = 0 ↔
      @inner ℂ (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeSndCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (firstFaceWithBase M hM F001 F010 F011 H
            hF001top hF010top hF011top))
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (firstFaceWithBase M hM F001 F010 F011 H
            hF001top hF010top hF011top)) = 0 := by
  exact invariantProjection_eq_zero_iff_inner_coordinateCopies_eq_zero
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (firstFaceWithBase M hM F001 F010 F011 H
      hF001top hF010top hF011top)

/-- Cauchy--Schwarz estimate furnished by the outer projection identity. -/
theorem norm_inner_outerCube_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    ‖@inner ℂ
        (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (baseVertexPullbackTwo M hM H))
        (sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top)‖ ≤
      ‖invariantProjectionCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (ForwardKroneckerFactor.lpStar
          (relativeCubeSystemTwo M hM)
          (fourVertexCubeProduct M hM F100 F101 F110 F111
            hF100top hF101top hF110top))‖ *
      ‖invariantProjectionCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (firstFaceWithBase M hM F001 F010 F011 H
          hF001top hF010top hF011top)‖ := by
  rw [inner_outerCube_eq_invariantProjections M hM
    F001 F010 F011 F100 F101 F110 F111 H
    hF001top hF010top hF011top hF100top hF101top hF110top]
  exact norm_inner_le_norm _ _

/-- Once the mixed first face has zero invariant projection, every choice
of bounded weights on the opposite face gives zero eight-vertex pairing. -/
theorem inner_outerCube_eq_zero_of_firstFaceProjection_eq_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ)
    (hzero :
      invariantProjectionCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (firstFaceWithBase M hM F001 F010 F011 H
          hF001top hF010top hF011top) = 0) :
    @inner ℂ
        (Lp ℂ 2 (relativeCubeSystemThree M hM).μ) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (baseVertexPullbackTwo M hM H))
        (sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top) = 0 := by
  rw [inner_outerCube_eq_invariantProjections M hM
    F001 F010 F011 F100 F101 F110 F111 H
    hF001top hF010top hF011top hF100top hF101top hF110top,
    hzero, inner_zero_right]

/-- The order-two Host--Kra dual function: multiply seven bounded inputs on
the non-base vertices of the eight-vertex relative cube and condition along
the three successive first-coordinate maps to vertex `000`. -/
def sevenVertexDualFunction
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    Lp ℂ 2 M.μ :=
  relativeFstConditionalCLM M hM
    (relativeFstConditionalCLM
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (relativeFstConditionalCLM
        (relativeCubeSystemTwo M hM)
        (relativeCubeSystemTwo_mps M hM)
        (sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top)))

/-- Exact eight-vertex pairing identity for the order-two dual function. -/
theorem inner_sevenVertexDualFunction
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F001 F010 F011 F100 F101 F110 F111 H : Lp ℂ 2 M.μ)
    (hF001top : MemLp (fun x ↦ F001 x) ⊤ M.μ)
    (hF010top : MemLp (fun x ↦ F010 x) ⊤ M.μ)
    (hF011top : MemLp (fun x ↦ F011 x) ⊤ M.μ)
    (hF100top : MemLp (fun x ↦ F100 x) ⊤ M.μ)
    (hF101top : MemLp (fun x ↦ F101 x) ⊤ M.μ)
    (hF110top : MemLp (fun x ↦ F110 x) ⊤ M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ H
        (sevenVertexDualFunction M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top) =
      @inner ℂ
        (Lp ℂ 2
          (relativeJoiningMeasure
            (relativeCubeSystemTwo M hM)
            (relativeCubeSystemTwo_mps M hM))) _
        (relativeFstCLM
          (relativeCubeSystemTwo M hM)
          (relativeCubeSystemTwo_mps M hM)
          (relativeFstCLM
            (relativeCubeSystemOne M hM)
            (relativeCubeSystemOne_mps M hM)
            (relativeFstCLM M hM H)))
        (sevenVertexCubeProduct M hM
          F001 F010 F011 F100 F101 F110 F111
          hF001top hF010top hF011top
          hF100top hF101top hF110top) := by
  rw [sevenVertexDualFunction]
  rw [inner_relativeFstConditionalCLM M hM H]
  rw [inner_relativeFstConditionalCLM
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (relativeFstCLM M hM H)]
  rw [inner_relativeFstConditionalCLM
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (relativeFstCLM
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (relativeFstCLM M hM H))]

/-- The genuine three-vertex Host--Kra dual function.  On the four-vertex
relative cube it multiplies the inputs at vertices `01`, `10`, and `11`,
then conditions successively to the `00` vertex. -/
def threeVertexDualFunction
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F01 F10 F11 : Lp ℂ 2 M.μ)
    (hF10top : MemLp (fun x ↦ F10 x) ⊤ M.μ)
    (hF11top : MemLp (fun x ↦ F11 x) ⊤ M.μ) :
    Lp ℂ 2 M.μ :=
  relativeFstConditionalCLM M hM
    (relativeDualProduct
      (relativeCubeSystemOne M hM)
      (relativeCubeSystemOne_mps M hM)
      (secondEdgeProduct M hM F10 F11 hF10top)
      (relativeSndCLM M hM F01)
      (secondEdgeProduct_memLp_top
        M hM F10 F11 hF10top hF11top))

/-- Exact four-vertex pairing identity for the three-vertex dual function.
The test vector occupies vertex `00`; the three inputs occupy `01`, `10`,
and `11`. -/
theorem inner_threeVertexDualFunction
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F01 F10 F11 H : Lp ℂ 2 M.μ)
    (hF10top : MemLp (fun x ↦ F10 x) ⊤ M.μ)
    (hF11top : MemLp (fun x ↦ F11 x) ⊤ M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ H
        (threeVertexDualFunction M hM F01 F10 F11
          hF10top hF11top) =
      @inner ℂ
        (Lp ℂ 2
          (relativeJoiningMeasure
            (relativeCubeSystemOne M hM)
            (relativeCubeSystemOne_mps M hM))) _
        (relativeFstCLM
          (relativeCubeSystemOne M hM)
          (relativeCubeSystemOne_mps M hM)
          (relativeFstCLM M hM H))
        (MultipleKhintchineKronecker.lpPointwiseMul
          (M := relativeCubeSystemTwo M hM)
          (relativeSndCLM
            (relativeCubeSystemOne M hM)
            (relativeCubeSystemOne_mps M hM)
            (secondEdgeProduct M hM F10 F11 hF10top))
          (relativeFstCLM
            (relativeCubeSystemOne M hM)
            (relativeCubeSystemOne_mps M hM)
            (relativeSndCLM M hM F01))
          (relativeSndCLM_memLp_top
            (relativeCubeSystemOne M hM)
            (relativeCubeSystemOne_mps M hM)
            (secondEdgeProduct M hM F10 F11 hF10top)
            (secondEdgeProduct_memLp_top
              M hM F10 F11 hF10top hF11top))) := by
  rw [threeVertexDualFunction, inner_relativeFstConditionalCLM]
  exact inner_relativeDualProduct
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (secondEdgeProduct M hM F10 F11 hF10top)
    (relativeSndCLM M hM F01)
    (relativeFstCLM M hM H)
    (secondEdgeProduct_memLp_top
      M hM F10 F11 hF10top hF11top)

end Chapter02.HostKraDualFunction
