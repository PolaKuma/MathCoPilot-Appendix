import Chapter02.HostKra.HostKraRelativeJoiningComplex

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraU3Nullspace

universe u

open HostKraCubeSeminorm HostKraStandardRelativeJoining

/-- The invariant mean vanishes after scalar multiplication whenever it
vanishes before scalar multiplication.  The hypotheses identify the two
input `L²` vectors and avoid any dependence on representatives. -/
theorem invariantMeanLp_eq_zero_of_toLp_eq_smul
    (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ)
    (hf : M.lpMember 2 f) (hg : M.lpMember 2 g)
    (c : ℂ)
    (hfg : hf.toLp f = c • hg.toLp g)
    (hzero : HostKraRelativeMean.invariantMeanLp M hM g hg = 0) :
    HostKraRelativeMean.invariantMeanLp M hM f hf = 0 := by
  let D := MultipleKhintchineCharacteristic.KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  change (S.orthogonalProjection (hf.toLp f) : Lp ℂ 2 M.μ) = 0
  rw [hfg, map_smul]
  have hgproj :
      (S.orthogonalProjection (hg.toLp g) : Lp ℂ 2 M.μ) = 0 := by
    rw [← HostKraRelativeMean.invariantMeanLp_eq_fixedProjection M hM g hg]
    exact hzero
  have hgprojSubtype : S.orthogonalProjection (hg.toLp g) = 0 :=
    Subtype.ext hgproj
  rw [hgprojSubtype, smul_zero]
  rfl

/-- Two cube lifts turn multiplication of the base function by `c` into
multiplication by the scalar `(c * star c) * star (c * star c)`. -/
lemma cubeLiftTwo_const_mul
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (f : M.X → ℂ) :
    cubeLiftTwo M hM (fun x ↦ c * f x) =
      fun p ↦ ((c * star c) * star (c * star c)) *
        cubeLiftTwo M hM f p := by
  funext p
  simp only [cubeLiftTwo, cubeLiftOne, cubeLift, star_mul]
  ring

/-- A cube lift respects almost-everywhere equality because both coordinate
projections of the relative joining preserve the predecessor measure. -/
lemma cubeLift_congr_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {f g : M.X → ℂ} (hfg : f =ᵐ[M.μ] g) :
    cubeLift f =ᵐ[(relativeJoiningMeasure M hM)] cubeLift g := by
  have hfst :=
    (HostKraCubeFactors.relativeJoining_fst_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq hfg
  have hsnd :=
    (HostKraCubeFactors.relativeJoining_snd_measurePreserving M hM)
      |>.quasiMeasurePreserving.ae_eq hfg
  filter_upwards [hfst, hsnd] with p hp₁ hp₂
  simp only [Function.comp_apply] at hp₁ hp₂
  simp only [cubeLift, hp₁, hp₂]

/-- The four-vertex lift used in `U³` respects almost-everywhere equality
on the base system. -/
lemma cubeLiftTwo_congr_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {f g : M.X → ℂ} (hfg : f =ᵐ[M.μ] g) :
    cubeLiftTwo M hM f =ᵐ[(relativeCubeSystemTwo M hM).μ]
      cubeLiftTwo M hM g := by
  exact cubeLift_congr_ae
    (relativeCubeSystemOne M hM)
    (relativeCubeSystemOne_mps M hM)
    (cubeLift_congr_ae M hM hfg)

/-- The `U³` null condition depends only on the almost-everywhere class of
the bounded function. -/
theorem hasZeroHostKraU3_congr
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : MemLp f ⊤ M.μ) (hg : MemLp g ⊤ M.μ)
    (hfg : f =ᵐ[M.μ] g)
    (hzero : HasZeroHostKraU3 M hM f hf) :
    HasZeroHostKraU3 M hM g hg := by
  let C := relativeCubeSystemTwo M hM
  let hC := relativeCubeSystemTwo_mps M hM
  let F := cubeLiftTwo M hM f
  let G := cubeLiftTwo M hM g
  let hF := cubeLiftTwo_memLp_two M hM f hf
  let hG := cubeLiftTwo_memLp_two M hM g hg
  have hFG : hF.toLp F = hG.toLp G :=
    MemLp.toLp_congr hF hG (cubeLiftTwo_congr_ae M hM hfg)
  apply (hasZeroHostKraU3_iff_invariantMean M hM g hg).2
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  change
    ((LinearMap.eqLocus
      (MultipleKhintchineCharacteristic.KData C hC).U
      (1 : Lp ℂ 2 C.μ →L[ℂ] Lp ℂ 2 C.μ)).orthogonalProjection
        (hG.toLp G)).val = 0
  rw [← hFG]
  calc
    _ = HostKraRelativeMean.invariantMeanLp C hC F hF :=
      (HostKraRelativeMean.invariantMeanLp_eq_fixedProjection
        C hC F hF).symm
    _ = 0 := (hasZeroHostKraU3_iff_invariantMean M hM f hf).1 hzero

/-- `HasZeroHostKraU3` is closed under complex scalar multiplication.
This is one of the algebraic inputs for realizing the `U³` kernel as a
linear subspace. -/
theorem hasZeroHostKraU3_const_mul
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM f hf)
    (c : ℂ) :
    HasZeroHostKraU3 M hM (fun x ↦ c * f x) (hf.const_mul c) := by
  let C := relativeCubeSystemTwo M hM
  let hC := relativeCubeSystemTwo_mps M hM
  let g := cubeLiftTwo M hM f
  let gc := cubeLiftTwo M hM (fun x ↦ c * f x)
  let hg := cubeLiftTwo_memLp_two M hM f hf
  let hgc :=
    cubeLiftTwo_memLp_two M hM (fun x ↦ c * f x) (hf.const_mul c)
  let a : ℂ := (c * star c) * star (c * star c)
  have hLp : hgc.toLp gc = a • hg.toLp g := by
    apply Lp.ext
    filter_upwards [hgc.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_smul a (hg.toLp g)] with p hcp hp hsp
    rw [hcp, hsp]
    change cubeLiftTwo M hM (fun x ↦ c * f x) p =
      a * (hg.toLp (cubeLiftTwo M hM f)) p
    rw [hp]
    exact congrFun (cubeLiftTwo_const_mul M hM c f) p
  apply (hasZeroHostKraU3_iff_invariantMean
    M hM (fun x ↦ c * f x) (hf.const_mul c)).2
  apply invariantMeanLp_eq_zero_of_toLp_eq_smul
    C hC gc g hgc hg a hLp
  exact (hasZeroHostKraU3_iff_invariantMean M hM f hf).1 hzero

/-- The zero function is `U³`-null. -/
theorem hasZeroHostKraU3_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    HasZeroHostKraU3 M hM (fun _ ↦ (0 : ℂ))
      (MemLp.zero') := by
  apply (hasZeroHostKraU3_iff_invariantMean M hM
    (fun _ ↦ (0 : ℂ)) MemLp.zero').2
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  have hcube :
      cubeLiftTwo M hM (fun _ ↦ (0 : ℂ)) =
        (0 : (relativeCubeSystemTwo M hM).X → ℂ) := by
    funext p
    simp [cubeLiftTwo, cubeLiftOne, cubeLift]
  have htoLp :
      (cubeLiftTwo_memLp_two M hM (fun _ ↦ (0 : ℂ)) MemLp.zero').toLp
          (cubeLiftTwo M hM (fun _ ↦ (0 : ℂ))) = 0 := by
    apply Lp.ext
    filter_upwards [
      (cubeLiftTwo_memLp_two M hM
        (fun _ ↦ (0 : ℂ)) MemLp.zero').coeFn_toLp,
      Lp.coeFn_zero ℂ 2 (relativeCubeSystemTwo M hM).μ] with p hp h0
    rw [hp, hcube, Pi.zero_apply, h0]
    simp
  rw [htoLp, map_zero]
  rfl

/-- Complex conjugation commutes with the four-vertex cube lift. -/
lemma cubeLiftTwo_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftTwo M hM (fun x ↦ star (f x)) =
      fun p ↦ star (cubeLiftTwo M hM f p) := by
  funext p
  simp only [cubeLiftTwo, cubeLiftOne, cubeLift, star_mul, star_star]
  ring

/-- Pointwise conjugation is antiunitary for the `L²` inner product. -/
lemma inner_lpStar_right
    (M : System.{u})
    (F G : Lp ℂ 2 M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ F
        (ForwardKroneckerFactor.lpStar M G) =
      star (@inner ℂ (Lp ℂ 2 M.μ) _
        (ForwardKroneckerFactor.lpStar M F) G) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, @inner ℂ ℂ _ (F x)
        (ForwardKroneckerFactor.lpStar M G x) ∂M.μ) =
        ∫ x, star (@inner ℂ ℂ _
          (ForwardKroneckerFactor.lpStar M F x) (G x)) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [
        ForwardKroneckerFactor.lpStar_coe M F,
        ForwardKroneckerFactor.lpStar_coe M G] with x hF hG
      rw [hF, hG]
      simp only [RCLike.inner_apply, starRingEnd_apply, star_mul, star_star]
      ring
    _ = star (∫ x, @inner ℂ ℂ _
        (ForwardKroneckerFactor.lpStar M F x) (G x) ∂M.μ) :=
      integral_conj

/-- `HasZeroHostKraU3` is invariant under pointwise complex conjugation. -/
theorem hasZeroHostKraU3_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU3 M hM f hf) :
    HasZeroHostKraU3 M hM (fun x ↦ star (f x)) hf.star := by
  let C := relativeCubeSystemTwo M hM
  let hC := relativeCubeSystemTwo_mps M hM
  let F := cubeLiftTwo M hM f
  let Fs := cubeLiftTwo M hM (fun x ↦ star (f x))
  let hF := cubeLiftTwo_memLp_two M hM f hf
  let hFs := cubeLiftTwo_memLp_two M hM (fun x ↦ star (f x)) hf.star
  let D := MultipleKhintchineCharacteristic.KData C hC
  let S : Submodule ℂ (Lp ℂ 2 C.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 C.μ →L[ℂ] Lp ℂ 2 C.μ)
  have hstarLp :
      hFs.toLp Fs =
        ForwardKroneckerFactor.lpStar C (hF.toLp F) := by
    apply Lp.ext
    filter_upwards [hFs.coeFn_toLp,
      ForwardKroneckerFactor.lpStar_coe C (hF.toLp F),
      hF.coeFn_toLp] with p hFsP hstarP hFP
    rw [hFsP, hstarP, hFP]
    exact congrFun (cubeLiftTwo_star M hM f) p
  have hprojF : S.starProjection (hF.toLp F) = 0 := by
    have hmean :=
      (hasZeroHostKraU3_iff_invariantMean M hM f hf).1 hzero
    rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection] at hmean
    exact hmean
  have hForth : hF.toLp F ∈ Sᗮ := by
    have hsub := S.sub_starProjection_mem_orthogonal (hF.toLp F)
    simpa only [hprojF, sub_zero] using hsub
  have hstarOrth :
      ForwardKroneckerFactor.lpStar C (hF.toLp F) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal]
    intro Y hY
    have hstarY : ForwardKroneckerFactor.lpStar C Y ∈ S := by
      change D.U (ForwardKroneckerFactor.lpStar C Y) =
        ForwardKroneckerFactor.lpStar C Y
      rw [← ForwardKroneckerFactor.lpStar_koopman C hC]
      change ForwardKroneckerFactor.lpStar C (D.U Y) =
        ForwardKroneckerFactor.lpStar C Y
      change D.U Y = Y at hY
      rw [hY]
    have hzeroInner :=
      hForth (ForwardKroneckerFactor.lpStar C Y) hstarY
    rw [inner_lpStar_right C Y (hF.toLp F), hzeroInner, star_zero]
  apply (hasZeroHostKraU3_iff_invariantMean
    M hM (fun x ↦ star (f x)) hf.star).2
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  change S.starProjection (hFs.toLp Fs) = 0
  rw [hstarLp]
  apply S.eq_starProjection_of_mem_orthogonal
  · exact S.zero_mem
  · simpa using hstarOrth

end Chapter02.HostKraU3Nullspace
