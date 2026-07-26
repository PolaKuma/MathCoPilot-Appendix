import Chapter02.HostKra.HostKraU3Nullspace

open Classical MeasureTheory

noncomputable section

namespace Chapter02.HostKraU4Nullspace

universe u

open HostKraCubeSeminorm HostKraStandardRelativeJoining

/-- The eight-vertex lift used in `U⁴` respects almost-everywhere equality
of bounded representatives. -/
lemma cubeLiftThree_congr_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    {f g : M.X → ℂ} (hfg : f =ᵐ[M.μ] g) :
    cubeLiftThree M hM f =ᵐ[(relativeCubeSystemThree M hM).μ]
      cubeLiftThree M hM g := by
  exact HostKraU3Nullspace.cubeLift_congr_ae
    (relativeCubeSystemTwo M hM)
    (relativeCubeSystemTwo_mps M hM)
    (HostKraU3Nullspace.cubeLiftTwo_congr_ae M hM hfg)

/-- The `U⁴` null condition depends only on the almost-everywhere class of
the bounded function. -/
theorem hasZeroHostKraU4_congr
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : MemLp f ⊤ M.μ) (hg : MemLp g ⊤ M.μ)
    (hfg : f =ᵐ[M.μ] g)
    (hzero : HasZeroHostKraU4 M hM f hf) :
    HasZeroHostKraU4 M hM g hg := by
  let C := relativeCubeSystemThree M hM
  let hC := relativeCubeSystemThree_mps M hM
  let F := cubeLiftThree M hM f
  let G := cubeLiftThree M hM g
  let hF := cubeLiftThree_memLp_two M hM f hf
  let hG := cubeLiftThree_memLp_two M hM g hg
  have hFG : hF.toLp F = hG.toLp G :=
    MemLp.toLp_congr hF hG (cubeLiftThree_congr_ae M hM hfg)
  apply (hasZeroHostKraU4_iff_invariantMean M hM g hg).2
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
    _ = 0 := (hasZeroHostKraU4_iff_invariantMean M hM f hf).1 hzero

/-- Three cube lifts turn multiplication on the base by `c` into
multiplication by a scalar independent of the cube vertex. -/
lemma cubeLiftThree_const_mul
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (f : M.X → ℂ) :
    cubeLiftThree M hM (fun x ↦ c * f x) =
      fun p ↦
        (((c * star c) * star (c * star c)) *
          star ((c * star c) * star (c * star c))) *
        cubeLiftThree M hM f p := by
  funext p
  simp only [cubeLiftThree, cubeLiftTwo, cubeLiftOne, cubeLift,
    star_mul]
  ring

/-- `HasZeroHostKraU4` is closed under complex scalar multiplication. -/
theorem hasZeroHostKraU4_const_mul
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM f hf)
    (c : ℂ) :
    HasZeroHostKraU4 M hM (fun x ↦ c * f x) (hf.const_mul c) := by
  let C := relativeCubeSystemThree M hM
  let hC := relativeCubeSystemThree_mps M hM
  let g := cubeLiftThree M hM f
  let gc := cubeLiftThree M hM (fun x ↦ c * f x)
  let hg := cubeLiftThree_memLp_two M hM f hf
  let hgc :=
    cubeLiftThree_memLp_two M hM (fun x ↦ c * f x) (hf.const_mul c)
  let a : ℂ :=
    ((c * star c) * star (c * star c)) *
      star ((c * star c) * star (c * star c))
  have hLp : hgc.toLp gc = a • hg.toLp g := by
    apply Lp.ext
    filter_upwards [hgc.coeFn_toLp, hg.coeFn_toLp,
      Lp.coeFn_smul a (hg.toLp g)] with p hcp hp hsp
    rw [hcp, hsp]
    change cubeLiftThree M hM (fun x ↦ c * f x) p =
      a * (hg.toLp (cubeLiftThree M hM f)) p
    rw [hp]
    exact congrFun (cubeLiftThree_const_mul M hM c f) p
  apply (hasZeroHostKraU4_iff_invariantMean
    M hM (fun x ↦ c * f x) (hf.const_mul c)).2
  apply HostKraU3Nullspace.invariantMeanLp_eq_zero_of_toLp_eq_smul
    C hC gc g hgc hg a hLp
  exact (hasZeroHostKraU4_iff_invariantMean M hM f hf).1 hzero

/-- Complex conjugation commutes with the eight-vertex cube lift. -/
lemma cubeLiftThree_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftThree M hM (fun x ↦ star (f x)) =
      fun p ↦ star (cubeLiftThree M hM f p) := by
  funext p
  simp only [cubeLiftThree, cubeLiftTwo, cubeLiftOne, cubeLift,
    star_mul, star_star]
  ring

/-- `HasZeroHostKraU4` is invariant under pointwise complex conjugation. -/
theorem hasZeroHostKraU4_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM f hf) :
    HasZeroHostKraU4 M hM (fun x ↦ star (f x)) hf.star := by
  let C := relativeCubeSystemThree M hM
  let hC := relativeCubeSystemThree_mps M hM
  let F := cubeLiftThree M hM f
  let Fs := cubeLiftThree M hM (fun x ↦ star (f x))
  let hF := cubeLiftThree_memLp_two M hM f hf
  let hFs := cubeLiftThree_memLp_two M hM (fun x ↦ star (f x)) hf.star
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
    exact congrFun (cubeLiftThree_star M hM f) p
  have hprojF : S.starProjection (hF.toLp F) = 0 := by
    have hmean :=
      (hasZeroHostKraU4_iff_invariantMean M hM f hf).1 hzero
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
    rw [HostKraU3Nullspace.inner_lpStar_right C Y (hF.toLp F),
      hzeroInner, star_zero]
  apply (hasZeroHostKraU4_iff_invariantMean
    M hM (fun x ↦ star (f x)) hf.star).2
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  change S.starProjection (hFs.toLp Fs) = 0
  rw [hstarLp]
  apply S.eq_starProjection_of_mem_orthogonal
  · exact S.zero_mem
  · simpa using hstarOrth

/-- The order-four null condition is exactly the order-three null condition
of the first cube lift on the first relative cube system. -/
theorem hasZeroHostKraU4_iff_cubeLiftOne_hasZeroHostKraU3
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    HasZeroHostKraU4 M hM f hf ↔
      HasZeroHostKraU3
        (relativeCubeSystemOne M hM)
        (relativeCubeSystemOne_mps M hM)
        (cubeLiftOne M hM f)
        (cubeLiftOne_memLp_top M hM f hf) := by
  rfl

end Chapter02.HostKraU4Nullspace
