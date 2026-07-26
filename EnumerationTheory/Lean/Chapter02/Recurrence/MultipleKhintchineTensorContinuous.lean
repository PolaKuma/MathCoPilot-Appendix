import Chapter02.Dynamics.CompactTwistedKernel
import Chapter02.Recurrence.MultipleKhintchineProductInvariant

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.MultipleKhintchineTensorContinuous

universe u

/-- An eigenkernel intertwines its Hilbert--Schmidt integral operator with
Koopman up to the same eigenvalue. -/
lemma kernelAction_koopman_ae_of_eigen
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ))
    (lam : ℂ)
    (hHeig :
      H ∘ productTransformation M =ᵐ[M.μ.prod M.μ]
        fun p ↦ lam * H p)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    (fun x ↦ kernelAction M H f (M.T x)) =ᵐ[M.μ]
      fun x ↦ lam * kernelAction M H (fun y ↦ f (M.T y)) x := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hslice :
      ∀ᵐ x ∂M.μ, AEStronglyMeasurable (fun y ↦ H (x, y)) M.μ :=
    hH.1.prodMk_left
  have hsliceT :
      ∀ᵐ x ∂M.μ, AEStronglyMeasurable (fun y ↦ H (M.T x, y)) M.μ := by
    simpa only using hM.2.quasiMeasurePreserving.ae hslice
  have heig :
      ∀ᵐ x ∂M.μ, ∀ᵐ y ∂M.μ,
        H (M.T x, M.T y) = lam * H (x, y) := by
    have h := Measure.ae_ae_of_ae_prod hHeig
    simpa only [Function.comp_apply, productTransformation] using h
  filter_upwards [hsliceT, heig] with x hxmeas hxeq
  simp only [kernelAction]
  calc
    (∫ y, H (M.T x, y) * f y ∂M.μ) =
        ∫ y, H (M.T x, M.T y) * f (M.T y) ∂M.μ := by
      symm
      exact
        HilbertSchmidtInvariant.integral_comp_measurePreserving M.T hM.2
        (fun y ↦ H (M.T x, y) * f y) (hxmeas.mul hf.1)
    _ = ∫ y, (lam * H (x, y)) * f (M.T y) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [hxeq] with y hy
      rw [hy]
    _ = lam * ∫ y, H (x, y) * f (M.T y) ∂M.μ := by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring

/-- Operator-level form of the eigenkernel intertwining identity. -/
lemma kernelOperator_twisted_commutes_koopman
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ))
    (lam : ℂ)
    (hHeig :
      H ∘ productTransformation M =ᵐ[M.μ.prod M.μ]
        fun p ↦ lam * H p)
    (F : Lp ℂ 2 M.μ) :
    (WeakSpectrum.koopmanData M hM).U
        (HilbertSchmidtConsequences.kernelOperator M hM H hH F) =
      lam • HilbertSchmidtConsequences.kernelOperator M hM H hH
        ((WeakSpectrum.koopmanData M hM).U F) := by
  let UF : Lp ℂ 2 M.μ := (WeakSpectrum.koopmanData M hM).U F
  let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM H hH F (Lp.memLp F)
  let hKUF := HilbertSchmidtConsequences.kernelAction_memLp_two
    M hM H hH (fun x ↦ UF x) (Lp.memLp UF)
  have hUcoe :
      (fun x ↦ UF x) =ᵐ[M.μ] fun x ↦ F (M.T x) :=
    Lp.coeFn_compMeasurePreserving F hM.2
  have hraw :=
    kernelAction_koopman_ae_of_eigen
      M hM H hH lam hHeig F (Lp.memLp F)
  have hcongr :
      kernelAction M H (fun x ↦ UF x) =
        kernelAction M H (fun x ↦ F (M.T x)) :=
    HilbertSchmidtConsequences.kernelAction_congr_ae M H hUcoe
  have hKFcoeT :
      (fun x ↦ (hKF.toLp (kernelAction M H F)) (M.T x)) =ᵐ[M.μ]
        fun x ↦ kernelAction M H F (M.T x) := by
    simpa only [Function.comp_apply] using
      hM.2.quasiMeasurePreserving.ae_eq_comp hKF.coeFn_toLp
  rw [HilbertSchmidtConsequences.kernelOperator_apply,
    HilbertSchmidtConsequences.kernelOperator_apply]
  apply Lp.ext (μ := M.μ)
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH F) hM.2,
    hKFcoeT, hKUF.coeFn_toLp,
    Lp.coeFn_smul lam
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH UF),
    hraw] with x hleft hKFcoe hKUFcoe hsmul hrawx
  change
    (Lp.compMeasurePreserving M.T hM.2
      (HilbertSchmidtConsequences.kernelLinearMap M hM H hH F)) x =
      (lam •
        HilbertSchmidtConsequences.kernelLinearMap M hM H hH UF) x
  rw [hleft, hsmul]
  change
    (hKF.toLp (kernelAction M H F)) (M.T x) =
      lam * (hKUF.toLp
        (kernelAction M H (fun x ↦ UF x))) x
  rw [hKFcoe, hKUFcoe, hcongr, hrawx]

/-- Applying an eigenkernel to an `L²` function produces an almost-periodic
Koopman vector. -/
lemma kernelAction_toLp_almostPeriodic_of_eigen
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ))
    (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hHeig :
      H ∘ productTransformation M =ᵐ[M.μ.prod M.μ]
        fun p ↦ lam * H p)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM)
      ((HilbertSchmidtConsequences.kernelAction_memLp_two
        M hM H hH f hf).toLp (kernelAction M H f)) := by
  let F : Lp ℂ 2 M.μ := hf.toLp f
  let K : Lp ℂ 2 M.μ :=
    HilbertSchmidtConsequences.kernelOperator M hM H hH F
  have hKap : IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM) K := by
    apply
      HilbertSchmidtConsequences.compact_twistedCommutant_range_almostPeriodic
        (WeakSpectrum.koopmanData M hM)
        (fun X ↦ (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
        (HilbertSchmidtConsequences.kernelOperator M hM H hH)
        (SeparatedKernelDensity.kernelOperator_hasCompactClosedBallImage
          M hM H hH)
        lam hlam
    exact kernelOperator_twisted_commutes_koopman
      M hM H hH lam hHeig
  have hFraw : (fun x ↦ F x) =ᵐ[M.μ] f := hf.coeFn_toLp
  have haction :
      kernelAction M H (fun x ↦ F x) = kernelAction M H f :=
    HilbertSchmidtConsequences.kernelAction_congr_ae M H hFraw
  have hK :
      K =
        (HilbertSchmidtConsequences.kernelAction_memLp_two
          M hM H hH f hf).toLp (kernelAction M H f) := by
    apply Lp.ext (μ := M.μ)
    change
      (fun x ↦
        (HilbertSchmidtConsequences.kernelOperator M hM H hH F) x)
          =ᵐ[M.μ]
        (fun x ↦
          ((HilbertSchmidtConsequences.kernelAction_memLp_two
            M hM H hH f hf).toLp (kernelAction M H f)) x)
    rw [HilbertSchmidtConsequences.kernelOperator_apply]
    let hKF := HilbertSchmidtConsequences.kernelAction_memLp_two
      M hM H hH F (Lp.memLp F)
    change
      (fun x ↦ (hKF.toLp (kernelAction M H F)) x) =ᵐ[M.μ]
        fun x ↦
          ((HilbertSchmidtConsequences.kernelAction_memLp_two
            M hM H hH f hf).toLp (kernelAction M H f)) x
    exact hKF.coeFn_toLp.trans
      ((EventuallyEq.of_eq haction).trans
        (HilbertSchmidtConsequences.kernelAction_memLp_two
          M hM H hH f hf).coeFn_toLp.symm)
  rw [← hK]
  exact hKap

/-- A continuous-spectral vector has tensor-conjugate square orthogonal to
every product-system eigenkernel. -/
theorem inner_tensorSquare_eigen_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f))
    (H : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ))
    (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hHeig :
      H ∘ productTransformation M =ᵐ[M.μ.prod M.μ]
        fun p ↦ lam * H p) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        ((HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
          (TensorSquare M f))
        (hH.toLp H) = 0 := by
  change
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        ((HilbertSchmidtInvariant.memLp_separatedProduct
          M hM f (fun x ↦ star (f x)) hf hf.star).toLp
          (fun p : M.X × M.X ↦ f p.1 * star (f p.2)))
        (hH.toLp H) = 0
  rw [HilbertSchmidtInvariant.inner_separatedProduct_kernel
    M hM H hH f (fun x ↦ star (f x)) hf hf.star]
  have hap :
      IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM)
        ((HilbertSchmidtConsequences.kernelAction_memLp_two
          M hM H hH
            (fun y ↦ star (star (f y))) hf.star.star).toLp
          (kernelAction M H (fun y ↦ star (star (f y))))) :=
    kernelAction_toLp_almostPeriodic_of_eigen
      M hM H hH lam hlam hHeig
        (fun y ↦ star (star (f y))) hf.star.star
  have hinput :
      (fun y ↦ star (star (f y))) = f := by
    funext y
    simp
  simpa only [hinput] using
    AlmostPeriodicIsometry.continuous_inner_almostPeriodic_eq_zero
      (WeakSpectrum.koopmanData M hM)
      (fun F ↦
        (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map F)
      (hf.toLp f)
      ((HilbertSchmidtConsequences.kernelAction_memLp_two
        M hM H hH f hf).toLp (kernelAction M H f))
      hcont (by simpa only [hinput] using hap)

/-- The tensor-conjugate square of a continuous-spectral vector is itself
continuous-spectral for the Cartesian-square Koopman isometry. -/
theorem tensorSquare_continuous
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f)) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
        (TensorSquare M f)
    InContinuousSpectralSubspace
      (WeakSpectrum.koopmanData P hP) Y := by
  dsimp only
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let Y : Lp ℂ 2 P.μ :=
    (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
      (TensorSquare M f)
  change
    ∀ Z : Lp ℂ 2 P.μ,
      IsEigenvector (WeakSpectrum.koopmanData P hP) Z →
        @inner ℂ (Lp ℂ 2 P.μ) _ Y Z = 0
  intro Z hZ
  obtain ⟨hZ0, lam, hZeig⟩ := hZ
  have hlam : ‖lam‖ = 1 :=
    AlmostPeriodicIsometry.eigenvalue_norm_one
      (WeakSpectrum.koopmanData P hP)
      (fun W ↦ (Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2).norm_map W)
      Z hZ0 lam hZeig
  have hcoe := Lp.coeFn_compMeasurePreserving Z hP.2
  have hsmul := Lp.coeFn_smul lam Z
  have hraw :
      (fun p : M.X × M.X ↦ Z (productTransformation M p))
          =ᵐ[M.μ.prod M.μ]
        fun p ↦ lam * Z p := by
    change
      (fun p : P.X ↦ Z (P.T p)) =ᵐ[P.μ]
        fun p ↦ lam * Z p
    change
      Lp.compMeasurePreserving P.T hP.2 Z = lam • Z at hZeig
    rw [hZeig] at hcoe
    exact hcoe.symm.trans (by
      simpa only [Pi.smul_apply, smul_eq_mul] using hsmul)
  have hinner :=
    inner_tensorSquare_eigen_eq_zero
      M hM f hf hcont (fun p ↦ Z p) (Lp.memLp Z)
        lam hlam (by
          simpa only [P, ProductWeakMixing.productSystem,
            productTransformation, Function.comp_apply] using hraw)
  have htoLp :
      (Lp.memLp Z).toLp (fun p ↦ Z p) = Z := by
    apply Lp.ext (μ := P.μ)
    exact (Lp.memLp Z).coeFn_toLp
  rw [← htoLp]
  simpa only [Y, P] using hinner

end Chapter02.MultipleKhintchineTensorContinuous
