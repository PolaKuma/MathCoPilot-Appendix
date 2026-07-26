import Chapter02.HostKra.HostKraCubeRelative
import Chapter02.Spectral.HilbertSchmidtInvariant
import Chapter02.Recurrence.MultipleKhintchineCartesian

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.HostKraCartesianCube

universe u

/-- The tensor-conjugate square of an `L²` vector, as an `L²` vector on the
ordinary Cartesian-square system. -/
def cartesianSquareLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    Lp ℂ 2 (MultipleKhintchineCartesian.productSystem M M).μ :=
  (HilbertSchmidtInvariant.tensorSquare_memLp
    M hM (fun x ↦ F x) (Lp.memLp F)).toLp
      (MultipleKhintchineCartesian.cartesianSquare (fun x ↦ F x))

lemma cartesianSquareLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    (fun p ↦ cartesianSquareLp M hM F p) =ᵐ[M.μ.prod M.μ]
      MultipleKhintchineCartesian.cartesianSquare (fun x ↦ F x) := by
  exact
    (HilbertSchmidtInvariant.tensorSquare_memLp
      M hM (fun x ↦ F x) (Lp.memLp F)).coeFn_toLp

lemma cartesianSquareLp_memLp_top
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ) :
    MemLp (fun p ↦ cartesianSquareLp M hM F p) ⊤
      (MultipleKhintchineCartesian.productSystem M M).μ := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hraw :
      MemLp
        (MultipleKhintchineCartesian.cartesianSquare (fun x ↦ F x))
        ⊤ (M.μ.prod M.μ) := by
    simpa only [MultipleKhintchineCartesian.cartesianSquare] using
      (hFtop.star.comp_snd M.μ).mul (r := ⊤) (hFtop.comp_fst M.μ)
  exact hraw.ae_eq (cartesianSquareLp_coe M hM F).symm

/-- Cartesian squaring commutes with the first multiplicative cube
derivative.  This is the algebraic bridge from a base-system derivative to
the diagonal Koopman action on the first Cartesian cube. -/
theorem cubeDerivative_cartesianSquare_ae_eq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    HostKraCubeTwo.cubeDerivative P hP
        (cartesianSquareLp M hM F) n =ᵐ[P.μ]
      MultipleKhintchineCartesian.cartesianSquare
        (HostKraCubeTwo.cubeDerivative M hM F n) := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Y := cartesianSquareLp M hM F
  have hder :=
    HostKraCubeTwo.cubeDerivative_ae_eq P hP Y n
  have hY := cartesianSquareLp_coe M hM F
  have hYshift :=
    (hP.2.iterate n).quasiMeasurePreserving.ae_eq_comp hY
  have hbase :=
    HostKraCubeTwo.cubeDerivative_ae_eq M hM F n
  have hbaseFst :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq_comp hbase
  have hbaseSnd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq_comp hbase
  filter_upwards [hder, hY, hYshift, hbaseFst, hbaseSnd] with
      p hderp hYp hYshiftp hbaseFstp hbaseSndp
  rw [hderp]
  change
    Y (((P.T)^[n]) p) * star (Y p) =
      HostKraCubeTwo.cubeDerivative M hM F n p.1 *
        star (HostKraCubeTwo.cubeDerivative M hM F n p.2)
  have hYshiftp' :
      Y (((P.T)^[n]) p) =
        MultipleKhintchineCartesian.cartesianSquare
          (fun x ↦ F x) (((P.T)^[n]) p) := by
    simpa only [Function.comp_apply] using hYshiftp
  change
    HostKraCubeTwo.cubeDerivative M hM F n p.1 =
      F ((M.T^[n]) p.1) * star (F p.1) at hbaseFstp
  change
    HostKraCubeTwo.cubeDerivative M hM F n p.2 =
      F ((M.T^[n]) p.2) * star (F p.2) at hbaseSndp
  rw [hYshiftp', hYp, hbaseFstp, hbaseSndp]
  rw [show (P.T^[n]) p =
      ((M.T^[n]) p.1, (M.T^[n]) p.2) by
    exact MultipleKhintchineCartesian.product_iter M M n p]
  simp only [MultipleKhintchineCartesian.cartesianSquare,
    starRingEnd_apply, star_mul, star_star]
  ring

/-- The canonical `L²` tensor square of a first derivative on the base
system. -/
def cartesianDerivativeLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    Lp ℂ 2 (MultipleKhintchineCartesian.productSystem M M).μ :=
  let D := HostKraCubeTwo.cubeDerivative M hM F n
  let hD := HostKraCubeTwo.cubeDerivative_memLp M hM F hFtop n
  (HilbertSchmidtInvariant.tensorSquare_memLp M hM D hD).toLp
    (MultipleKhintchineCartesian.cartesianSquare D)

/-- The derivative of the tensor-square input on the product system and the
tensor square of the base derivative define the same `L²` vector. -/
theorem cubeDerivative_cartesianSquare_toLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let Y := cartesianSquareLp M hM F
    let hYtop := cartesianSquareLp_memLp_top M hM F hFtop
    (HostKraCubeTwo.cubeDerivative_memLp P hP Y hYtop n).toLp
        (HostKraCubeTwo.cubeDerivative P hP Y n) =
      cartesianDerivativeLp M hM F hFtop n := by
  dsimp only
  apply Lp.ext
  exact
    (HostKraCubeTwo.cubeDerivative_memLp
      (MultipleKhintchineCartesian.productSystem M M)
      (MultipleKhintchineCartesian.productSystem_mps M M hM hM)
      (cartesianSquareLp M hM F)
      (cartesianSquareLp_memLp_top M hM F hFtop) n).coeFn_toLp
      |>.trans (cubeDerivative_cartesianSquare_ae_eq M hM F n)
      |>.trans
        ((HilbertSchmidtInvariant.tensorSquare_memLp M hM
          (HostKraCubeTwo.cubeDerivative M hM F n)
          (HostKraCubeTwo.cubeDerivative_memLp
            M hM F hFtop n)).coeFn_toLp.symm)

/-- The first nontrivial Host--Kra object available in the current project:
the tensor square of a base derivative, projected to the diagonal Koopman
fixed subspace of the ordinary Cartesian square. -/
def firstCubeInvariantLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    Lp ℂ 2 (MultipleKhintchineCartesian.productSystem M M).μ :=
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Y := cartesianSquareLp M hM F
  let hYtop := cartesianSquareLp_memLp_top M hM F hFtop
  HostKraRelativeMean.invariantMeanLp P hP
    (HostKraCubeTwo.cubeDerivative P hP Y n)
    (HostKraCubeTwo.cubeDerivative_memLp P hP Y hYtop n)

theorem firstCubeInvariantLp_eq_fixedProjection
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
    let D := MultipleKhintchineCharacteristic.KData P hP
    let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
      LinearMap.eqLocus D.U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
    firstCubeInvariantLp M hM F hFtop n =
      (S.orthogonalProjection
        (cartesianDerivativeLp M hM F hFtop n) : Lp ℂ 2 P.μ) := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Y := cartesianSquareLp M hM F
  let hYtop := cartesianSquareLp_memLp_top M hM F hFtop
  let hD :=
    HostKraCubeTwo.cubeDerivative_memLp P hP Y hYtop n
  have hmean :=
    HostKraRelativeMean.invariantMeanLp_eq_fixedProjection P hP
      (HostKraCubeTwo.cubeDerivative P hP Y n) hD
  have hinput :
      hD.toLp (HostKraCubeTwo.cubeDerivative P hP Y n) =
        cartesianDerivativeLp M hM F hFtop n := by
    simpa only [P, hP, Y, hYtop, hD] using
      cubeDerivative_cartesianSquare_toLp M hM F hFtop n
  rw [hinput] at hmean
  simpa only [firstCubeInvariantLp, P, hP, Y, hYtop, hD] using hmean

/-- Four vertices on the Cartesian-square input are the tensor-conjugate
square of the corresponding four vertices on the base system. -/
theorem cubeTwoIntegrand_cartesianSquare_ae_eq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n m : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let Y := cartesianSquareLp M hM F
    HostKraCubeTwo.cubeTwoIntegrand P Y n m =ᵐ[P.μ]
      MultipleKhintchineCartesian.cartesianSquare
        (HostKraCubeTwo.cubeTwoIntegrand M F n m) := by
  dsimp only
  let P := MultipleKhintchineCartesian.productSystem M M
  let hP := MultipleKhintchineCartesian.productSystem_mps M M hM hM
  let Y := cartesianSquareLp M hM F
  have hY := cartesianSquareLp_coe M hM F
  have hYshift (r : ℕ) :
      (fun p ↦ Y p) ∘ (P.T^[r]) =ᵐ[P.μ]
        MultipleKhintchineCartesian.cartesianSquare
          (fun x ↦ F x) ∘ (P.T^[r]) :=
    (hP.2.iterate r).quasiMeasurePreserving.ae_eq_comp hY
  filter_upwards [hYshift (n + m), hYshift m, hYshift n, hY] with
      p hnm hm hn hzero
  change
    Y ((P.T^[n + m]) p) * star (Y ((P.T^[m]) p)) *
        star (Y ((P.T^[n]) p)) * Y p =
      MultipleKhintchineCartesian.cartesianSquare
        (HostKraCubeTwo.cubeTwoIntegrand M F n m) p
  change
    Y ((P.T^[n + m]) p) =
      MultipleKhintchineCartesian.cartesianSquare
        (fun x ↦ F x) ((P.T^[n + m]) p) at hnm
  change
    Y ((P.T^[m]) p) =
      MultipleKhintchineCartesian.cartesianSquare
        (fun x ↦ F x) ((P.T^[m]) p) at hm
  change
    Y ((P.T^[n]) p) =
      MultipleKhintchineCartesian.cartesianSquare
        (fun x ↦ F x) ((P.T^[n]) p) at hn
  rw [hnm, hm, hn, hzero]
  simp only [P, MultipleKhintchineCartesian.product_iter,
    MultipleKhintchineCartesian.cartesianSquare,
    HostKraCubeTwo.cubeTwoIntegrand, starRingEnd_apply,
    star_mul, star_star]
  ring

/-- The product-system four-vertex integral is exactly the squared modulus
of the base-system four-vertex integral. -/
theorem norm_integral_cubeTwo_sq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n m : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let Y := cartesianSquareLp M hM F
    ‖∫ x, HostKraCubeTwo.cubeTwoIntegrand M F n m x ∂M.μ‖ ^ 2 =
      (∫ p, HostKraCubeTwo.cubeTwoIntegrand P Y n m p ∂P.μ).re := by
  dsimp only
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [← MultipleKhintchineCartesian.re_integral_cartesianSquare_eq_norm_sq
    M.μ (HostKraCubeTwo.cubeTwoIntegrand M F n m)]
  apply congrArg Complex.re
  apply integral_congr_ae
  exact (cubeTwoIntegrand_cartesianSquare_ae_eq M hM F n m).symm

/-- The complex-valued form of `norm_integral_cubeTwo_sq`: the product
four-vertex integral itself is the real scalar `‖∫ cubeTwoIntegrand‖²`.
This is the termwise identity needed to rewrite Cartesian-cube Cesàro
energies entirely on the base system. -/
theorem integral_cubeTwo_cartesian_eq_norm_sq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (n m : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let Y := cartesianSquareLp M hM F
    ∫ p, HostKraCubeTwo.cubeTwoIntegrand P Y n m p ∂P.μ =
      ((‖∫ x, HostKraCubeTwo.cubeTwoIntegrand M F n m x ∂M.μ‖ ^ 2 : ℝ) : ℂ) := by
  dsimp only
  letI : IsProbabilityMeasure M.μ := hM.1
  calc
    (∫ p, HostKraCubeTwo.cubeTwoIntegrand
        (MultipleKhintchineCartesian.productSystem M M)
        (cartesianSquareLp M hM F) n m p
        ∂(MultipleKhintchineCartesian.productSystem M M).μ) =
        ∫ p, MultipleKhintchineCartesian.cartesianSquare
          (HostKraCubeTwo.cubeTwoIntegrand M F n m) p ∂M.μ.prod M.μ := by
          apply integral_congr_ae
          exact cubeTwoIntegrand_cartesianSquare_ae_eq M hM F n m
    _ = (∫ x, HostKraCubeTwo.cubeTwoIntegrand M F n m x ∂M.μ) *
          (starRingEnd ℂ)
            (∫ x, HostKraCubeTwo.cubeTwoIntegrand M F n m x ∂M.μ) :=
      MultipleKhintchineCartesian.integral_cartesianSquare M.μ
        (HostKraCubeTwo.cubeTwoIntegrand M F n m)
    _ = ((‖∫ x, HostKraCubeTwo.cubeTwoIntegrand M F n m x ∂M.μ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Relative four-vertex energy recursion on the first Cartesian cube.  Its
limit is the energy of the diagonal fixed-space projection identified by
`firstCubeInvariantLp_eq_fixedProjection`. -/
theorem cartesianCubeTwo_uniform_energy_limit
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let Y := cartesianSquareLp M hM F
    let I := firstCubeInvariantLp M hM F hFtop n
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              ∫ p,
                HostKraCubeTwo.cubeTwoIntegrand P Y n (i + m) p
                ∂P.μ)
          (@inner ℂ (Lp ℂ 2 P.μ) _ I I) < ε := by
  dsimp only
  simpa only [firstCubeInvariantLp] using
    (HostKraCubeRelative.cubeTwo_relative_uniform_energy_limit
      (MultipleKhintchineCartesian.productSystem M M)
      (MultipleKhintchineCartesian.productSystem_mps M M hM hM)
      (cartesianSquareLp M hM F)
      (cartesianSquareLp_memLp_top M hM F hFtop) n)

/-- Base-space form of the first Cartesian-cube energy recursion.  The
uniform Cesàro averages of squared four-vertex integrals converge to the
energy of the diagonal invariant projection on the Cartesian square. -/
theorem baseCubeTwo_meanSquare_uniform_energy_limit
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    let P := MultipleKhintchineCartesian.productSystem M M
    let I := firstCubeInvariantLp M hM F hFtop n
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              ((‖∫ x,
                  HostKraCubeTwo.cubeTwoIntegrand M F n (i + m) x
                  ∂M.μ‖ ^ 2 : ℝ) : ℂ))
          (@inner ℂ (Lp ℂ 2 P.μ) _ I I) < ε := by
  dsimp only
  simpa only [integral_cubeTwo_cartesian_eq_norm_sq] using
    (cartesianCubeTwo_uniform_energy_limit M hM F hFtop n)

/-- Vanishing of the diagonal fixed-space component forces the translated
mean-square four-vertex energy to vanish uniformly.  This is the checked
zero-energy interface needed by a future `Z₂` characteristic-factor layer. -/
theorem baseCubeTwo_meanSquare_uniform_zero_limit
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ)
    (hzero : firstCubeInvariantLp M hM F hFtop n = 0) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ m ∈ Finset.range N,
              ((‖∫ x,
                  HostKraCubeTwo.cubeTwoIntegrand M F n (i + m) x
                  ∂M.μ‖ ^ 2 : ℝ) : ℂ))
          0 < ε := by
  simpa only [hzero, inner_zero_right] using
    (baseCubeTwo_meanSquare_uniform_energy_limit M hM F hFtop n)

end Chapter02.HostKraCartesianCube
