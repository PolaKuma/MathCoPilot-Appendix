import Chapter02.Spectral.HilbertSchmidtInvariant
import Chapter02.Recurrence.Khintchine
import Chapter02.Recurrence.MultipleKhintchineCartesian
import Chapter02.Recurrence.ForwardKroneckerFactor

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02.MultipleKhintchineProductInvariant

universe u

/-- The canonical separated tensor of two `L²` vectors on the Cartesian
square.  Keeping this construction at the `Lp` level makes the spectral
approximation argument independent of chosen representatives. -/
def separatedProductLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ) :
    Lp ℂ 2 (M.μ.prod M.μ) :=
  (HilbertSchmidtInvariant.memLp_separatedProduct
    M hM (fun x ↦ F x) (fun x ↦ G x) (Lp.memLp F) (Lp.memLp G)).toLp
      (fun p : M.X × M.X ↦ F p.1 * G p.2)

lemma separatedProductLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ) :
    (fun p ↦ separatedProductLp M hM F G p) =ᵐ[M.μ.prod M.μ]
      fun p : M.X × M.X ↦ F p.1 * G p.2 :=
  (HilbertSchmidtInvariant.memLp_separatedProduct
    M hM (fun x ↦ F x) (fun x ↦ G x) (Lp.memLp F) (Lp.memLp G)).coeFn_toLp

/-- Inner products of separated tensors factor into the two coordinate
inner products. -/
theorem inner_separatedProductLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H K : Lp ℂ 2 M.μ) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        (separatedProductLp M hM F G)
        (separatedProductLp M hM H K) =
      @inner ℂ (Lp ℂ 2 M.μ) _ F H *
        @inner ℂ (Lp ℂ 2 M.μ) _ G K := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  calc
    (∫ p,
        @inner ℂ ℂ _
          (separatedProductLp M hM F G p)
          (separatedProductLp M hM H K p) ∂M.μ.prod M.μ) =
        ∫ p : M.X × M.X,
          (star (F p.1) * H p.1) *
            (star (G p.2) * K p.2) ∂M.μ.prod M.μ := by
      apply integral_congr_ae
      filter_upwards [
        separatedProductLp_coe M hM F G,
        separatedProductLp_coe M hM H K] with p hFG hHK
      rw [hFG, hHK]
      simp only [RCLike.inner_apply, starRingEnd_apply, star_mul]
      ring
    _ = (∫ x, star (F x) * H x ∂M.μ) *
          ∫ y, star (G y) * K y ∂M.μ := by
      exact integral_prod_mul
        (fun x ↦ star (F x) * H x)
        (fun y ↦ star (G y) * K y)
    _ = _ := by
      simp only [RCLike.inner_apply, starRingEnd_apply]
      congr 1 <;>
        apply integral_congr_ae <;>
        filter_upwards with x <;>
        ring

/-- The Hilbert norm of a separated tensor is the product of the two
factor norms. -/
theorem norm_separatedProductLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ) :
    ‖separatedProductLp M hM F G‖ = ‖F‖ * ‖G‖ := by
  have hsquare :
      ‖separatedProductLp M hM F G‖ ^ 2 =
        (‖F‖ * ‖G‖) ^ 2 := by
    have hFinner := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) F
    have hGinner := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) G
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_separatedProductLp, hFinner, hGinner]
    norm_num
    norm_cast
    ring
  nlinarith [norm_nonneg (separatedProductLp M hM F G),
    norm_nonneg F, norm_nonneg G, mul_nonneg (norm_nonneg F) (norm_nonneg G)]

theorem separatedProductLp_add_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F H G : Lp ℂ 2 M.μ) :
    separatedProductLp M hM (F + H) G =
      separatedProductLp M hM F G + separatedProductLp M hM H G := by
  apply Lp.ext
  have hFH :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq (Lp.coeFn_add F H)
  filter_upwards [
    separatedProductLp_coe M hM (F + H) G,
    separatedProductLp_coe M hM F G,
    separatedProductLp_coe M hM H G,
    Lp.coeFn_add (separatedProductLp M hM F G)
      (separatedProductLp M hM H G),
    hFH] with p hl hF hH hr hbase
  rw [hl, hr]
  change (F + H) p.1 * G p.2 =
    separatedProductLp M hM F G p +
      separatedProductLp M hM H G p
  rw [hF, hH]
  change (F + H) p.1 = F p.1 + H p.1 at hbase
  rw [hbase]
  ring

theorem separatedProductLp_add_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G K : Lp ℂ 2 M.μ) :
    separatedProductLp M hM F (G + K) =
      separatedProductLp M hM F G + separatedProductLp M hM F K := by
  apply Lp.ext
  have hGK :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq (Lp.coeFn_add G K)
  filter_upwards [
    separatedProductLp_coe M hM F (G + K),
    separatedProductLp_coe M hM F G,
    separatedProductLp_coe M hM F K,
    Lp.coeFn_add (separatedProductLp M hM F G)
      (separatedProductLp M hM F K),
    hGK] with p hl hG hK hr hbase
  rw [hl, hr]
  change F p.1 * (G + K) p.2 =
    separatedProductLp M hM F G p +
      separatedProductLp M hM F K p
  rw [hG, hK]
  change (G + K) p.2 = G p.2 + K p.2 at hbase
  rw [hbase]
  ring

theorem separatedProductLp_smul_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (F G : Lp ℂ 2 M.μ) :
    separatedProductLp M hM (c • F) G =
      c • separatedProductLp M hM F G := by
  apply Lp.ext
  have hcF :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq (Lp.coeFn_smul c F)
  filter_upwards [
    separatedProductLp_coe M hM (c • F) G,
    separatedProductLp_coe M hM F G,
    Lp.coeFn_smul c (separatedProductLp M hM F G),
    hcF] with p hl hF hr hbase
  rw [hl, hr]
  change (c • F) p.1 * G p.2 =
    c * separatedProductLp M hM F G p
  rw [hF]
  change (c • F) p.1 = c * F p.1 at hbase
  rw [hbase]
  ring

theorem separatedProductLp_smul_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (F G : Lp ℂ 2 M.μ) :
    separatedProductLp M hM F (c • G) =
      c • separatedProductLp M hM F G := by
  apply Lp.ext
  have hcG :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq (Lp.coeFn_smul c G)
  filter_upwards [
    separatedProductLp_coe M hM F (c • G),
    separatedProductLp_coe M hM F G,
    Lp.coeFn_smul c (separatedProductLp M hM F G),
    hcG] with p hl hG hr hbase
  rw [hl, hr]
  change F p.1 * (c • G) p.2 =
    c * separatedProductLp M hM F G p
  rw [hG]
  change (c • G) p.2 = c * G p.2 at hbase
  rw [hbase]
  ring

/-- Pointwise conjugation distributes over a separated tensor. -/
lemma lpStar_separatedProductLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ) :
    ForwardKroneckerFactor.lpStar
        (MultipleKhintchineCartesian.productSystem M M)
        (separatedProductLp M hM F G) =
      separatedProductLp M hM
        (ForwardKroneckerFactor.lpStar M F)
        (ForwardKroneckerFactor.lpStar M G) := by
  apply Lp.ext
  have hFstar :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq
        (ForwardKroneckerFactor.lpStar_coe M F)
  have hGstar :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq
        (ForwardKroneckerFactor.lpStar_coe M G)
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe
      (MultipleKhintchineCartesian.productSystem M M)
      (separatedProductLp M hM F G),
    separatedProductLp_coe M hM F G,
    separatedProductLp_coe M hM
      (ForwardKroneckerFactor.lpStar M F)
      (ForwardKroneckerFactor.lpStar M G),
    hFstar, hGstar] with p hout hin hr hF hG
  change
    ForwardKroneckerFactor.lpStar M F p.1 = star (F p.1) at hF
  change
    ForwardKroneckerFactor.lpStar M G p.2 = star (G p.2) at hG
  rw [hout, hin, hr, hF, hG, star_mul]
  ring

/-- An `Lp` Koopman eigen-relation written for the canonical pointwise
representative. -/
lemma koopmanEigenrelation_ae
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (lam : ℂ)
    (hFeig : (WeakSpectrum.koopmanData M hM).U F = lam • F) :
    (fun x ↦ F (M.T x)) =ᵐ[M.μ] fun x ↦ lam * F x := by
  have hcomp := Lp.coeFn_compMeasurePreserving F hM.2
  have hsmul := Lp.coeFn_smul lam F
  change Lp.compMeasurePreserving M.T hM.2 F = lam • F at hFeig
  have heq :
      (fun x ↦
        (show Lp ℂ 2 M.μ from
          Lp.compMeasurePreserving M.T hM.2 F) x) =ᵐ[M.μ]
        fun x ↦ (lam • F) x := by rw [hFeig]
  filter_upwards [hcomp, hsmul, heq] with x hc hs he
  rw [hc, hs] at he
  exact he

/-- Ergodicity makes every nonzero `Lp` Koopman eigenspace
one-dimensional. -/
theorem same_koopmanEigenvalue_proportional
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ) (lam : ℂ)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hFeig : (WeakSpectrum.koopmanData M hM).U F = lam • F)
    (hGeig : (WeakSpectrum.koopmanData M hM).U G = lam • G) :
    ∃ c : ℂ, F = c • G := by
  have hFraw := koopmanEigenrelation_ae M hM F lam hFeig
  have hGraw := koopmanEigenrelation_ae M hM G lam hGeig
  have hFae0 : ¬ (fun x ↦ F x) =ᵐ[M.μ] 0 := by
    intro hzero
    apply hF0
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℂ 2 M.μ).symm
  have hGae0 : ¬ (fun x ↦ G x) =ᵐ[M.μ] 0 := by
    intro hzero
    apply hG0
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℂ 2 M.μ).symm
  obtain ⟨c, hc⟩ :=
    Section05.same_eigenvalue_proportional M hErg lam
      (fun x ↦ F x) (fun x ↦ G x)
      ⟨Lp.memLp F, hFae0, by
        simpa only [Chapter01.koopman, Function.comp_def] using hFraw⟩
      ⟨Lp.memLp G, hGae0, by
        simpa only [Chapter01.koopman, Function.comp_def] using hGraw⟩
  refine ⟨c, ?_⟩
  apply Lp.ext
  filter_upwards [hc, Lp.coeFn_smul c G] with x hx hsmul
  rw [hsmul]
  exact hx

lemma koopmanEigenvalue_norm_one
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (lam : ℂ)
    (hF0 : F ≠ 0)
    (hFeig : (WeakSpectrum.koopmanData M hM).U F = lam • F) :
    ‖lam‖ = 1 := by
  exact
    AlmostPeriodicIsometry.eigenvalue_norm_one
      (WeakSpectrum.koopmanData M hM)
      (fun X ↦ (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X)
      F hF0 lam hFeig

/-- Distinct nonzero Koopman eigenvectors are orthogonal in `L²`.
This is the intrinsic `Lp` wrapper around the representative-level
orthogonality theorem from Section 5. -/
theorem koopmanEigenvectors_inner_eq_zero_of_ne
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ) (lam xi : ℂ)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hFeig : (WeakSpectrum.koopmanData M hM).U F = lam • F)
    (hGeig : (WeakSpectrum.koopmanData M hM).U G = xi • G)
    (hne : lam ≠ xi) :
    @inner ℂ (Lp ℂ 2 M.μ) _ F G = 0 := by
  have hFraw := koopmanEigenrelation_ae M hM F lam hFeig
  have hGraw := koopmanEigenrelation_ae M hM G xi hGeig
  have hFae0 : ¬ (fun x ↦ F x) =ᵐ[M.μ] 0 := by
    intro hzero
    apply hF0
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℂ 2 M.μ).symm
  have hGae0 : ¬ (fun x ↦ G x) =ᵐ[M.μ] 0 := by
    intro hzero
    apply hG0
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℂ 2 M.μ).symm
  have horth :=
    Section05.eigen_orthogonal M hErg xi lam hne.symm
      (fun x ↦ G x) (fun x ↦ F x)
      ⟨Lp.memLp G, hGae0, by
        simpa only [Chapter01.koopman, Function.comp_def] using hGraw⟩
      ⟨Lp.memLp F, hFae0, by
        simpa only [Chapter01.koopman, Function.comp_def] using hFraw⟩
  rw [L2.inner_def]
  calc
    (∫ x,
        @inner ℂ ℂ _ (F x) (G x) ∂M.μ) =
        ∫ x, G x * star (F x) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.inner_apply, starRingEnd_apply]
    _ = 0 := horth

/-- Pointwise conjugation is conjugate-linear on complex `L²`. -/
lemma lpStar_smul
    (M : System.{u}) (c : ℂ) (F : Lp ℂ 2 M.μ) :
    ForwardKroneckerFactor.lpStar M (c • F) =
      star c • ForwardKroneckerFactor.lpStar M F := by
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M (c • F),
    ForwardKroneckerFactor.lpStar_coe M F,
    Lp.coeFn_smul c F,
    Lp.coeFn_smul (star c)
      (ForwardKroneckerFactor.lpStar M F)] with x hout hstar hin hr
  rw [hout, hin, hr]
  change star (c * F x) =
    star c * ForwardKroneckerFactor.lpStar M F x
  rw [hstar, star_mul]
  ring

lemma lpStar_add
    (M : System.{u}) (F G : Lp ℂ 2 M.μ) :
    ForwardKroneckerFactor.lpStar M (F + G) =
      ForwardKroneckerFactor.lpStar M F +
        ForwardKroneckerFactor.lpStar M G := by
  apply Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.lpStar_coe M (F + G),
    ForwardKroneckerFactor.lpStar_coe M F,
    ForwardKroneckerFactor.lpStar_coe M G,
    Lp.coeFn_add F G,
    Lp.coeFn_add
      (ForwardKroneckerFactor.lpStar M F)
      (ForwardKroneckerFactor.lpStar M G)] with x hout hF hG hin hr
  rw [hout, hin, hr]
  simp only [Pi.add_apply]
  rw [hF, hG, star_add]

/-- Pointwise conjugation sends a Koopman eigenvalue to its complex
conjugate. -/
lemma lpStar_koopmanEigenrelation
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (lam : ℂ)
    (hFeig : (WeakSpectrum.koopmanData M hM).U F = lam • F) :
    (WeakSpectrum.koopmanData M hM).U
        (ForwardKroneckerFactor.lpStar M F) =
      star lam • ForwardKroneckerFactor.lpStar M F := by
  calc
    (WeakSpectrum.koopmanData M hM).U
          (ForwardKroneckerFactor.lpStar M F) =
        ForwardKroneckerFactor.lpStar M
          ((WeakSpectrum.koopmanData M hM).U F) := by
      simpa only [WeakSpectrum.koopmanData,
        MultipleKhintchineKronecker.koopmanData] using
        (ForwardKroneckerFactor.lpStar_koopman M hM F).symm
    _ = ForwardKroneckerFactor.lpStar M (lam • F) := by rw [hFeig]
    _ = star lam • ForwardKroneckerFactor.lpStar M F :=
      lpStar_smul M lam F

lemma lpStar_ne_zero
    (M : System.{u}) (F : Lp ℂ 2 M.μ) (hF : F ≠ 0) :
    ForwardKroneckerFactor.lpStar M F ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  rw [ForwardKroneckerFactor.norm_lpStar, norm_zero] at hnorm
  exact hF (norm_eq_zero.mp hnorm)

/-- Pointwise conjugation is antiunitary for the `L²` inner product.  This
local version keeps the product-invariant argument independent of the later
Host--Kra cube modules. -/
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

/-- The continuous spectral subspace is stable under pointwise complex
conjugation. -/
lemma continuous_lpStar
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ)
    (hF :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) F) :
    InContinuousSpectralSubspace
      (WeakSpectrum.koopmanData M hM)
      (ForwardKroneckerFactor.lpStar M F) := by
  intro Y hY
  obtain ⟨hY0, lam, hYeig⟩ := hY
  have hstarY :
      IsEigenvector (WeakSpectrum.koopmanData M hM)
        (ForwardKroneckerFactor.lpStar M Y) :=
    ⟨lpStar_ne_zero M Y hY0, star lam,
      lpStar_koopmanEigenrelation M hM Y lam hYeig⟩
  have hzero :
      @inner ℂ (Lp ℂ 2 M.μ) _ F
        (ForwardKroneckerFactor.lpStar M Y) = 0 :=
    hF _ hstarY
  have hconj :
      star (@inner ℂ (Lp ℂ 2 M.μ) _
        (ForwardKroneckerFactor.lpStar M F) Y) = 0 := by
    rw [← inner_lpStar_right M F Y]
    exact hzero
  exact star_eq_zero.mp hconj

lemma star_mul_self_eq_one_of_norm_one
    (z : ℂ) (hz : ‖z‖ = 1) :
    star z * z = 1 := by
  rw [mul_comm]
  change z * (starRingEnd ℂ) z = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- Orthogonal projection onto the fixed subspace of the Cartesian-square
Koopman operator. -/
def productInvariantProjectionCLM
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M) :
    Lp ℂ 2 (M.μ.prod M.μ) →L[ℂ] Lp ℂ 2 (M.μ.prod M.μ) :=
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let Uiso :
      Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  S.subtypeL.comp S.orthogonalProjection

theorem norm_productInvariantProjectionCLM_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 (M.μ.prod M.μ)) :
    ‖productInvariantProjectionCLM M hM F‖ ≤ ‖F‖ := by
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let Uiso :
      Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  simpa only [productInvariantProjectionCLM, P, hP, Uiso, U, S] using
    S.norm_starProjection_apply_le F

/-- The row-oriented four-vertex cube pairing. -/
def rowCubePairing
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) : ℂ :=
  @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
    (productInvariantProjectionCLM M hM
      (separatedProductLp M hM
        (ForwardKroneckerFactor.lpStar M F10)
        (ForwardKroneckerFactor.lpStar M F11)))
    (productInvariantProjectionCLM M hM
      (separatedProductLp M hM F00 F01))

/-- The column-oriented four-vertex cube pairing. -/
def columnCubePairing
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) : ℂ :=
  @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
    (productInvariantProjectionCLM M hM
      (separatedProductLp M hM
        (ForwardKroneckerFactor.lpStar M F01)
        (ForwardKroneckerFactor.lpStar M F11)))
    (productInvariantProjectionCLM M hM
      (separatedProductLp M hM F00 F10))

/-- Difference between the two axis orderings of the four-vertex cube
pairing. -/
def cubePairingDefect
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) : ℂ :=
  rowCubePairing M hM F00 F01 F10 F11 -
    columnCubePairing M hM F00 F01 F10 F11

theorem norm_rowCubePairing_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    ‖rowCubePairing M hM F00 F01 F10 F11‖ ≤
      ‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖ := by
  calc
    ‖rowCubePairing M hM F00 F01 F10 F11‖ ≤
        ‖productInvariantProjectionCLM M hM
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F10)
            (ForwardKroneckerFactor.lpStar M F11))‖ *
        ‖productInvariantProjectionCLM M hM
          (separatedProductLp M hM F00 F01)‖ := by
      exact norm_inner_le_norm _ _
    _ ≤
        ‖separatedProductLp M hM
          (ForwardKroneckerFactor.lpStar M F10)
          (ForwardKroneckerFactor.lpStar M F11)‖ *
        ‖separatedProductLp M hM F00 F01‖ := by
      exact mul_le_mul
        (norm_productInvariantProjectionCLM_le M hM _)
        (norm_productInvariantProjectionCLM_le M hM _)
        (norm_nonneg _) (norm_nonneg _)
    _ = ‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖ := by
      rw [norm_separatedProductLp, norm_separatedProductLp,
        ForwardKroneckerFactor.norm_lpStar,
        ForwardKroneckerFactor.norm_lpStar]
      ring

theorem norm_columnCubePairing_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    ‖columnCubePairing M hM F00 F01 F10 F11‖ ≤
      ‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖ := by
  calc
    ‖columnCubePairing M hM F00 F01 F10 F11‖ ≤
        ‖productInvariantProjectionCLM M hM
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F01)
            (ForwardKroneckerFactor.lpStar M F11))‖ *
        ‖productInvariantProjectionCLM M hM
          (separatedProductLp M hM F00 F10)‖ := by
      exact norm_inner_le_norm _ _
    _ ≤
        ‖separatedProductLp M hM
          (ForwardKroneckerFactor.lpStar M F01)
          (ForwardKroneckerFactor.lpStar M F11)‖ *
        ‖separatedProductLp M hM F00 F10‖ := by
      exact mul_le_mul
        (norm_productInvariantProjectionCLM_le M hM _)
        (norm_productInvariantProjectionCLM_le M hM _)
        (norm_nonneg _) (norm_nonneg _)
    _ = ‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖ := by
      rw [norm_separatedProductLp, norm_separatedProductLp,
        ForwardKroneckerFactor.norm_lpStar,
        ForwardKroneckerFactor.norm_lpStar]
      ring

theorem norm_cubePairingDefect_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    ‖cubePairingDefect M hM F00 F01 F10 F11‖ ≤
      2 * (‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖) := by
  calc
    ‖cubePairingDefect M hM F00 F01 F10 F11‖ ≤
        ‖rowCubePairing M hM F00 F01 F10 F11‖ +
          ‖columnCubePairing M hM F00 F01 F10 F11‖ := by
      exact norm_sub_le _ _
    _ ≤
        (‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖) +
          (‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖) :=
      add_le_add
        (norm_rowCubePairing_le M hM F00 F01 F10 F11)
        (norm_columnCubePairing_le M hM F00 F01 F10 F11)
    _ = 2 * (‖F00‖ * ‖F01‖ * ‖F10‖ * ‖F11‖) := by ring

theorem cubePairingDefect_add_00
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM (F + G) F01 F10 F11 =
      cubePairingDefect M hM F F01 F10 F11 +
        cubePairingDefect M hM G F01 F10 F11 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_add_left, map_add, inner_add_right]
  ring

theorem cubePairingDefect_add_01
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F G F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 (F + G) F10 F11 =
      cubePairingDefect M hM F00 F F10 F11 +
        cubePairingDefect M hM F00 G F10 F11 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_add_right, separatedProductLp_add_left,
    lpStar_add, map_add, inner_add_left, inner_add_right]
  ring

theorem cubePairingDefect_add_10
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F G F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 (F + G) F11 =
      cubePairingDefect M hM F00 F01 F F11 +
        cubePairingDefect M hM F00 F01 G F11 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_add_left, separatedProductLp_add_right,
    lpStar_add, map_add, inner_add_left, inner_add_right]
  ring

theorem cubePairingDefect_add_11
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F G : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 F10 (F + G) =
      cubePairingDefect M hM F00 F01 F10 F +
        cubePairingDefect M hM F00 F01 F10 G := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_add_right, lpStar_add, map_add, inner_add_left]
  ring

theorem cubePairingDefect_smul_00
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM (c • F00) F01 F10 F11 =
      c * cubePairingDefect M hM F00 F01 F10 F11 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_smul_left, map_smul, inner_smul_right]
  ring

theorem cubePairingDefect_smul_01
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 (c • F01) F10 F11 =
      c * cubePairingDefect M hM F00 F01 F10 F11 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_smul_right, separatedProductLp_smul_left,
    lpStar_smul, map_smul, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_star]
  ring

theorem cubePairingDefect_smul_10
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 (c • F10) F11 =
      c * cubePairingDefect M hM F00 F01 F10 F11 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_smul_left, separatedProductLp_smul_right,
    lpStar_smul, map_smul, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_star]
  ring

theorem cubePairingDefect_smul_11
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (c : ℂ) (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 F10 (c • F11) =
      c * cubePairingDefect M hM F00 F01 F10 F11 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing,
    separatedProductLp_smul_right, lpStar_smul, map_smul,
    inner_smul_left, starRingEnd_apply, star_star]
  ring

theorem cubePairingDefect_zero_00
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM 0 F01 F10 F11 = 0 := by
  simpa using
    (cubePairingDefect_smul_00 M hM 0
      (0 : Lp ℂ 2 M.μ) F01 F10 F11)

theorem cubePairingDefect_zero_01
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 0 F10 F11 = 0 := by
  simpa using
    (cubePairingDefect_smul_01 M hM 0
      F00 (0 : Lp ℂ 2 M.μ) F10 F11)

theorem cubePairingDefect_zero_10
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 0 F11 = 0 := by
  simpa using
    (cubePairingDefect_smul_10 M hM 0
      F00 F01 (0 : Lp ℂ 2 M.μ) F11)

theorem cubePairingDefect_zero_11
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 F10 0 = 0 := by
  simpa using
    (cubePairingDefect_smul_11 M hM 0
      F00 F01 F10 (0 : Lp ℂ 2 M.μ))

theorem cubePairingDefect_finset_00
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (s : Finset (Lp ℂ 2 M.μ)) (c : Lp ℂ 2 M.μ → ℂ)
    (F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM (∑ y ∈ s, c y • y) F01 F10 F11 =
      ∑ y ∈ s, c y * cubePairingDefect M hM y F01 F10 F11 := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, cubePairingDefect_zero_00]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        cubePairingDefect_add_00, cubePairingDefect_smul_00, ih]

theorem cubePairingDefect_finset_01
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 : Lp ℂ 2 M.μ)
    (s : Finset (Lp ℂ 2 M.μ)) (c : Lp ℂ 2 M.μ → ℂ)
    (F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 (∑ y ∈ s, c y • y) F10 F11 =
      ∑ y ∈ s, c y * cubePairingDefect M hM F00 y F10 F11 := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, cubePairingDefect_zero_01]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        cubePairingDefect_add_01, cubePairingDefect_smul_01, ih]

theorem cubePairingDefect_finset_10
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 : Lp ℂ 2 M.μ)
    (s : Finset (Lp ℂ 2 M.μ)) (c : Lp ℂ 2 M.μ → ℂ)
    (F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 (∑ y ∈ s, c y • y) F11 =
      ∑ y ∈ s, c y * cubePairingDefect M hM F00 F01 y F11 := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, cubePairingDefect_zero_10]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        cubePairingDefect_add_10, cubePairingDefect_smul_10, ih]

theorem cubePairingDefect_finset_11
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 : Lp ℂ 2 M.μ)
    (s : Finset (Lp ℂ 2 M.μ)) (c : Lp ℂ 2 M.μ → ℂ) :
    cubePairingDefect M hM F00 F01 F10 (∑ y ∈ s, c y • y) =
      ∑ y ∈ s, c y * cubePairingDefect M hM F00 F01 F10 y := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, cubePairingDefect_zero_11]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        cubePairingDefect_add_11, cubePairingDefect_smul_11, ih]

/-- A bounded additive scalar functional vanishes at every point that can
be approximated arbitrarily well by zeros of the functional. -/
theorem additive_eq_zero_of_approximable
    {E : Type*} [SeminormedAddCommGroup E]
    (φ : E → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hbound : ∀ x, ‖φ x‖ ≤ C * ‖x‖)
    (x : E)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ y : E, ‖x - y‖ < ε ∧ φ y = 0) :
    φ x = 0 := by
  by_contra hzero
  have hnormpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hzero
  by_cases hCzero : C = 0
  · have hb := hbound x
    rw [hCzero, zero_mul] at hb
    exact (not_lt_of_ge hb) hnormpos
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    let ε : ℝ := ‖φ x‖ / (2 * C)
    have hε : 0 < ε := div_pos hnormpos (mul_pos (by norm_num) hCpos)
    obtain ⟨y, hy, hyzero⟩ := happrox ε hε
    have hφ : φ x = φ (x - y) := by
      calc
        φ x = φ ((x - y) + y) := by congr 1; abel
        _ = φ (x - y) + φ y := hadd _ _
        _ = φ (x - y) := by rw [hyzero, add_zero]
    have hb := hbound (x - y)
    rw [← hφ] at hb
    have hstrict : C * ‖x - y‖ < ‖φ x‖ := by
      calc
        C * ‖x - y‖ < C * ε :=
          mul_lt_mul_of_pos_left hy hCpos
        _ = ‖φ x‖ / 2 := by
          dsimp only [ε]
          field_simp
        _ < ‖φ x‖ := by linarith
    exact (not_lt_of_ge hb) hstrict

/-- Applying an invariant Hilbert--Schmidt kernel to a raw `L²` function
produces an almost-periodic Koopman vector. -/
lemma kernelAction_toLp_almostPeriodic
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM)
      ((HilbertSchmidtConsequences.kernelAction_memLp_two
        M hM H hH.1 f hf).toLp (kernelAction M H f)) := by
  let F : Lp ℂ 2 M.μ := hf.toLp f
  let K : Lp ℂ 2 M.μ :=
    HilbertSchmidtConsequences.kernelOperator M hM H hH.1 F
  have hKap :
      IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM) K :=
    HilbertSchmidtInvariant.kernelOperator_range_almostPeriodic
      M hM H hH F
  have hFraw : (fun x ↦ F x) =ᵐ[M.μ] f := hf.coeFn_toLp
  have haction :
      kernelAction M H (fun x ↦ F x) = kernelAction M H f :=
    HilbertSchmidtConsequences.kernelAction_congr_ae M H hFraw
  have hK :
      K =
        (HilbertSchmidtConsequences.kernelAction_memLp_two
          M hM H hH.1 f hf).toLp (kernelAction M H f) := by
    apply Lp.ext (μ := M.μ)
    change
      (fun x ↦
        (HilbertSchmidtConsequences.kernelOperator M hM H hH.1 F) x)
          =ᵐ[M.μ]
        (fun x ↦
          ((HilbertSchmidtConsequences.kernelAction_memLp_two
            M hM H hH.1 f hf).toLp (kernelAction M H f)) x)
    rw [HilbertSchmidtConsequences.kernelOperator_apply]
    simp only [HilbertSchmidtConsequences.kernelLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk]
    filter_upwards [
      (HilbertSchmidtConsequences.kernelAction_memLp_two
        M hM H hH.1 (fun x ↦ F x) (Lp.memLp F)).coeFn_toLp,
      (HilbertSchmidtConsequences.kernelAction_memLp_two
        M hM H hH.1 f hf).coeFn_toLp] with x hxF hxf
    rw [hxF, hxf, haction]
  rw [← hK]
  exact hKap

/-- A separated product of two Koopman eigenfunctions is an eigenvector on
the Cartesian-square system, with eigenvalue equal to the product of the two
eigenvalues.  The statement allows zero inputs because later projection
computations only use the eigen-relation itself. -/
theorem separatedProduct_koopman_eigen
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f b : M.X → ℂ) (hf : M.lpMember 2 f) (hb : M.lpMember 2 b)
    (lam xi : ℂ)
    (hfeig : f ∘ M.T =ᵐ[M.μ] fun x ↦ lam * f x)
    (hbeig : b ∘ M.T =ᵐ[M.μ] fun x ↦ xi * b x) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.memLp_separatedProduct
        M hM f b hf hb).toLp
        (fun p : M.X × M.X ↦ f p.1 * b p.2)
    (WeakSpectrum.koopmanData P hP).U Y = (lam * xi) • Y := by
  dsimp only
  letI : IsProbabilityMeasure M.μ := hM.1
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let hY :=
    HilbertSchmidtInvariant.memLp_separatedProduct M hM f b hf hb
  let Y : Lp ℂ 2 P.μ :=
    hY.toLp (fun p : M.X × M.X ↦ f p.1 * b p.2)
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving Y hP.2
  have hYcoe := hY.coeFn_toLp
  have hTYcoe := hP.2.quasiMeasurePreserving.ae_eq hYcoe
  have hfeigfst :=
    (Measure.quasiMeasurePreserving_fst
      (μ := M.μ) (ν := M.μ)).ae_eq_comp hfeig
  have hbeigsnd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := M.μ) (ν := M.μ)).ae_eq_comp hbeig
  filter_upwards [hcomp, hYcoe, hTYcoe, hfeigfst, hbeigsnd,
    Lp.coeFn_smul (lam * xi) Y]
      with p hcp hp hTp hfp hbp hsmul
  change
    (Lp.compMeasurePreserving P.T hP.2 Y) p =
      ((lam * xi) • Y) p
  change
    (Lp.compMeasurePreserving P.T hP.2 Y) p =
      (Y ∘ P.T) p at hcp
  change Y p = f p.1 * b p.2 at hp
  change ((lam * xi) • Y) p = (lam * xi) * Y p at hsmul
  rw [hcp, hTp, hsmul, hp]
  change f (M.T p.1) * b (M.T p.2) =
    (lam * xi) * (f p.1 * b p.2)
  change f (M.T p.1) = lam * f p.1 at hfp
  change b (M.T p.2) = xi * b p.2 at hbp
  rw [hfp, hbp]
  ring

/-- The fixed-space projection of a separated product of two Koopman
eigenfunctions is the product itself precisely when the product eigenvalue is
one, and is zero otherwise. -/
theorem separatedProduct_fixedProjection_of_eigen
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f b : M.X → ℂ) (hf : M.lpMember 2 f) (hb : M.lpMember 2 b)
    (lam xi : ℂ)
    (hfeig : f ∘ M.T =ᵐ[M.μ] fun x ↦ lam * f x)
    (hbeig : b ∘ M.T =ᵐ[M.μ] fun x ↦ xi * b x) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Uiso :
        Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
      Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
    let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
      Uiso.toContinuousLinearMap
    let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
      LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.memLp_separatedProduct
        M hM f b hf hb).toLp
        (fun p : M.X × M.X ↦ f p.1 * b p.2)
    (S.orthogonalProjection Y : Lp ℂ 2 P.μ) =
      if lam * xi = 1 then Y else 0 := by
  dsimp only
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let Uiso :
      Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  let Y : Lp ℂ 2 P.μ :=
    (HilbertSchmidtInvariant.memLp_separatedProduct
      M hM f b hf hb).toLp
      (fun p : M.X × M.X ↦ f p.1 * b p.2)
  have hYeig : U Y = (lam * xi) • Y := by
    simpa only [U, Uiso, WeakSpectrum.koopmanData] using
      separatedProduct_koopman_eigen
        M hM f b hf hb lam xi hfeig hbeig
  by_cases halpha : lam * xi = 1
  · rw [if_pos halpha]
    have hYfix : U Y = Y := by
      rw [hYeig, halpha, one_smul]
    have hYS : Y ∈ S := hYfix
    simpa using congrArg Subtype.val
      (S.orthogonalProjection_mem_subspace_eq_self ⟨Y, hYS⟩)
  · rw [if_neg halpha]
    have hYorth : Y ∈ Sᗮ := by
      intro Z hZS
      have hZfix : U Z = Z := hZS
      have hisom := Uiso.inner_map_map Y Z
      change
        @inner ℂ (Lp ℂ 2 P.μ) _ (U Y) (U Z) =
          @inner ℂ (Lp ℂ 2 P.μ) _ Y Z at hisom
      rw [hYeig, hZfix, inner_smul_left] at hisom
      have hstar_ne : star (lam * xi) ≠ 1 := by
        intro hstar
        apply halpha
        have := congrArg star hstar
        simpa using this
      have hmul :
          (star (lam * xi) - 1) *
              @inner ℂ (Lp ℂ 2 P.μ) _ Y Z = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]
        exact hisom
      have hinner :
          @inner ℂ (Lp ℂ 2 P.μ) _ Y Z = 0 :=
        (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hstar_ne)
      exact inner_eq_zero_symm.mpr hinner
    have hproj : S.starProjection Y = 0 := by
      apply S.eq_starProjection_of_mem_orthogonal
      · exact S.zero_mem
      · simpa using hYorth
    exact hproj

/-- `Lp`-level form of `separatedProduct_fixedProjection_of_eigen`, avoiding
all representative choices in later finite spectral sums. -/
theorem separatedProductLp_fixedProjection_of_eigen
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ) (lam xi : ℂ)
    (hFeig :
      (WeakSpectrum.koopmanData M hM).U F = lam • F)
    (hGeig :
      (WeakSpectrum.koopmanData M hM).U G = xi • G) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Uiso :
        Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
      Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
    let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
      Uiso.toContinuousLinearMap
    let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
      LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
    (S.orthogonalProjection (separatedProductLp M hM F G) :
        Lp ℂ 2 P.μ) =
      if lam * xi = 1 then separatedProductLp M hM F G else 0 := by
  dsimp only
  have hFcomp := Lp.coeFn_compMeasurePreserving F hM.2
  have hGcomp := Lp.coeFn_compMeasurePreserving G hM.2
  have hFsmul := Lp.coeFn_smul lam F
  have hGsmul := Lp.coeFn_smul xi G
  have hFraw :
      (fun x ↦ F (M.T x)) =ᵐ[M.μ] fun x ↦ lam * F x := by
    change Lp.compMeasurePreserving M.T hM.2 F = lam • F at hFeig
    have heq :
        (fun x ↦
          (show Lp ℂ 2 M.μ from
            Lp.compMeasurePreserving M.T hM.2 F) x) =ᵐ[M.μ]
          fun x ↦ (lam • F) x := by rw [hFeig]
    filter_upwards [hFcomp, hFsmul, heq] with x hcomp hsmul heig
    rw [hcomp, hsmul] at heig
    exact heig
  have hGraw :
      (fun x ↦ G (M.T x)) =ᵐ[M.μ] fun x ↦ xi * G x := by
    change Lp.compMeasurePreserving M.T hM.2 G = xi • G at hGeig
    have heq :
        (fun x ↦
          (show Lp ℂ 2 M.μ from
            Lp.compMeasurePreserving M.T hM.2 G) x) =ᵐ[M.μ]
          fun x ↦ (xi • G) x := by rw [hGeig]
    filter_upwards [hGcomp, hGsmul, heq] with x hcomp hsmul heig
    rw [hcomp, hsmul] at heig
    exact heig
  simpa only [separatedProductLp] using
    separatedProduct_fixedProjection_of_eigen
      M hM (fun x ↦ F x) (fun x ↦ G x)
      (Lp.memLp F) (Lp.memLp G) lam xi hFraw hGraw

theorem productInvariantProjectionCLM_separatedProductLp_eigen
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ) (lam xi : ℂ)
    (hFeig :
      (WeakSpectrum.koopmanData M hM).U F = lam • F)
    (hGeig :
      (WeakSpectrum.koopmanData M hM).U G = xi • G) :
    productInvariantProjectionCLM M hM
        (separatedProductLp M hM F G) =
      if lam * xi = 1 then separatedProductLp M hM F G else 0 := by
  simpa only [productInvariantProjectionCLM] using
    separatedProductLp_fixedProjection_of_eigen
      M hM F G lam xi hFeig hGeig

/-- The nonzero (fully resonant) four-eigenvector case of diagonal cube
transposition.  Ergodicity reduces the four inputs to two one-dimensional
eigenspaces, after which the identity is purely scalar. -/
theorem eigenCubePairing_eq_of_resonant
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (lam00 lam01 lam10 lam11 : ℂ)
    (hF00 : F00 ≠ 0) (hF01 : F01 ≠ 0)
    (hF10 : F10 ≠ 0) (hF11 : F11 ≠ 0)
    (heig00 : (WeakSpectrum.koopmanData M hM).U F00 = lam00 • F00)
    (heig01 : (WeakSpectrum.koopmanData M hM).U F01 = lam01 • F01)
    (heig10 : (WeakSpectrum.koopmanData M hM).U F10 = lam10 • F10)
    (heig11 : (WeakSpectrum.koopmanData M hM).U F11 = lam11 • F11)
    (hrow0 : lam00 * lam01 = 1)
    (hrow1 : lam10 * lam11 = 1)
    (hcol0 : lam00 * lam10 = 1)
    (hcol1 : lam01 * lam11 = 1) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F10)
            (ForwardKroneckerFactor.lpStar M F11)))
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM F00 F01)) =
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F01)
            (ForwardKroneckerFactor.lpStar M F11)))
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM F00 F10)) := by
  have hstarRow1 : star lam10 * star lam11 = 1 := by
    rw [mul_comm (star lam10) (star lam11), ← star_mul, hrow1, star_one]
  have hstarCol1 : star lam01 * star lam11 = 1 := by
    rw [mul_comm (star lam01) (star lam11), ← star_mul, hcol1, star_one]
  rw [
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM (ForwardKroneckerFactor.lpStar M F10)
        (ForwardKroneckerFactor.lpStar M F11)
        (star lam10) (star lam11)
        (lpStar_koopmanEigenrelation M hM F10 lam10 heig10)
        (lpStar_koopmanEigenrelation M hM F11 lam11 heig11),
    if_pos hstarRow1,
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM F00 F01 lam00 lam01 heig00 heig01,
    if_pos hrow0,
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM (ForwardKroneckerFactor.lpStar M F01)
        (ForwardKroneckerFactor.lpStar M F11)
        (star lam01) (star lam11)
        (lpStar_koopmanEigenrelation M hM F01 lam01 heig01)
        (lpStar_koopmanEigenrelation M hM F11 lam11 heig11),
    if_pos hstarCol1,
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM F00 F10 lam00 lam10 heig00 heig10,
    if_pos hcol0]
  rw [inner_separatedProductLp, inner_separatedProductLp]
  have hlam00 : lam00 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hrow0
    exact zero_ne_one hrow0
  have hlam01 : lam01 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hrow0
    exact zero_ne_one hrow0
  have hlam11eq : lam11 = lam00 := by
    apply mul_left_cancel₀ hlam01
    calc
      lam01 * lam11 = 1 := hcol1
      _ = lam00 * lam01 := hrow0.symm
      _ = lam01 * lam00 := mul_comm _ _
  have hlam10eq : lam10 = lam01 := by
    apply mul_left_cancel₀ hlam00
    calc
      lam00 * lam10 = 1 := hcol0
      _ = lam00 * lam01 := hrow0.symm
  have heig11' :
      (WeakSpectrum.koopmanData M hM).U F11 = lam00 • F11 := by
    simpa only [hlam11eq] using heig11
  have heig10' :
      (WeakSpectrum.koopmanData M hM).U F10 = lam01 • F10 := by
    simpa only [hlam10eq] using heig10
  obtain ⟨a, ha⟩ :=
    same_koopmanEigenvalue_proportional
      M hM hErg F11 F00 lam00 hF11 hF00 heig11' heig00
  obtain ⟨b, hb⟩ :=
    same_koopmanEigenvalue_proportional
      M hM hErg F10 F01 lam01 hF10 hF01 heig10' heig01
  rw [ha, hb, lpStar_smul, lpStar_smul]
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]
  ring

/-- Diagonal cube transposition for four nonzero Koopman eigenvectors.
The resonant case is one-dimensional by ergodicity; in every nonresonant
case one of the invariant projections, or one of the resulting factor
inner products, vanishes. -/
theorem eigenCubePairing_eq
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (lam00 lam01 lam10 lam11 : ℂ)
    (hF00 : F00 ≠ 0) (hF01 : F01 ≠ 0)
    (hF10 : F10 ≠ 0) (hF11 : F11 ≠ 0)
    (heig00 : (WeakSpectrum.koopmanData M hM).U F00 = lam00 • F00)
    (heig01 : (WeakSpectrum.koopmanData M hM).U F01 = lam01 • F01)
    (heig10 : (WeakSpectrum.koopmanData M hM).U F10 = lam10 • F10)
    (heig11 : (WeakSpectrum.koopmanData M hM).U F11 = lam11 • F11) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F10)
            (ForwardKroneckerFactor.lpStar M F11)))
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM F00 F01)) =
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F01)
            (ForwardKroneckerFactor.lpStar M F11)))
        (productInvariantProjectionCLM M hM
          (separatedProductLp M hM F00 F10)) := by
  have hlam01 := koopmanEigenvalue_norm_one M hM F01 lam01 hF01 heig01
  have hlam10 := koopmanEigenvalue_norm_one M hM F10 lam10 hF10 heig10
  have hlam11 := koopmanEigenvalue_norm_one M hM F11 lam11 hF11 heig11
  have hstar01 := star_mul_self_eq_one_of_norm_one lam01 hlam01
  have hstar10 := star_mul_self_eq_one_of_norm_one lam10 hlam10
  have hstar11 := star_mul_self_eq_one_of_norm_one lam11 hlam11
  have hstarRow1 :
      (star lam10 * star lam11 = 1) ↔
        (lam10 * lam11 = 1) := by
    constructor <;> intro h
    · have hs := congrArg star h
      simpa only [star_mul, star_star, star_one, mul_comm] using hs
    · have hs := congrArg star h
      simpa only [star_mul, star_one, mul_comm] using hs
  have hstarCol1 :
      (star lam01 * star lam11 = 1) ↔
        (lam01 * lam11 = 1) := by
    constructor <;> intro h
    · have hs := congrArg star h
      simpa only [star_mul, star_star, star_one, mul_comm] using hs
    · have hs := congrArg star h
      simpa only [star_mul, star_one, mul_comm] using hs
  have hleft_zero_of_not_col0
      (hcol0 : ¬ lam00 * lam10 = 1) :
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F10)
            (ForwardKroneckerFactor.lpStar M F11))
          (separatedProductLp M hM F00 F01) = 0 := by
    rw [inner_separatedProductLp]
    have hne : star lam10 ≠ lam00 := by
      intro heq
      apply hcol0
      rw [← heq]
      exact hstar10
    have hinner :=
      koopmanEigenvectors_inner_eq_zero_of_ne
        M hM hErg
        (ForwardKroneckerFactor.lpStar M F10) F00
        (star lam10) lam00
        (lpStar_ne_zero M F10 hF10) hF00
        (lpStar_koopmanEigenrelation M hM F10 lam10 heig10)
        heig00 hne
    rw [hinner, zero_mul]
  have hleft_zero_of_not_col1
      (hcol1 : ¬ lam01 * lam11 = 1) :
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F10)
            (ForwardKroneckerFactor.lpStar M F11))
          (separatedProductLp M hM F00 F01) = 0 := by
    rw [inner_separatedProductLp]
    have hne : star lam11 ≠ lam01 := by
      intro heq
      apply hcol1
      rw [← heq]
      exact hstar11
    have hinner :=
      koopmanEigenvectors_inner_eq_zero_of_ne
        M hM hErg
        (ForwardKroneckerFactor.lpStar M F11) F01
        (star lam11) lam01
        (lpStar_ne_zero M F11 hF11) hF01
        (lpStar_koopmanEigenrelation M hM F11 lam11 heig11)
        heig01 hne
    rw [hinner, mul_zero]
  have hright_zero_of_not_row0
      (hrow0 : ¬ lam00 * lam01 = 1) :
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F01)
            (ForwardKroneckerFactor.lpStar M F11))
          (separatedProductLp M hM F00 F10) = 0 := by
    rw [inner_separatedProductLp]
    have hne : star lam01 ≠ lam00 := by
      intro heq
      apply hrow0
      rw [← heq]
      exact hstar01
    have hinner :=
      koopmanEigenvectors_inner_eq_zero_of_ne
        M hM hErg
        (ForwardKroneckerFactor.lpStar M F01) F00
        (star lam01) lam00
        (lpStar_ne_zero M F01 hF01) hF00
        (lpStar_koopmanEigenrelation M hM F01 lam01 heig01)
        heig00 hne
    rw [hinner, zero_mul]
  have hright_zero_of_not_row1
      (hrow1 : ¬ lam10 * lam11 = 1) :
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F01)
            (ForwardKroneckerFactor.lpStar M F11))
          (separatedProductLp M hM F00 F10) = 0 := by
    rw [inner_separatedProductLp]
    have hne : star lam11 ≠ lam10 := by
      intro heq
      apply hrow1
      rw [← heq]
      exact hstar11
    have hinner :=
      koopmanEigenvectors_inner_eq_zero_of_ne
        M hM hErg
        (ForwardKroneckerFactor.lpStar M F11) F10
        (star lam11) lam10
        (lpStar_ne_zero M F11 hF11) hF10
        (lpStar_koopmanEigenrelation M hM F11 lam11 heig11)
        heig10 hne
    rw [hinner, mul_zero]
  have hresonant
      (hrow0 : lam00 * lam01 = 1)
      (hrow1 : lam10 * lam11 = 1)
      (hcol0 : lam00 * lam10 = 1)
      (hcol1 : lam01 * lam11 = 1) :
      @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F10)
            (ForwardKroneckerFactor.lpStar M F11))
          (separatedProductLp M hM F00 F01) =
        @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
          (separatedProductLp M hM
            (ForwardKroneckerFactor.lpStar M F01)
            (ForwardKroneckerFactor.lpStar M F11))
          (separatedProductLp M hM F00 F10) := by
    have h :=
      eigenCubePairing_eq_of_resonant
        M hM hErg F00 F01 F10 F11
        lam00 lam01 lam10 lam11
        hF00 hF01 hF10 hF11
        heig00 heig01 heig10 heig11
        hrow0 hrow1 hcol0 hcol1
    rw [
      productInvariantProjectionCLM_separatedProductLp_eigen
        M hM (ForwardKroneckerFactor.lpStar M F10)
          (ForwardKroneckerFactor.lpStar M F11)
          (star lam10) (star lam11)
          (lpStar_koopmanEigenrelation M hM F10 lam10 heig10)
          (lpStar_koopmanEigenrelation M hM F11 lam11 heig11),
      if_pos (hstarRow1.mpr hrow1),
      productInvariantProjectionCLM_separatedProductLp_eigen
        M hM F00 F01 lam00 lam01 heig00 heig01,
      if_pos hrow0,
      productInvariantProjectionCLM_separatedProductLp_eigen
        M hM (ForwardKroneckerFactor.lpStar M F01)
          (ForwardKroneckerFactor.lpStar M F11)
          (star lam01) (star lam11)
          (lpStar_koopmanEigenrelation M hM F01 lam01 heig01)
          (lpStar_koopmanEigenrelation M hM F11 lam11 heig11),
      if_pos (hstarCol1.mpr hcol1),
      productInvariantProjectionCLM_separatedProductLp_eigen
        M hM F00 F10 lam00 lam10 heig00 heig10,
      if_pos hcol0] at h
    exact h
  rw [
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM (ForwardKroneckerFactor.lpStar M F10)
        (ForwardKroneckerFactor.lpStar M F11)
        (star lam10) (star lam11)
        (lpStar_koopmanEigenrelation M hM F10 lam10 heig10)
        (lpStar_koopmanEigenrelation M hM F11 lam11 heig11),
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM F00 F01 lam00 lam01 heig00 heig01,
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM (ForwardKroneckerFactor.lpStar M F01)
        (ForwardKroneckerFactor.lpStar M F11)
        (star lam01) (star lam11)
        (lpStar_koopmanEigenrelation M hM F01 lam01 heig01)
        (lpStar_koopmanEigenrelation M hM F11 lam11 heig11),
    productInvariantProjectionCLM_separatedProductLp_eigen
      M hM F00 F10 lam00 lam10 heig00 heig10]
  simp only [hstarRow1, hstarCol1]
  by_cases hrow0 : lam00 * lam01 = 1 <;>
    by_cases hrow1 : lam10 * lam11 = 1 <;>
    by_cases hcol0 : lam00 * lam10 = 1 <;>
    by_cases hcol1 : lam01 * lam11 = 1
  all_goals
    simp only [hrow0, hrow1, hcol0, hcol1, if_true, if_false,
      inner_zero_left, inner_zero_right]
  all_goals
    first
    | exact hresonant hrow0 hrow1 hcol0 hcol1
    | exact hleft_zero_of_not_col0 hcol0
    | exact hleft_zero_of_not_col1 hcol1
    | exact (hright_zero_of_not_row0 hrow0).symm
    | exact (hright_zero_of_not_row1 hrow1).symm

theorem cubePairingDefect_eigen_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (h00 : IsEigenvector (WeakSpectrum.koopmanData M hM) F00)
    (h01 : IsEigenvector (WeakSpectrum.koopmanData M hM) F01)
    (h10 : IsEigenvector (WeakSpectrum.koopmanData M hM) F10)
    (h11 : IsEigenvector (WeakSpectrum.koopmanData M hM) F11) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  obtain ⟨hF00, lam00, heig00⟩ := h00
  obtain ⟨hF01, lam01, heig01⟩ := h01
  obtain ⟨hF10, lam10, heig10⟩ := h10
  obtain ⟨hF11, lam11, heig11⟩ := h11
  rw [cubePairingDefect, sub_eq_zero]
  simpa only [rowCubePairing, columnCubePairing] using
    eigenCubePairing_eq
      M hM hErg F00 F01 F10 F11
      lam00 lam01 lam10 lam11
      hF00 hF01 hF10 hF11
      heig00 heig01 heig10 heig11

/-- The cube transposition defect vanishes on four finite Koopman spectral
combinations. -/
theorem cubePairingDefect_finiteEigenCombinations_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (s00 s01 s10 s11 : Finset (Lp ℂ 2 M.μ))
    (hs00 : ∀ y ∈ s00, IsEigenvector (WeakSpectrum.koopmanData M hM) y)
    (hs01 : ∀ y ∈ s01, IsEigenvector (WeakSpectrum.koopmanData M hM) y)
    (hs10 : ∀ y ∈ s10, IsEigenvector (WeakSpectrum.koopmanData M hM) y)
    (hs11 : ∀ y ∈ s11, IsEigenvector (WeakSpectrum.koopmanData M hM) y)
    (c00 c01 c10 c11 : Lp ℂ 2 M.μ → ℂ) :
    cubePairingDefect M hM
      (∑ y ∈ s00, c00 y • y)
      (∑ y ∈ s01, c01 y • y)
      (∑ y ∈ s10, c10 y • y)
      (∑ y ∈ s11, c11 y • y) = 0 := by
  rw [cubePairingDefect_finset_00]
  apply Finset.sum_eq_zero
  intro y00 hy00
  apply mul_eq_zero.mpr
  right
  rw [cubePairingDefect_finset_01]
  apply Finset.sum_eq_zero
  intro y01 hy01
  apply mul_eq_zero.mpr
  right
  rw [cubePairingDefect_finset_10]
  apply Finset.sum_eq_zero
  intro y10 hy10
  apply mul_eq_zero.mpr
  right
  rw [cubePairingDefect_finset_11]
  apply Finset.sum_eq_zero
  intro y11 hy11
  apply mul_eq_zero.mpr
  right
  exact cubePairingDefect_eigen_eq_zero
    M hM hErg y00 y01 y10 y11
    (hs00 y00 hy00) (hs01 y01 hy01)
    (hs10 y10 hy10) (hs11 y11 hy11)

theorem cubePairingDefect_eq_zero_of_discrete_00
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hdisc :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F00)
    (hfinite :
      ∀ (s : Finset (Lp ℂ 2 M.μ))
        (_hs : ∀ y ∈ s,
          IsEigenvector (WeakSpectrum.koopmanData M hM) y)
        (c : Lp ℂ 2 M.μ → ℂ),
        cubePairingDefect M hM
          (∑ y ∈ s, c y • y) F01 F10 F11 = 0) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  let C : ℝ := 2 * (‖F01‖ * ‖F10‖ * ‖F11‖)
  apply additive_eq_zero_of_approximable
    (fun X ↦ cubePairingDefect M hM X F01 F10 F11) C
  · dsimp only [C]
    positivity
  · intro X Y
    exact cubePairingDefect_add_00 M hM X Y F01 F10 F11
  · intro X
    calc
      ‖cubePairingDefect M hM X F01 F10 F11‖ ≤
          2 * (‖X‖ * ‖F01‖ * ‖F10‖ * ‖F11‖) :=
        norm_cubePairingDefect_le M hM X F01 F10 F11
      _ = C * ‖X‖ := by dsimp only [C]; ring
  · intro ε hε
    obtain ⟨s, hs, c, hclose⟩ := hdisc ε hε
    exact ⟨∑ y ∈ s, c y • y, hclose, hfinite s hs c⟩

theorem cubePairingDefect_eq_zero_of_discrete_01
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hdisc :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F01)
    (hfinite :
      ∀ (s : Finset (Lp ℂ 2 M.μ))
        (_hs : ∀ y ∈ s,
          IsEigenvector (WeakSpectrum.koopmanData M hM) y)
        (c : Lp ℂ 2 M.μ → ℂ),
        cubePairingDefect M hM F00
          (∑ y ∈ s, c y • y) F10 F11 = 0) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  let C : ℝ := 2 * (‖F00‖ * ‖F10‖ * ‖F11‖)
  apply additive_eq_zero_of_approximable
    (fun X ↦ cubePairingDefect M hM F00 X F10 F11) C
  · dsimp only [C]
    positivity
  · intro X Y
    exact cubePairingDefect_add_01 M hM F00 X Y F10 F11
  · intro X
    calc
      ‖cubePairingDefect M hM F00 X F10 F11‖ ≤
          2 * (‖F00‖ * ‖X‖ * ‖F10‖ * ‖F11‖) :=
        norm_cubePairingDefect_le M hM F00 X F10 F11
      _ = C * ‖X‖ := by dsimp only [C]; ring
  · intro ε hε
    obtain ⟨s, hs, c, hclose⟩ := hdisc ε hε
    exact ⟨∑ y ∈ s, c y • y, hclose, hfinite s hs c⟩

theorem cubePairingDefect_eq_zero_of_discrete_10
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hdisc :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F10)
    (hfinite :
      ∀ (s : Finset (Lp ℂ 2 M.μ))
        (_hs : ∀ y ∈ s,
          IsEigenvector (WeakSpectrum.koopmanData M hM) y)
        (c : Lp ℂ 2 M.μ → ℂ),
        cubePairingDefect M hM F00 F01
          (∑ y ∈ s, c y • y) F11 = 0) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  let C : ℝ := 2 * (‖F00‖ * ‖F01‖ * ‖F11‖)
  apply additive_eq_zero_of_approximable
    (fun X ↦ cubePairingDefect M hM F00 F01 X F11) C
  · dsimp only [C]
    positivity
  · intro X Y
    exact cubePairingDefect_add_10 M hM F00 F01 X Y F11
  · intro X
    calc
      ‖cubePairingDefect M hM F00 F01 X F11‖ ≤
          2 * (‖F00‖ * ‖F01‖ * ‖X‖ * ‖F11‖) :=
        norm_cubePairingDefect_le M hM F00 F01 X F11
      _ = C * ‖X‖ := by dsimp only [C]; ring
  · intro ε hε
    obtain ⟨s, hs, c, hclose⟩ := hdisc ε hε
    exact ⟨∑ y ∈ s, c y • y, hclose, hfinite s hs c⟩

theorem cubePairingDefect_eq_zero_of_discrete_11
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hdisc :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F11)
    (hfinite :
      ∀ (s : Finset (Lp ℂ 2 M.μ))
        (_hs : ∀ y ∈ s,
          IsEigenvector (WeakSpectrum.koopmanData M hM) y)
        (c : Lp ℂ 2 M.μ → ℂ),
        cubePairingDefect M hM F00 F01 F10
          (∑ y ∈ s, c y • y) = 0) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  let C : ℝ := 2 * (‖F00‖ * ‖F01‖ * ‖F10‖)
  apply additive_eq_zero_of_approximable
    (fun X ↦ cubePairingDefect M hM F00 F01 F10 X) C
  · dsimp only [C]
    positivity
  · intro X Y
    exact cubePairingDefect_add_11 M hM F00 F01 F10 X Y
  · intro X
    calc
      ‖cubePairingDefect M hM F00 F01 F10 X‖ ≤
          2 * (‖F00‖ * ‖F01‖ * ‖F10‖ * ‖X‖) :=
        norm_cubePairingDefect_le M hM F00 F01 F10 X
      _ = C * ‖X‖ := by dsimp only [C]; ring
  · intro ε hε
    obtain ⟨s, hs, c, hclose⟩ := hdisc ε hε
    exact ⟨∑ y ∈ s, c y • y, hclose, hfinite s hs c⟩

/-- Cube transposition on the full discrete spectral subspace of an
ergodic Koopman system. -/
theorem cubePairingDefect_discrete_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hdisc00 :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F00)
    (hdisc01 :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F01)
    (hdisc10 :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F10)
    (hdisc11 :
      InDiscreteSpectralSubspace (WeakSpectrum.koopmanData M hM) F11) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  apply cubePairingDefect_eq_zero_of_discrete_11
    M hM F00 F01 F10 F11 hdisc11
  intro s11 hs11 c11
  apply cubePairingDefect_eq_zero_of_discrete_10
    M hM F00 F01 F10 (∑ y ∈ s11, c11 y • y) hdisc10
  intro s10 hs10 c10
  apply cubePairingDefect_eq_zero_of_discrete_01
    M hM F00 F01
      (∑ y ∈ s10, c10 y • y)
      (∑ y ∈ s11, c11 y • y) hdisc01
  intro s01 hs01 c01
  apply cubePairingDefect_eq_zero_of_discrete_00
    M hM F00
      (∑ y ∈ s01, c01 y • y)
      (∑ y ∈ s10, c10 y • y)
      (∑ y ∈ s11, c11 y • y) hdisc00
  intro s00 hs00 c00
  exact cubePairingDefect_finiteEigenCombinations_eq_zero
    M hM hErg s00 s01 s10 s11
    hs00 hs01 hs10 hs11 c00 c01 c10 c11

/-- If the first factor is continuous-spectral, then every separated product
with that first factor is orthogonal to every invariant `L²` kernel on the
Cartesian square.  This is the polarized form of the tensor-square
orthogonality used in the cube-symmetry argument. -/
theorem inner_separatedProduct_invariant_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f b : M.X → ℂ) (hf : M.lpMember 2 f) (hb : M.lpMember 2 b)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f))
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        ((HilbertSchmidtInvariant.memLp_separatedProduct
          M hM f b hf hb).toLp
          (fun p : M.X × M.X ↦ f p.1 * b p.2))
        (hH.1.toLp H) = 0 := by
  rw [HilbertSchmidtInvariant.inner_separatedProduct_kernel
    M hM H hH.1 f b hf hb]
  have hap :
      IsAlmostPeriodicVector (WeakSpectrum.koopmanData M hM)
        ((HilbertSchmidtConsequences.kernelAction_memLp_two
          M hM H hH.1
            (fun y ↦ star (b y)) hb.star).toLp
          (kernelAction M H (fun y ↦ star (b y)))) :=
    kernelAction_toLp_almostPeriodic M hM H hH
      (fun y ↦ star (b y)) hb.star
  exact
    AlmostPeriodicIsometry.continuous_inner_almostPeriodic_eq_zero
      (WeakSpectrum.koopmanData M hM)
      (fun F ↦
        (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map F)
      (hf.toLp f)
      ((HilbertSchmidtConsequences.kernelAction_memLp_two
        M hM H hH.1 (fun y ↦ star (b y)) hb.star).toLp
          (kernelAction M H (fun y ↦ star (b y))))
      hcont hap

/-- The symmetric form of `inner_separatedProduct_invariant_eq_zero`: a
continuous-spectral second factor also forces orthogonality. -/
theorem inner_separatedProduct_invariant_eq_zero_of_second
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f b : M.X → ℂ) (hf : M.lpMember 2 f) (hb : M.lpMember 2 b)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hb.toLp b))
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        ((HilbertSchmidtInvariant.memLp_separatedProduct
          M hM f b hf hb).toLp
          (fun p : M.X × M.X ↦ f p.1 * b p.2))
        (hH.1.toLp H) = 0 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let τ : M.X × M.X → M.X × M.X := fun p ↦ (p.2, p.1)
  let hτ : MeasurePreserving τ (M.μ.prod M.μ) (M.μ.prod M.μ) := by
    simpa only [τ] using
      (Measure.measurePreserving_swap (μ := M.μ) (ν := M.μ))
  let V : Lp ℂ 2 (M.μ.prod M.μ) →ₗᵢ[ℂ]
      Lp ℂ 2 (M.μ.prod M.μ) :=
    Lp.compMeasurePreservingₗᵢ ℂ τ hτ
  let hfb :=
    HilbertSchmidtInvariant.memLp_separatedProduct M hM f b hf hb
  let hbf :=
    HilbertSchmidtInvariant.memLp_separatedProduct M hM b f hb hf
  let FB : Lp ℂ 2 (M.μ.prod M.μ) :=
    hfb.toLp (fun p : M.X × M.X ↦ f p.1 * b p.2)
  let BF : Lp ℂ 2 (M.μ.prod M.μ) :=
    hbf.toLp (fun p : M.X × M.X ↦ b p.1 * f p.2)
  let HT : M.X × M.X → ℂ :=
    HilbertSchmidtInvariant.kernelTranspose M H
  let hHT : IsInvariantL2Kernel M HT :=
    ⟨HilbertSchmidtInvariant.kernelTranspose_memLp M hM H hH.1,
      HilbertSchmidtInvariant.kernelTranspose_invariant M hM H hH.2⟩
  let HLp : Lp ℂ 2 (M.μ.prod M.μ) := hH.1.toLp H
  let HTLp : Lp ℂ 2 (M.μ.prod M.μ) := hHT.1.toLp HT
  have hVFB : V FB = BF := by
    apply Lp.ext
    have hcomp := Lp.coeFn_compMeasurePreserving FB hτ
    have hfbcoe := hfb.coeFn_toLp
    have hbfcoe := hbf.coeFn_toLp
    filter_upwards [hcomp, hτ.quasiMeasurePreserving.ae_eq hfbcoe,
      hbfcoe] with p hcp hfp hbp
    change V FB p = BF p
    change V FB p = FB (τ p) at hcp
    change FB (τ p) = f (τ p).1 * b (τ p).2 at hfp
    change BF p = b p.1 * f p.2 at hbp
    rw [hcp, hfp, hbp]
    simp only [τ]
    ring
  have hVHLp : V HLp = HTLp := by
    apply Lp.ext
    have hcomp := Lp.coeFn_compMeasurePreserving HLp hτ
    have hHcoe := hH.1.coeFn_toLp
    have hHTcoe := hHT.1.coeFn_toLp
    filter_upwards [hcomp, hτ.quasiMeasurePreserving.ae_eq hHcoe,
      hHTcoe] with p hcp hp htp
    change V HLp p = HTLp p
    change V HLp p = HLp (τ p) at hcp
    change HLp (τ p) = H (τ p) at hp
    change HTLp p = HT p at htp
    rw [hcp, hp, htp]
    rfl
  have hisom := V.inner_map_map FB HLp
  rw [hVFB, hVHLp] at hisom
  change
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _ FB HLp = 0
  rw [← hisom]
  exact inner_separatedProduct_invariant_eq_zero
    M hM b f hb hf hcont HT hHT

/-- A continuous-spectral vector has tensor-conjugate square orthogonal to
every invariant `L²` kernel on the Cartesian square. -/
theorem inner_tensorSquare_invariant_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f))
    (H : M.X × M.X → ℂ) (hH : IsInvariantL2Kernel M H) :
    @inner ℂ (Lp ℂ 2 (M.μ.prod M.μ)) _
        ((HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
          (TensorSquare M f))
        (hH.1.toLp H) = 0 := by
  simpa only [TensorSquare] using
    inner_separatedProduct_invariant_eq_zero
      M hM f (fun x ↦ star (f x)) hf hf.star hcont H hH

/-- The invariant projection of a separated product vanishes whenever its
first factor is continuous-spectral. -/
theorem separatedProduct_fixedProjection_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f b : M.X → ℂ) (hf : M.lpMember 2 f) (hb : M.lpMember 2 b)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f)) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Uiso :
        Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
      Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
    let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
      Uiso.toContinuousLinearMap
    let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
      LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.memLp_separatedProduct
        M hM f b hf hb).toLp
        (fun p : M.X × M.X ↦ f p.1 * b p.2)
    (S.orthogonalProjection Y : Lp ℂ 2 P.μ) = 0 := by
  dsimp only
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let Uiso :
      Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  let Y : Lp ℂ 2 P.μ :=
    (HilbertSchmidtInvariant.memLp_separatedProduct
      M hM f b hf hb).toLp
      (fun p : M.X × M.X ↦ f p.1 * b p.2)
  have hYorth : Y ∈ Sᗮ := by
    intro Z hZ
    have hfix : U Z = Z := hZ
    have hcoe := Lp.coeFn_compMeasurePreserving Z hP.2
    have hZinv :
        (fun p : M.X × M.X ↦ Z (productTransformation M p)) =ᵐ[M.μ.prod M.μ]
          (fun p ↦ Z p) := by
      change ⇑(U Z) =ᵐ[P.μ] (⇑Z) ∘ P.T at hcoe
      rw [hfix] at hcoe
      simpa only [P, ProductWeakMixing.productSystem,
        productTransformation, Function.comp_apply] using hcoe.symm
    have hinner :=
      inner_separatedProduct_invariant_eq_zero M hM f b hf hb hcont
        (fun p ↦ Z p) ⟨Lp.memLp Z, hZinv⟩
    have htoLp :
        (Lp.memLp Z).toLp (fun p ↦ Z p) = Z := by
      apply Lp.ext (μ := P.μ)
      exact (Lp.memLp Z).coeFn_toLp
    have hinner' : @inner ℂ (Lp ℂ 2 P.μ) _ Y Z = 0 := by
      rw [← htoLp]
      simpa only [Y, P] using hinner
    exact inner_eq_zero_symm.mpr hinner'
  have hproj : S.starProjection Y = 0 := by
    apply S.eq_starProjection_of_mem_orthogonal
    · exact S.zero_mem
    · simpa using hYorth
  exact hproj

/-- The symmetric fixed-projection statement: a continuous-spectral second
factor also annihilates the invariant projection of a separated product. -/
theorem separatedProduct_fixedProjection_eq_zero_of_second
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f b : M.X → ℂ) (hf : M.lpMember 2 f) (hb : M.lpMember 2 b)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hb.toLp b)) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Uiso :
        Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
      Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
    let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
      Uiso.toContinuousLinearMap
    let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
      LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.memLp_separatedProduct
        M hM f b hf hb).toLp
        (fun p : M.X × M.X ↦ f p.1 * b p.2)
    (S.orthogonalProjection Y : Lp ℂ 2 P.μ) = 0 := by
  dsimp only
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let Uiso :
      Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  let Y : Lp ℂ 2 P.μ :=
    (HilbertSchmidtInvariant.memLp_separatedProduct
      M hM f b hf hb).toLp
      (fun p : M.X × M.X ↦ f p.1 * b p.2)
  have hYorth : Y ∈ Sᗮ := by
    intro Z hZ
    have hfix : U Z = Z := hZ
    have hcoe := Lp.coeFn_compMeasurePreserving Z hP.2
    have hZinv :
        (fun p : M.X × M.X ↦ Z (productTransformation M p)) =ᵐ[M.μ.prod M.μ]
          (fun p ↦ Z p) := by
      change ⇑(U Z) =ᵐ[P.μ] (⇑Z) ∘ P.T at hcoe
      rw [hfix] at hcoe
      simpa only [P, ProductWeakMixing.productSystem,
        productTransformation, Function.comp_apply] using hcoe.symm
    have hinner :=
      inner_separatedProduct_invariant_eq_zero_of_second
        M hM f b hf hb hcont (fun p ↦ Z p) ⟨Lp.memLp Z, hZinv⟩
    have htoLp :
        (Lp.memLp Z).toLp (fun p ↦ Z p) = Z := by
      apply Lp.ext (μ := P.μ)
      exact (Lp.memLp Z).coeFn_toLp
    have hinner' : @inner ℂ (Lp ℂ 2 P.μ) _ Y Z = 0 := by
      rw [← htoLp]
      simpa only [Y, P] using hinner
    exact inner_eq_zero_symm.mpr hinner'
  have hproj : S.starProjection Y = 0 := by
    apply S.eq_starProjection_of_mem_orthogonal
    · exact S.zero_mem
    · simpa using hYorth
  exact hproj

/-- `Lp`-level form of continuous-spectrum annihilation in the first tensor
coordinate. -/
theorem productInvariantProjectionCLM_separatedProductLp_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) F) :
    productInvariantProjectionCLM M hM
      (separatedProductLp M hM F G) = 0 := by
  have hFto :
      (Lp.memLp F).toLp (fun x ↦ F x) = F := by
    apply Lp.ext
    exact (Lp.memLp F).coeFn_toLp
  have hcont' :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM)
        ((Lp.memLp F).toLp (fun x ↦ F x)) := by
    rw [hFto]
    exact hcont
  simpa only [productInvariantProjectionCLM, separatedProductLp] using
    separatedProduct_fixedProjection_eq_zero
      M hM (fun x ↦ F x) (fun x ↦ G x)
        (Lp.memLp F) (Lp.memLp G) hcont'

/-- `Lp`-level form of continuous-spectrum annihilation in the second tensor
coordinate. -/
theorem productInvariantProjectionCLM_separatedProductLp_eq_zero_of_second
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : Lp ℂ 2 M.μ)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) G) :
    productInvariantProjectionCLM M hM
      (separatedProductLp M hM F G) = 0 := by
  have hGto :
      (Lp.memLp G).toLp (fun x ↦ G x) = G := by
    apply Lp.ext
    exact (Lp.memLp G).coeFn_toLp
  have hcont' :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM)
        ((Lp.memLp G).toLp (fun x ↦ G x)) := by
    rw [hGto]
    exact hcont
  simpa only [productInvariantProjectionCLM, separatedProductLp] using
    separatedProduct_fixedProjection_eq_zero_of_second
      M hM (fun x ↦ F x) (fun x ↦ G x)
        (Lp.memLp F) (Lp.memLp G) hcont'

/-- A continuous component in the `00` vertex kills both axis pairings. -/
theorem cubePairingDefect_eq_zero_of_continuous_00
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) F00) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing]
  rw [
    productInvariantProjectionCLM_separatedProductLp_eq_zero
      M hM F00 F01 hcont,
    productInvariantProjectionCLM_separatedProductLp_eq_zero
      M hM F00 F10 hcont]
  simp

/-- A continuous component in the `01` vertex kills both axis pairings. -/
theorem cubePairingDefect_eq_zero_of_continuous_01
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) F01) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  have hstar := continuous_lpStar M hM F01 hcont
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing]
  rw [
    productInvariantProjectionCLM_separatedProductLp_eq_zero_of_second
      M hM F00 F01 hcont,
    productInvariantProjectionCLM_separatedProductLp_eq_zero
      M hM (ForwardKroneckerFactor.lpStar M F01)
        (ForwardKroneckerFactor.lpStar M F11) hstar]
  simp

/-- A continuous component in the `10` vertex kills both axis pairings. -/
theorem cubePairingDefect_eq_zero_of_continuous_10
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) F10) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  have hstar := continuous_lpStar M hM F10 hcont
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing]
  rw [
    productInvariantProjectionCLM_separatedProductLp_eq_zero
      M hM (ForwardKroneckerFactor.lpStar M F10)
        (ForwardKroneckerFactor.lpStar M F11) hstar,
    productInvariantProjectionCLM_separatedProductLp_eq_zero_of_second
      M hM F00 F10 hcont]
  simp

/-- A continuous component in the `11` vertex kills both axis pairings. -/
theorem cubePairingDefect_eq_zero_of_continuous_11
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) F11) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  have hstar := continuous_lpStar M hM F11 hcont
  simp only [cubePairingDefect, rowCubePairing, columnCubePairing]
  rw [
    productInvariantProjectionCLM_separatedProductLp_eq_zero_of_second
      M hM (ForwardKroneckerFactor.lpStar M F10)
        (ForwardKroneckerFactor.lpStar M F11) hstar,
    productInvariantProjectionCLM_separatedProductLp_eq_zero_of_second
      M hM (ForwardKroneckerFactor.lpStar M F01)
        (ForwardKroneckerFactor.lpStar M F11) hstar]
  simp

/-- Cube transposition for arbitrary `L²` inputs.  Each vector is split into
its almost-periodic projection and a continuous-spectral residual.  The
discrete four-vertex theorem handles the projected term, while every other
term vanishes by Cartesian invariant-projection orthogonality. -/
theorem cubePairingDefect_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F00 F01 F10 F11 : Lp ℂ 2 M.μ) :
    cubePairingDefect M hM F00 F01 F10 F11 = 0 := by
  let D := WeakSpectrum.koopmanData M hM
  let hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X ↦
      (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map X
  let A00 : Lp ℂ 2 M.μ :=
    AlmostPeriodicIsometry.almostPeriodicProjection D hU F00
  let A01 : Lp ℂ 2 M.μ :=
    AlmostPeriodicIsometry.almostPeriodicProjection D hU F01
  let A10 : Lp ℂ 2 M.μ :=
    AlmostPeriodicIsometry.almostPeriodicProjection D hU F10
  let A11 : Lp ℂ 2 M.μ :=
    AlmostPeriodicIsometry.almostPeriodicProjection D hU F11
  let C00 := F00 - A00
  let C01 := F01 - A01
  let C10 := F10 - A10
  let C11 := F11 - A11
  have hdec00 : F00 = A00 + C00 := by
    dsimp only [C00]
    abel
  have hdec01 : F01 = A01 + C01 := by
    dsimp only [C01]
    abel
  have hdec10 : F10 = A10 + C10 := by
    dsimp only [C10]
    abel
  have hdec11 : F11 = A11 + C11 := by
    dsimp only [C11]
    abel
  have hcont00 :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) C00 := by
    exact AlmostPeriodicIsometry.sub_almostPeriodicProjection_continuous
      D hU F00
  have hcont01 :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) C01 := by
    exact AlmostPeriodicIsometry.sub_almostPeriodicProjection_continuous
      D hU F01
  have hcont10 :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) C10 := by
    exact AlmostPeriodicIsometry.sub_almostPeriodicProjection_continuous
      D hU F10
  have hcont11 :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) C11 := by
    exact AlmostPeriodicIsometry.sub_almostPeriodicProjection_continuous
      D hU F11
  have hdisc00 :
      InDiscreteSpectralSubspace
        (WeakSpectrum.koopmanData M hM) A00 := by
    exact AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      D hU A00
        (AlmostPeriodicIsometry.almostPeriodicProjection_mem D hU F00)
  have hdisc01 :
      InDiscreteSpectralSubspace
        (WeakSpectrum.koopmanData M hM) A01 := by
    exact AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      D hU A01
        (AlmostPeriodicIsometry.almostPeriodicProjection_mem D hU F01)
  have hdisc10 :
      InDiscreteSpectralSubspace
        (WeakSpectrum.koopmanData M hM) A10 := by
    exact AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      D hU A10
        (AlmostPeriodicIsometry.almostPeriodicProjection_mem D hU F10)
  have hdisc11 :
      InDiscreteSpectralSubspace
        (WeakSpectrum.koopmanData M hM) A11 := by
    exact AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      D hU A11
        (AlmostPeriodicIsometry.almostPeriodicProjection_mem D hU F11)
  calc
    cubePairingDefect M hM F00 F01 F10 F11 =
        cubePairingDefect M hM A00 F01 F10 F11 +
          cubePairingDefect M hM C00 F01 F10 F11 := by
      rw [hdec00, cubePairingDefect_add_00]
    _ = cubePairingDefect M hM A00 F01 F10 F11 := by
      rw [cubePairingDefect_eq_zero_of_continuous_00
        M hM C00 F01 F10 F11 hcont00, add_zero]
    _ = cubePairingDefect M hM A00 A01 F10 F11 +
          cubePairingDefect M hM A00 C01 F10 F11 := by
      rw [hdec01, cubePairingDefect_add_01]
    _ = cubePairingDefect M hM A00 A01 F10 F11 := by
      rw [cubePairingDefect_eq_zero_of_continuous_01
        M hM A00 C01 F10 F11 hcont01, add_zero]
    _ = cubePairingDefect M hM A00 A01 A10 F11 +
          cubePairingDefect M hM A00 A01 C10 F11 := by
      rw [hdec10, cubePairingDefect_add_10]
    _ = cubePairingDefect M hM A00 A01 A10 F11 := by
      rw [cubePairingDefect_eq_zero_of_continuous_10
        M hM A00 A01 C10 F11 hcont10, add_zero]
    _ = cubePairingDefect M hM A00 A01 A10 A11 +
          cubePairingDefect M hM A00 A01 A10 C11 := by
      rw [hdec11, cubePairingDefect_add_11]
    _ = cubePairingDefect M hM A00 A01 A10 A11 := by
      rw [cubePairingDefect_eq_zero_of_continuous_11
        M hM A00 A01 A10 C11 hcont11, add_zero]
    _ = 0 :=
      cubePairingDefect_discrete_eq_zero
        M hM hErg A00 A01 A10 A11 hdisc00 hdisc01 hdisc10 hdisc11

/-- The tensor-conjugate square of a continuous-spectral vector has zero
projection onto the fixed subspace of the Cartesian-square Koopman
operator. -/
theorem tensorSquare_fixedProjection_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f)) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Uiso :
        Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
      Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
    let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
      Uiso.toContinuousLinearMap
    let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
      LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
        (TensorSquare M f)
    (S.orthogonalProjection Y : Lp ℂ 2 P.μ) = 0 := by
  simpa only [TensorSquare] using
    separatedProduct_fixedProjection_eq_zero
      M hM f (fun x ↦ star (f x)) hf hf.star hcont

/-- Ordinary Koopman averages of the tensor square of a
continuous-spectral vector converge to zero on the Cartesian square. -/
theorem tensorSquare_birkhoffAverage_tendsto_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f)) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let Uiso :
        Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
      Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
    let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
      Uiso.toContinuousLinearMap
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
        (TensorSquare M f)
    Tendsto (fun N ↦ birkhoffAverage ℂ U id N Y)
      Filter.atTop (nhds 0) := by
  dsimp only
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let Uiso :
      Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  let Y : Lp ℂ 2 P.μ :=
    (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
      (TensorSquare M f)
  have hnorm : ‖U‖ ≤ 1 := by
    apply U.opNorm_le_bound (by norm_num)
    intro Z
    change ‖Uiso Z‖ ≤ 1 * ‖Z‖
    rw [Uiso.norm_map, one_mul]
  have ht :=
    U.tendsto_birkhoffAverage_orthogonalProjection hnorm Y
  have hproj :
      (S.orthogonalProjection Y : Lp ℂ 2 P.μ) = 0 := by
    simpa only [P, hP, Uiso, U, S, Y] using
      tensorSquare_fixedProjection_eq_zero M hM f hf hcont
  change Tendsto (fun N ↦ birkhoffAverage ℂ U id N Y)
    Filter.atTop (nhds (S.orthogonalProjection Y : Lp ℂ 2 P.μ)) at ht
  rw [hproj] at ht
  exact ht

/-- The preceding zero limit is uniform over the starting point of the
averaging interval, because every shifted block is an isometric image of the
initial block. -/
theorem tensorSquare_uniform_shifted_cesaro_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f)) :
    let P := ProductWeakMixing.productSystem M M
    let hP := ProductWeakMixing.productSystem_mps M M hM hM
    let V :
        Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
      Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
    let Y : Lp ℂ 2 P.μ :=
      (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
        (TensorSquare M f)
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
        ∑ n ∈ Finset.range (N + 1),
          (V.toContinuousLinearMap^[i + n]) Y‖ < ε := by
  dsimp only
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  let V :
      Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let Y : Lp ℂ 2 P.μ :=
    (HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf).toLp
      (TensorSquare M f)
  have ht :
      Tendsto
        (fun N ↦ birkhoffAverage ℂ V.toContinuousLinearMap id N Y)
        atTop (nhds 0) := by
    simpa only [P, hP, V, Y] using
      tensorSquare_birkhoffAverage_tendsto_zero M hM f hf hcont
  intro ε hε
  have havg :
      ∀ᶠ N : ℕ in atTop,
        ‖birkhoffAverage ℂ V.toContinuousLinearMap id (N + 1) Y‖ < ε := by
    have hnorm :
        Tendsto
          (fun N ↦
            ‖birkhoffAverage ℂ V.toContinuousLinearMap id N Y‖)
          atTop (nhds 0) := by
      simpa using continuous_norm.continuousAt.tendsto.comp ht
    exact (tendsto_order.1
      (hnorm.comp (tendsto_add_atTop_nat 1))).2 ε hε
  filter_upwards [havg] with N hN
  intro i
  rw [← Khintchine.iterate_birkhoffAverage_eq_block V Y i (N + 1)]
  rw [Khintchine.iterate_isometry_norm]
  exact hN

/-- Conditional-expectation form of the Cartesian-square orthogonality:
the tensor square of a continuous-spectral vector has zero conditional
expectation onto the invariant sigma algebra of the product system. -/
theorem condExp_tensorSquare_invariant_eq_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f)
    (hcont :
      InContinuousSpectralSubspace
        (WeakSpectrum.koopmanData M hM) (hf.toLp f)) :
    condExp
        (MeasurableSpace.generateFrom (productInvariantSigmaAlgebra M))
        (M.μ.prod M.μ) (TensorSquare M f) =ᵐ[M.μ.prod M.μ] 0 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let P := ProductWeakMixing.productSystem M M
  let hP := ProductWeakMixing.productSystem_mps M M hM hM
  letI : IsProbabilityMeasure P.μ := hP.1
  let mInv : MeasurableSpace P.X :=
    MeasurableSpace.generateFrom (invariantSigmaAlgebra P)
  letI : MeasurableSpace P.X := P.measurableSpace
  have hm : mInv ≤ P.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro s hs
    exact hs.1
  letI : Fact (mInv ≤ P.measurableSpace) := ⟨hm⟩
  let hY := HilbertSchmidtInvariant.tensorSquare_memLp M hM f hf
  let Y : Lp ℂ 2 P.μ := hY.toLp (TensorSquare M f)
  let Uiso : Lp ℂ 2 P.μ →ₗᵢ[ℂ] Lp ℂ 2 P.μ :=
    Lp.compMeasurePreservingₗᵢ ℂ P.T hP.2
  let U : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ :=
    Uiso.toContinuousLinearMap
  let S : Submodule ℂ (Lp ℂ 2 P.μ) :=
    LinearMap.eqLocus U (1 : Lp ℂ 2 P.μ →L[ℂ] Lp ℂ 2 P.μ)
  let CEsub :=
    (condExpL2 (m := mInv) (m0 := P.measurableSpace)
      (μ := P.μ) ℂ ℂ hm) Y
  let CE : Lp ℂ 2 P.μ := (CEsub : Lp ℂ 2 P.μ)
  have hproj : (S.orthogonalProjection Y : Lp ℂ 2 P.μ) = 0 := by
    simpa only [P, hP, Uiso, U, S, Y, hY] using
      tensorSquare_fixedProjection_eq_zero M hM f hf hcont
  have hprojCE : (S.orthogonalProjection Y : Lp ℂ 2 P.μ) = CE := by
    simpa only [P, hP, Uiso, U, S, mInv, hm, Y, CE, CEsub] using
      MeanErgodicL2.fixedProjection_eq_condExpL2 P hP Y
  have hCEzero : CE = 0 := hprojCE.symm.trans hproj
  have hYint : Integrable (TensorSquare M f) P.μ :=
    hY.integrable (by norm_num)
  have hraw :
      (fun p ↦ CE p) =ᵐ[P.μ] condExp mInv P.μ (TensorSquare M f) := by
    exact hY.condExpL2_ae_eq_condExp' hm hYint
  have hCEcoe : (fun p ↦ CE p) =ᵐ[P.μ] 0 := by
    rw [hCEzero]
    exact Lp.coeFn_zero ℂ 2 P.μ
  have hz :
      condExp mInv P.μ (TensorSquare M f) =ᵐ[P.μ] 0 :=
    hraw.symm.trans hCEcoe
  simpa only [P, mInv] using hz

end Chapter02.MultipleKhintchineProductInvariant
