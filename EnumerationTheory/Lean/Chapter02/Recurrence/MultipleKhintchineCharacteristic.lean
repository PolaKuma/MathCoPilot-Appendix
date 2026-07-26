import Chapter02.Recurrence.MultipleKhintchineKronecker
import Chapter02.Ergodic.CorrelationMean
import Chapter02.Recurrence.ForwardKroneckerFactor
import Chapter02.Recurrence.MultipleKhintchineSyndetic

open Classical Filter Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Chapter02.MultipleKhintchineCharacteristic

universe u

abbrev KData (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :=
  MultipleKhintchineKronecker.koopmanData M hM

/-- The Hilbert-valued bilinear progression sequence
`(U^n F) (U^(2n) G)`. -/
noncomputable def doubleKoopmanProduct
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) : MeasureTheory.Lp ℂ 2 M.μ :=
  MultipleKhintchineKronecker.lpPointwiseMul
    (((KData M hM).U^[n]) F)
    (((KData M hM).U^[2 * n]) G)
    (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM n F hFtop)

lemma doubleKoopmanProduct_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    (fun x ↦ doubleKoopmanProduct M hM F G hFtop n x) =ᵐ[M.μ]
      (fun x ↦
        (show MeasureTheory.Lp ℂ 2 M.μ from
          ((KData M hM).U^[n]) F) x *
        (show MeasureTheory.Lp ℂ 2 M.μ from
          ((KData M hM).U^[2 * n]) G) x) := by
  exact MultipleKhintchineKronecker.lpPointwiseMul_coe _ _ _

lemma norm_doubleKoopmanProduct_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (n : ℕ) :
    ‖doubleKoopmanProduct M hM F G hFtop n‖ ≤ C * ‖G‖ := by
  have hiterBound :=
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM n F C hFbound
  have hmul :=
    MultipleKhintchineKronecker.norm_lpPointwiseMul_le
      (((KData M hM).U^[n]) F)
      (((KData M hM).U^[2 * n]) G)
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM n F hFtop)
      C hC hiterBound
  calc
    ‖doubleKoopmanProduct M hM F G hFtop n‖ ≤
        C * ‖((KData M hM).U^[2 * n]) G‖ := hmul
    _ = C * ‖G‖ := by
      congr 1
      exact AlmostPeriodicIsometry.iterate_norm
        (KData M hM)
        (fun H ↦
          (MeasureTheory.Lp.compMeasurePreservingₗᵢ
            ℂ M.T hM.2).norm_map H)
        G (2 * n)

/-- Factoring a common `U^n` from a shifted bilinear progression term. -/
lemma doubleKoopmanProduct_add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (n h : ℕ) :
    doubleKoopmanProduct M hM F G hFtop (n + h) =
      ((KData M hM).U^[n])
        (MultipleKhintchineKronecker.lpPointwiseMul
          (((KData M hM).U^[h]) F)
          (((KData M hM).U^[n + 2 * h]) G)
          (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
            M hM h F hFtop)) := by
  rw [MultipleKhintchineKronecker.koopmanData_iter_lpPointwiseMul]
  unfold doubleKoopmanProduct
  congr 1
  · rw [← Function.iterate_add_apply]
  · rw [← Function.iterate_add_apply]
    congr 2
    omega

/-- Removing the common `U^n` from the inner product of two shifted
bilinear progression terms. -/
lemma inner_doubleKoopmanProduct_add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (n h k : ℕ) :
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (doubleKoopmanProduct M hM F G hFtop (n + k))
        (doubleKoopmanProduct M hM F G hFtop (n + h)) =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (MultipleKhintchineKronecker.lpPointwiseMul
          (((KData M hM).U^[k]) F)
          (((KData M hM).U^[n + 2 * k]) G)
          (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
            M hM k F hFtop))
        (MultipleKhintchineKronecker.lpPointwiseMul
          (((KData M hM).U^[h]) F)
          (((KData M hM).U^[n + 2 * h]) G)
          (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
            M hM h F hFtop)) := by
  rw [doubleKoopmanProduct_add, doubleKoopmanProduct_add]
  exact MultipleKhintchineKronecker.koopmanData_iter_inner M hM n _ _

/-- The fixed first-factor part arising in a van der Corput pair. -/
def leftPairFunction
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) (h k : ℕ) : M.X → ℂ :=
  fun x ↦
    (show MeasureTheory.Lp ℂ 2 M.μ from
      ((KData M hM).U^[h]) F) x *
    star ((show MeasureTheory.Lp ℂ 2 M.μ from
      ((KData M hM).U^[k]) F) x)

/-- The second-factor self-correlation arising in a van der Corput pair. -/
def rightPairFunction
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : MeasureTheory.Lp ℂ 2 M.μ) (h k : ℕ) : M.X → ℂ :=
  fun x ↦
    (show MeasureTheory.Lp ℂ 2 M.μ from
      ((KData M hM).U^[2 * h]) G) x *
    star ((show MeasureTheory.Lp ℂ 2 M.μ from
      ((KData M hM).U^[2 * k]) G) x)

lemma leftPairFunction_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (h k : ℕ) :
    MeasureTheory.MemLp (leftPairFunction M hM F h k) 2 M.μ := by
  exact
    ((MeasureTheory.Lp.memLp (((KData M hM).U^[k]) F)).star).mul
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM h F hFtop)

lemma rightPairFunction_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : MeasureTheory.Lp ℂ 2 M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (h k : ℕ) :
    MeasureTheory.MemLp (rightPairFunction M hM G h k) 2 M.μ := by
  exact
    ((MeasureTheory.Lp.memLp (((KData M hM).U^[2 * k]) G)).star).mul
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM (2 * h) G hGtop)

lemma star_leftPairFunction_memLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (h k : ℕ) :
    MeasureTheory.MemLp
      (fun x ↦ star (leftPairFunction M hM F h k x)) 2 M.μ :=
  (leftPairFunction_memLp M hM F hFtop h k).star

/-- Each shifted bilinear pair correlation is an ordinary one-parameter
ergodic correlation of two fixed functions. -/
lemma inner_shiftedProducts_eq_functionCorrelation
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (n h k : ℕ) :
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (MultipleKhintchineKronecker.lpPointwiseMul
          (((KData M hM).U^[k]) F)
          (((KData M hM).U^[n + 2 * k]) G)
          (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
            M hM k F hFtop))
        (MultipleKhintchineKronecker.lpPointwiseMul
          (((KData M hM).U^[h]) F)
          (((KData M hM).U^[n + 2 * h]) G)
          (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
            M hM h F hFtop)) =
      functionCorrelation M
        (rightPairFunction M hM G h k)
        (fun x ↦ star (leftPairFunction M hM F h k x)) n := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  have hGk :
      ((KData M hM).U^[n + 2 * k]) G =
        ((KData M hM).U^[n]) (((KData M hM).U^[2 * k]) G) := by
    rw [Function.iterate_add_apply]
  have hGh :
      ((KData M hM).U^[n + 2 * h]) G =
        ((KData M hM).U^[n]) (((KData M hM).U^[2 * h]) G) := by
    rw [Function.iterate_add_apply]
  filter_upwards [
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (((KData M hM).U^[k]) F)
      (((KData M hM).U^[n + 2 * k]) G)
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM k F hFtop),
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (((KData M hM).U^[h]) F)
      (((KData M hM).U^[n + 2 * h]) G)
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM h F hFtop),
    MultipleKhintchineKronecker.koopmanData_iter_ae
      M hM n (((KData M hM).U^[2 * k]) G),
    MultipleKhintchineKronecker.koopmanData_iter_ae
      M hM n (((KData M hM).U^[2 * h]) G)] with
      x hkprod hhprod hkiter hhiter
  simp only [rightPairFunction, leftPairFunction,
    RCLike.inner_apply, starRingEnd_apply]
  rw [hkprod, hhprod, hGk, hGh, hkiter, hhiter]
  simp only [star_mul, star_star]
  ring

/-- Ergodicity computes the Cesàro limit of every fixed van der Corput
pair in the bilinear progression sequence. -/
lemma tendsto_cesaro_inner_doubleKoopmanProduct_add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (h k : ℕ) :
    Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (doubleKoopmanProduct M hM F G hFtop (n + k))
            (doubleKoopmanProduct M hM F G hFtop (n + h)))
      atTop
      (nhds (productOfMeans M
        (rightPairFunction M hM G h k)
        (fun x ↦ star (leftPairFunction M hM F h k x)))) := by
  have hcorr :=
    CorrelationMean.ergodic_cesaroFunctionCorrelations
      M hM hErg
      (rightPairFunction M hM G h k)
      (fun x ↦ star (leftPairFunction M hM F h k x))
      (rightPairFunction_memLp M hM G hGtop h k)
      (star_leftPairFunction_memLp M hM F hFtop h k)
  convert hcorr using 1
  funext N
  by_cases hN : N = 0
  · simp [hN]
  · simp only [hN, if_false]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [inner_doubleKoopmanProduct_add
          M hM F G hFtop n h k,
      inner_shiftedProducts_eq_functionCorrelation
          M hM F G hFtop n h k]

lemma tendsto_cesaro_re_inner_doubleKoopmanProduct_add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (h k : ℕ) :
    Tendsto
      (fun N ↦ cesaroAverage
        (fun n ↦
          (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (doubleKoopmanProduct M hM F G hFtop (n + k))
            (doubleKoopmanProduct M hM F G hFtop (n + h))).re) N)
      atTop
      (nhds (productOfMeans M
        (rightPairFunction M hM G h k)
        (fun x ↦ star (leftPairFunction M hM F h k x))).re) := by
  have hc :=
    (tendsto_cesaro_inner_doubleKoopmanProduct_add
      M hM hErg F G hFtop hGtop h k).comp
        (tendsto_add_atTop_nat 1)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  convert hr using 1
  funext N
  unfold cesaroAverage
  change (((N + 1 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range (N + 1),
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (doubleKoopmanProduct M hM F G hFtop (n + k))
          (doubleKoopmanProduct M hM F G hFtop (n + h))).re) =
    (((((N + 1 : ℕ) : ℂ)⁻¹) *
      ∑ n ∈ Finset.range (N + 1),
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (doubleKoopmanProduct M hM F G hFtop (n + k))
          (doubleKoopmanProduct M hM F G hFtop (n + h))).re)
  have hscalar :
      (((N + 1 : ℕ) : ℂ)⁻¹) =
        ((((N + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact (Complex.ofReal_inv (((N + 1 : ℕ) : ℝ))).symm
  rw [hscalar, Complex.re_ofReal_mul]
  have hre :
      (∑ n ∈ Finset.range (N + 1),
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (doubleKoopmanProduct M hM F G hFtop (n + k))
          (doubleKoopmanProduct M hM F G hFtop (n + h))).re =
      ∑ n ∈ Finset.range (N + 1),
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (doubleKoopmanProduct M hM F G hFtop (n + k))
          (doubleKoopmanProduct M hM F G hFtop (n + h))).re := by
    induction Finset.range (N + 1) using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
        simp [Finset.sum_insert, hn, ih, Complex.add_re]
  rw [hre, Finset.mul_sum]

lemma integral_rightPairFunction
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : MeasureTheory.Lp ℂ 2 M.μ) (h k : ℕ) :
    ∫ x, rightPairFunction M hM G h k x ∂M.μ =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((KData M hM).U^[2 * k]) G)
        (((KData M hM).U^[2 * h]) G) := by
  rw [MeasureTheory.L2.inner_def]
  rfl

lemma norm_integral_star_leftPairFunction_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (h k : ℕ) :
    ‖∫ x, star (leftPairFunction M hM F h k x) ∂M.μ‖ ≤ C ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hh :=
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM h F C hFbound
  have hk :=
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM k F C hFbound
  have hpoint :
      ∀ᵐ x ∂M.μ,
        ‖star (leftPairFunction M hM F h k x)‖ ≤ C ^ 2 := by
    filter_upwards [hh, hk] with x hhx hkx
    simp only [norm_star, leftPairFunction, norm_mul]
    nlinarith [norm_nonneg
      ((show MeasureTheory.Lp ℂ 2 M.μ from
        ((KData M hM).U^[h]) F) x),
      norm_nonneg
      ((show MeasureTheory.Lp ℂ 2 M.μ from
        ((KData M hM).U^[k]) F) x)]
  simpa using MeasureTheory.norm_integral_le_of_norm_le_const hpoint

lemma norm_pairLimit_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (h k : ℕ) :
    ‖productOfMeans M
        (rightPairFunction M hM G h k)
        (fun x ↦ star (leftPairFunction M hM F h k x))‖ ≤
      C ^ 2 *
        ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (((KData M hM).U^[2 * k]) G)
          (((KData M hM).U^[2 * h]) G)‖ := by
  unfold productOfMeans
  rw [norm_mul, norm_star, integral_rightPairFunction]
  let z : ℂ :=
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (((KData M hM).U^[2 * k]) G)
      (((KData M hM).U^[2 * h]) G)
  have hleft :=
    norm_integral_star_leftPairFunction_le M hM F C hC hFbound h k
  change ‖z‖ *
      ‖∫ x, star (leftPairFunction M hM F h k x) ∂M.μ‖ ≤
    C ^ 2 * ‖z‖
  calc
    _ ≤ ‖z‖ * C ^ 2 :=
      mul_le_mul_of_nonneg_left hleft (norm_nonneg z)
    _ = C ^ 2 * ‖z‖ := mul_comm _ _

lemma integral_star_leftPairFunction
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) (h k : ℕ) :
    ∫ x, star (leftPairFunction M hM F h k x) ∂M.μ =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((KData M hM).U^[h]) F)
        (((KData M hM).U^[k]) F) := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp [leftPairFunction, mul_comm]

lemma norm_integral_rightPairFunction_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C)
    (h k : ℕ) :
    ‖∫ x, rightPairFunction M hM G h k x ∂M.μ‖ ≤ C ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  have hh :=
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM (2 * h) G C hGbound
  have hk :=
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM (2 * k) G C hGbound
  have hpoint :
      ∀ᵐ x ∂M.μ, ‖rightPairFunction M hM G h k x‖ ≤ C ^ 2 := by
    filter_upwards [hh, hk] with x hhx hkx
    simp only [rightPairFunction, norm_mul, norm_star]
    nlinarith [norm_nonneg
      ((show MeasureTheory.Lp ℂ 2 M.μ from
        ((KData M hM).U^[2 * h]) G) x),
      norm_nonneg
      ((show MeasureTheory.Lp ℂ 2 M.μ from
        ((KData M hM).U^[2 * k]) G) x)]
  simpa using MeasureTheory.norm_integral_le_of_norm_le_const hpoint

lemma norm_pairLimit_le_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C)
    (h k : ℕ) :
    ‖productOfMeans M
        (rightPairFunction M hM G h k)
        (fun x ↦ star (leftPairFunction M hM F h k x))‖ ≤
      C ^ 2 *
        ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (((KData M hM).U^[h]) F)
          (((KData M hM).U^[k]) F)‖ := by
  unfold productOfMeans
  rw [norm_mul, norm_star, integral_star_leftPairFunction]
  let z : ℂ :=
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (((KData M hM).U^[h]) F)
      (((KData M hM).U^[k]) F)
  have hright :=
    norm_integral_rightPairFunction_le M hM G C hC hGbound h k
  change ‖∫ x, rightPairFunction M hM G h k x ∂M.μ‖ * ‖z‖ ≤
    C ^ 2 * ‖z‖
  exact mul_le_mul_of_nonneg_right hright (norm_nonneg z)

/-- For a fixed row, every nonnegative correlation at a given distance
occurs at most twice. -/
lemma sum_range_split_distance_le
    (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r)
    (H h : ℕ) (hh : h < H) :
    (Finset.range H).sum
        (fun k ↦ if k ≤ h then a (h - k) else a (k - h)) ≤
      2 * (Finset.range H).sum a := by
  let S₁ := (Finset.range H).filter (fun k ↦ k ≤ h)
  let S₂ := (Finset.range H).filter (fun k ↦ ¬ k ≤ h)
  have hsplit :
      (Finset.range H).sum
          (fun k ↦ if k ≤ h then a (h - k) else a (k - h)) =
        S₁.sum (fun k ↦ a (h - k)) +
          S₂.sum (fun k ↦ a (k - h)) := by
    rw [show (Finset.range H).sum
          (fun k ↦ if k ≤ h then a (h - k) else a (k - h)) =
        ((Finset.range H).filter (fun k ↦ k ≤ h)).sum
            (fun k ↦ if k ≤ h then a (h - k) else a (k - h)) +
          ((Finset.range H).filter (fun k ↦ ¬ k ≤ h)).sum
            (fun k ↦ if k ≤ h then a (h - k) else a (k - h)) by
      exact (Finset.sum_filter_add_sum_filter_not
        (Finset.range H) (fun k ↦ k ≤ h)
        (fun k ↦ if k ≤ h then a (h - k) else a (k - h))).symm]
    dsimp only [S₁, S₂]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Finset.mem_filter.mp hk).2]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [if_neg (Finset.mem_filter.mp hk).2]
  have h₁ :
      S₁.sum (fun k ↦ a (h - k)) ≤
        (Finset.range H).sum a := by
    let e : ℕ → ℕ := fun k ↦ h - k
    have hinj : Set.InjOn e S₁ := by
      intro x hx y hy hxy
      change x ∈ (Finset.range H).filter (fun k ↦ k ≤ h) at hx
      change y ∈ (Finset.range H).filter (fun k ↦ k ≤ h) at hy
      have hxle : x ≤ h := (Finset.mem_filter.mp hx).2
      have hyle : y ≤ h := (Finset.mem_filter.mp hy).2
      dsimp [e] at hxy
      omega
    have himage : S₁.image e ⊆ Finset.range H := by
      intro r hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      apply Finset.mem_range.mpr
      change k ∈ (Finset.range H).filter (fun k ↦ k ≤ h) at hk
      have hkh : k ≤ h := (Finset.mem_filter.mp hk).2
      dsimp [e]
      omega
    calc
      S₁.sum (fun k ↦ a (h - k)) =
          (S₁.image e).sum a := by
        rw [Finset.sum_image hinj]
      _ ≤ (Finset.range H).sum a :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun r hr hnot ↦ ha r)
  have h₂ :
      S₂.sum (fun k ↦ a (k - h)) ≤
        (Finset.range H).sum a := by
    let e : ℕ → ℕ := fun k ↦ k - h
    have hinj : Set.InjOn e S₂ := by
      intro x hx y hy hxy
      change x ∈ (Finset.range H).filter (fun k ↦ ¬ k ≤ h) at hx
      change y ∈ (Finset.range H).filter (fun k ↦ ¬ k ≤ h) at hy
      have hhx : h < x := by
        have := (Finset.mem_filter.mp hx).2
        omega
      have hhy : h < y := by
        have := (Finset.mem_filter.mp hy).2
        omega
      dsimp [e] at hxy
      omega
    have himage : S₂.image e ⊆ Finset.range H := by
      intro r hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      apply Finset.mem_range.mpr
      change k ∈ (Finset.range H).filter (fun k ↦ ¬ k ≤ h) at hk
      have hkH : k < H := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      dsimp [e]
      omega
    calc
      S₂.sum (fun k ↦ a (k - h)) =
          (S₂.image e).sum a := by
        rw [Finset.sum_image hinj]
      _ ≤ (Finset.range H).sum a :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun r hr hnot ↦ ha r)
  rw [hsplit]
  linarith

/-- Absolute Koopman autocorrelation sampled at even times. -/
def evenAutocorrelationNorm
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : MeasureTheory.Lp ℂ 2 M.μ) (r : ℕ) : ℝ :=
  ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
    (((KData M hM).U^[2 * r]) G) G‖

/-- Absolute Koopman autocorrelation at ordinary (rather than even) times. -/
def autocorrelationNorm
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) (r : ℕ) : ℝ :=
  ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
    (((KData M hM).U^[r]) F) F‖

lemma norm_inner_iterates
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ) (h k : ℕ) :
    ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((KData M hM).U^[h]) F)
        (((KData M hM).U^[k]) F)‖ =
      if h ≤ k then autocorrelationNorm M hM F (k - h)
      else autocorrelationNorm M hM F (h - k) := by
  by_cases hhk : h ≤ k
  · rw [if_pos hhk]
    have hexp : k = h + (k - h) := by omega
    have hvec :
        ((KData M hM).U^[k]) F =
          ((KData M hM).U^[h])
            (((KData M hM).U^[k - h]) F) := by
      rw [hexp, Function.iterate_add_apply]
      congr 2
      omega
    rw [hvec,
      MultipleKhintchineKronecker.koopmanData_iter_inner
        M hM h F (((KData M hM).U^[k - h]) F)]
    exact norm_inner_symm _ _
  · rw [if_neg hhk]
    have hkh : k ≤ h := by omega
    have hexp : h = k + (h - k) := by omega
    have hvec :
        ((KData M hM).U^[h]) F =
          ((KData M hM).U^[k])
            (((KData M hM).U^[h - k]) F) := by
      rw [hexp, Function.iterate_add_apply]
      congr 2
      omega
    rw [hvec,
      MultipleKhintchineKronecker.koopmanData_iter_inner
        M hM k (((KData M hM).U^[h - k]) F) F]
    rfl

lemma norm_inner_even_iterates
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : MeasureTheory.Lp ℂ 2 M.μ) (h k : ℕ) :
    ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((KData M hM).U^[2 * k]) G)
        (((KData M hM).U^[2 * h]) G)‖ =
      if k ≤ h then evenAutocorrelationNorm M hM G (h - k)
      else evenAutocorrelationNorm M hM G (k - h) := by
  by_cases hkh : k ≤ h
  · rw [if_pos hkh]
    have hexp : 2 * h = 2 * k + 2 * (h - k) := by omega
    have hvec :
        ((KData M hM).U^[2 * h]) G =
          ((KData M hM).U^[2 * k])
            (((KData M hM).U^[2 * (h - k)]) G) := by
      rw [hexp, Function.iterate_add_apply]
    rw [hvec,
      MultipleKhintchineKronecker.koopmanData_iter_inner
        M hM (2 * k) G (((KData M hM).U^[2 * (h - k)]) G)]
    exact norm_inner_symm _ _
  · rw [if_neg hkh]
    have hhk : h ≤ k := by omega
    have hexp : 2 * k = 2 * h + 2 * (k - h) := by omega
    have hvec :
        ((KData M hM).U^[2 * k]) G =
          ((KData M hM).U^[2 * h])
            (((KData M hM).U^[2 * (k - h)]) G) := by
      rw [hexp, Function.iterate_add_apply]
    rw [hvec,
      MultipleKhintchineKronecker.koopmanData_iter_inner
        M hM (2 * h) (((KData M hM).U^[2 * (k - h)]) G) G]
    rfl

lemma sum_pairLimit_norm_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (H : ℕ) :
    (Finset.range H).sum (fun h ↦
      (Finset.range H).sum (fun k ↦
        ‖productOfMeans M
          (rightPairFunction M hM G h k)
          (fun x ↦ star (leftPairFunction M hM F h k x))‖)) ≤
      2 * (H : ℝ) * C ^ 2 *
        (Finset.range H).sum (evenAutocorrelationNorm M hM G) := by
  calc
    _ ≤ (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          C ^ 2 *
            ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (((KData M hM).U^[2 * k]) G)
              (((KData M hM).U^[2 * h]) G)‖)) := by
      gcongr with h hh k hk
      exact norm_pairLimit_le M hM F G C hC hFbound h k
    _ = C ^ 2 * (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (((KData M hM).U^[2 * k]) G)
            (((KData M hM).U^[2 * h]) G)‖)) := by
      simp_rw [Finset.mul_sum]
    _ ≤ C ^ 2 * ((H : ℝ) *
          (2 * (Finset.range H).sum
            (evenAutocorrelationNorm M hM G))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      calc
        _ ≤ (Finset.range H).sum (fun _h ↦
            2 * (Finset.range H).sum
              (evenAutocorrelationNorm M hM G)) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [show (Finset.range H).sum (fun k ↦
              ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
                (((KData M hM).U^[2 * k]) G)
                (((KData M hM).U^[2 * h]) G)‖) =
              (Finset.range H).sum (fun k ↦
                if k ≤ h then
                  evenAutocorrelationNorm M hM G (h - k)
                else evenAutocorrelationNorm M hM G (k - h)) by
            apply Finset.sum_congr rfl
            intro k hk
            exact norm_inner_even_iterates M hM G h k]
          exact sum_range_split_distance_le
            (evenAutocorrelationNorm M hM G)
            (fun r ↦ norm_nonneg _) H h (Finset.mem_range.mp hh)
        _ = (H : ℝ) * (2 * (Finset.range H).sum
              (evenAutocorrelationNorm M hM G)) := by simp
    _ = _ := by ring

/-- Symmetric pair-limit estimate used when the first dynamic factor is
continuous-spectral and the second one is merely bounded. -/
lemma sum_pairLimit_norm_le_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C)
    (H : ℕ) :
    (Finset.range H).sum (fun h ↦
      (Finset.range H).sum (fun k ↦
        ‖productOfMeans M
          (rightPairFunction M hM G h k)
          (fun x ↦ star (leftPairFunction M hM F h k x))‖)) ≤
      2 * (H : ℝ) * C ^ 2 *
        (Finset.range H).sum (autocorrelationNorm M hM F) := by
  calc
    _ ≤ (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          C ^ 2 *
            ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (((KData M hM).U^[h]) F)
              (((KData M hM).U^[k]) F)‖)) := by
      gcongr with h hh k hk
      exact norm_pairLimit_le_left M hM F G C hC hGbound h k
    _ = C ^ 2 * (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (((KData M hM).U^[h]) F)
            (((KData M hM).U^[k]) F)‖)) := by
      simp_rw [Finset.mul_sum]
    _ ≤ C ^ 2 * ((H : ℝ) *
          (2 * (Finset.range H).sum
            (autocorrelationNorm M hM F))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      calc
        _ ≤ (Finset.range H).sum (fun _h ↦
            2 * (Finset.range H).sum
              (autocorrelationNorm M hM F)) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [show (Finset.range H).sum (fun k ↦
              ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
                (((KData M hM).U^[h]) F)
                (((KData M hM).U^[k]) F)‖) =
              (Finset.range H).sum (fun k ↦
                if k ≤ h then
                  autocorrelationNorm M hM F (h - k)
                else autocorrelationNorm M hM F (k - h)) by
            apply Finset.sum_congr rfl
            intro k hk
            rw [norm_inner_iterates M hM F h k]
            by_cases hkh : h ≤ k
            · rw [if_pos hkh]
              by_cases heq : h = k
              · subst k
                simp
              · rw [if_neg (by omega)]
            · rw [if_neg hkh, if_pos (by omega)]]
          exact sum_range_split_distance_le
            (autocorrelationNorm M hM F)
            (fun r ↦ norm_nonneg _) H h (Finset.mem_range.mp hh)
        _ = (H : ℝ) * (2 * (Finset.range H).sum
              (autocorrelationNorm M hM F)) := by simp
    _ = _ := by ring

/-- A nonnegative sequence with zero Cesàro mean also has arbitrarily small
averages along the even subsequence. -/
lemma exists_even_sum_lt_of_cesaro_zero
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hzero : cesaroTendsTo a 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧
      (Finset.range H).sum (fun r ↦ a (2 * r)) < δ * (H : ℝ) := by
  unfold cesaroTendsTo seqTendsTo at hzero
  rw [Metric.tendsto_atTop] at hzero
  obtain ⟨N₀, hN₀⟩ := hzero (δ / 2) (by positivity)
  let H := N₀ + 1
  have hH : 0 < H := by dsimp [H]; omega
  have hlarge : N₀ ≤ 2 * H - 1 := by
    dsimp [H]
    omega
  have havgdist := hN₀ (2 * H - 1) hlarge
  have htwoH : 2 * H - 1 + 1 = 2 * H := by omega
  have havg_nonneg :
      0 ≤ cesaroAverage a (2 * H - 1) := by
    unfold cesaroAverage
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun n hn ↦ ha n)
  have havg :
      ((2 * H : ℕ) : ℝ)⁻¹ *
          (Finset.range (2 * H)).sum a < δ / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg havg_nonneg] at havgdist
    unfold cesaroAverage at havgdist
    rw [htwoH] at havgdist
    exact havgdist
  have hsub :
      (Finset.range H).sum (fun r ↦ a (2 * r)) ≤
        (Finset.range (2 * H)).sum a := by
    let e : ℕ → ℕ := fun r ↦ 2 * r
    have hinj : Set.InjOn e (Finset.range H) := by
      intro x hx y hy hxy
      dsimp [e] at hxy
      omega
    have himage :
        (Finset.range H).image e ⊆ Finset.range (2 * H) := by
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
      apply Finset.mem_range.mpr
      have hrH := Finset.mem_range.mp hr
      dsimp [e]
      omega
    calc
      (Finset.range H).sum (fun r ↦ a (2 * r)) =
          ((Finset.range H).image e).sum a := by
        rw [Finset.sum_image hinj]
      _ ≤ (Finset.range (2 * H)).sum a :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun n hn hnot ↦ ha n)
  refine ⟨H, hH, ?_⟩
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have h2Hreal : (0 : ℝ) < 2 * H := by positivity
  have hfull :
      (Finset.range (2 * H)).sum a < δ * (H : ℝ) := by
    have havg' :
        (2 * (H : ℝ))⁻¹ *
            (Finset.range (2 * H)).sum a < δ / 2 := by
      simpa using havg
    rw [inv_mul_lt_iff₀ h2Hreal] at havg'
    nlinarith
  exact lt_of_le_of_lt hsub hfull

lemma exists_small_evenAutocorrelation_sum
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : MeasureTheory.Lp ℂ 2 M.μ)
    (hGcont : InContinuousSpectralSubspace (KData M hM) G)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧
      (Finset.range H).sum (evenAutocorrelationNorm M hM G) <
        δ * (H : ℝ) := by
  have hcorr :=
    MultipleKhintchineKronecker.koopman_continuous_autocorrelation_abs_cesaro
      M hM G hGcont
  simpa only [evenAutocorrelationNorm] using
    exists_even_sum_lt_of_cesaro_zero
      (fun n ↦
        ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (((KData M hM).U^[n]) G) G‖)
      (fun n ↦ norm_nonneg _) hcorr δ hδ

lemma exists_sum_lt_of_cesaro_zero
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hzero : cesaroTendsTo a 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧
      (Finset.range H).sum a < δ * (H : ℝ) := by
  unfold cesaroTendsTo seqTendsTo at hzero
  rw [Metric.tendsto_atTop] at hzero
  obtain ⟨N₀, hN₀⟩ := hzero δ hδ
  let H := N₀ + 1
  have hH : 0 < H := by dsimp [H]; omega
  have havgdist := hN₀ N₀ le_rfl
  have havg_nonneg : 0 ≤ cesaroAverage a N₀ := by
    unfold cesaroAverage
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun n hn ↦ ha n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg havg_nonneg] at havgdist
  refine ⟨H, hH, ?_⟩
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  unfold cesaroAverage at havgdist
  change ((H : ℝ)⁻¹) * (Finset.range H).sum a < δ at havgdist
  rw [inv_mul_lt_iff₀ hHreal] at havgdist
  nlinarith

lemma exists_small_autocorrelation_sum
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hFcont : InContinuousSpectralSubspace (KData M hM) F)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧
      (Finset.range H).sum (autocorrelationNorm M hM F) <
        δ * (H : ℝ) := by
  have hcorr :=
    MultipleKhintchineKronecker.koopman_continuous_autocorrelation_abs_cesaro
      M hM F hFcont
  simpa only [autocorrelationNorm] using
    exists_sum_lt_of_cesaro_zero
      (fun n ↦
        ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (((KData M hM).U^[n]) F) F‖)
      (fun n ↦ norm_nonneg _) hcorr δ hδ

/-- If the second factor is continuous-spectral, the bilinear progression
sequence satisfies the complete block-decay hypothesis of van der Corput. -/
theorem doubleKoopmanProduct_hasBlockDecay
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hGcont : InContinuousSpectralSubspace (KData M hM) G) :
    VanDerCorput.HasVanDerCorputBlockDecay
      (doubleKoopmanProduct M hM F G hFtop) := by
  intro δ hδ
  let η : ℝ := δ / (4 * (C ^ 2 + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨H, hH, heven⟩ :=
    exists_small_evenAutocorrelation_sum M hM G hGcont η hη
  refine ⟨H, hH, ?_⟩
  let L : ℝ :=
    (Finset.range H).sum (fun h ↦
      (Finset.range H).sum (fun k ↦
        (productOfMeans M
          (rightPairFunction M hM G h k)
          (fun x ↦ star (leftPairFunction M hM F h k x))).re))
  have hlim :
      Tendsto
        (fun N ↦ cesaroAverage
          (fun n ↦ ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
            (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (doubleKoopmanProduct M hM F G hFtop (n + k))
              (doubleKoopmanProduct M hM F G hFtop (n + h))).re) N)
        atTop (nhds L) := by
    have hsums :=
      tendsto_finset_sum (Finset.range H) (fun h hh ↦
        tendsto_finset_sum (Finset.range H) (fun k hk ↦
          tendsto_cesaro_re_inner_doubleKoopmanProduct_add
            M hM hErg F G hFtop hGtop h k))
    convert hsums using 1
    · funext N
      unfold cesaroAverage
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_comm]
  have hLnorm :
      L ≤ (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          ‖productOfMeans M
            (rightPairFunction M hM G h k)
            (fun x ↦ star (leftPairFunction M hM F h k x))‖)) := by
    dsimp [L]
    gcongr with h hh k hk
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hsumBound :=
    sum_pairLimit_norm_le M hM F G C hC hFbound H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hstrict :
      L < δ * (H : ℝ) ^ 2 := by
    calc
      L ≤ (Finset.range H).sum (fun h ↦
          (Finset.range H).sum (fun k ↦
            ‖productOfMeans M
              (rightPairFunction M hM G h k)
              (fun x ↦ star (leftPairFunction M hM F h k x))‖)) :=
        hLnorm
      _ ≤ 2 * (H : ℝ) * C ^ 2 *
          (Finset.range H).sum (evenAutocorrelationNorm M hM G) :=
        hsumBound
      _ ≤ 2 * (H : ℝ) * C ^ 2 * (η * (H : ℝ)) := by
        have hcoef : 0 ≤ 2 * (H : ℝ) * C ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left heven.le hcoef
      _ < δ * (H : ℝ) ^ 2 := by
        have hratio : 2 * C ^ 2 * η < δ := by
          dsimp [η]
          have hden : 0 < 4 * (C ^ 2 + 1) := by positivity
          rw [div_eq_mul_inv]
          calc
            2 * C ^ 2 * (δ * (4 * (C ^ 2 + 1))⁻¹) =
                δ * (2 * C ^ 2 / (4 * (C ^ 2 + 1))) := by ring
            _ < δ * 1 := by
              apply mul_lt_mul_of_pos_left _ hδ
              rw [div_lt_one hden]
              nlinarith [sq_nonneg C]
            _ = δ := mul_one _
        nlinarith [sq_pos_of_pos hHreal]
  exact (tendsto_order.1 hlim).2 _ hstrict

/-- If the second factor belongs to the continuous spectral subspace, then
the bilinear progression `(U^n F) (U^(2n) G)` has zero Cesàro mean in
`L²`.  This is the characteristic-factor van der Corput step. -/
theorem doubleKoopmanProduct_cesaro_tendsto_zero
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (hGcont : InContinuousSpectralSubspace (KData M hM) G) :
    Tendsto
      (fun N : ℕ ↦ (((N + 1 : ℕ) : ℂ)⁻¹) •
        ∑ n ∈ Finset.range (N + 1),
          doubleKoopmanProduct M hM F G hFtop n)
      atTop (nhds 0) := by
  exact VanDerCorput.vectorCesaro_tendsto_zero_of_blockDecay
    (doubleKoopmanProduct M hM F G hFtop)
    (C * ‖G‖)
    (norm_doubleKoopmanProduct_le M hM F G hFtop C hC hFbound)
    (doubleKoopmanProduct_hasBlockDecay
      M hM hErg F G hFtop hGtop C hC hFbound hGcont)

/-- Symmetric block-decay statement: now the first dynamic factor is
continuous-spectral, while the second one is bounded. -/
theorem doubleKoopmanProduct_hasBlockDecay_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C)
    (hFcont : InContinuousSpectralSubspace (KData M hM) F) :
    VanDerCorput.HasVanDerCorputBlockDecay
      (doubleKoopmanProduct M hM F G hFtop) := by
  intro δ hδ
  let η : ℝ := δ / (4 * (C ^ 2 + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨H, hH, hcorr⟩ :=
    exists_small_autocorrelation_sum M hM F hFcont η hη
  refine ⟨H, hH, ?_⟩
  let L : ℝ :=
    (Finset.range H).sum (fun h ↦
      (Finset.range H).sum (fun k ↦
        (productOfMeans M
          (rightPairFunction M hM G h k)
          (fun x ↦ star (leftPairFunction M hM F h k x))).re))
  have hlim :
      Tendsto
        (fun N ↦ cesaroAverage
          (fun n ↦ ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
            (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
              (doubleKoopmanProduct M hM F G hFtop (n + k))
              (doubleKoopmanProduct M hM F G hFtop (n + h))).re) N)
        atTop (nhds L) := by
    have hsums :=
      tendsto_finset_sum (Finset.range H) (fun h hh ↦
        tendsto_finset_sum (Finset.range H) (fun k hk ↦
          tendsto_cesaro_re_inner_doubleKoopmanProduct_add
            M hM hErg F G hFtop hGtop h k))
    convert hsums using 1
    · funext N
      unfold cesaroAverage
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_comm]
  have hLnorm :
      L ≤ (Finset.range H).sum (fun h ↦
        (Finset.range H).sum (fun k ↦
          ‖productOfMeans M
            (rightPairFunction M hM G h k)
            (fun x ↦ star (leftPairFunction M hM F h k x))‖)) := by
    dsimp [L]
    gcongr with h hh k hk
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hsumBound :=
    sum_pairLimit_norm_le_left M hM F G C hC hGbound H
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hstrict :
      L < δ * (H : ℝ) ^ 2 := by
    calc
      L ≤ (Finset.range H).sum (fun h ↦
          (Finset.range H).sum (fun k ↦
            ‖productOfMeans M
              (rightPairFunction M hM G h k)
              (fun x ↦ star (leftPairFunction M hM F h k x))‖)) :=
        hLnorm
      _ ≤ 2 * (H : ℝ) * C ^ 2 *
          (Finset.range H).sum (autocorrelationNorm M hM F) :=
        hsumBound
      _ ≤ 2 * (H : ℝ) * C ^ 2 * (η * (H : ℝ)) := by
        have hcoef : 0 ≤ 2 * (H : ℝ) * C ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hcorr.le hcoef
      _ < δ * (H : ℝ) ^ 2 := by
        have hratio : 2 * C ^ 2 * η < δ := by
          dsimp [η]
          have hden : 0 < 4 * (C ^ 2 + 1) := by positivity
          rw [div_eq_mul_inv]
          calc
            2 * C ^ 2 * (δ * (4 * (C ^ 2 + 1))⁻¹) =
                δ * (2 * C ^ 2 / (4 * (C ^ 2 + 1))) := by ring
            _ < δ * 1 := by
              apply mul_lt_mul_of_pos_left _ hδ
              rw [div_lt_one hden]
              nlinarith [sq_nonneg C]
            _ = δ := mul_one _
        nlinarith [sq_pos_of_pos hHreal]
  exact (tendsto_order.1 hlim).2 _ hstrict

/-- If the first factor belongs to the continuous spectral subspace and both
factors are bounded, the same bilinear progression has zero Cesàro mean. -/
theorem doubleKoopmanProduct_cesaro_tendsto_zero_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x ↦ G x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (hFcont : InContinuousSpectralSubspace (KData M hM) F) :
    Tendsto
      (fun N : ℕ ↦ (((N + 1 : ℕ) : ℂ)⁻¹) •
        ∑ n ∈ Finset.range (N + 1),
          doubleKoopmanProduct M hM F G hFtop n)
      atTop (nhds 0) := by
  exact VanDerCorput.vectorCesaro_tendsto_zero_of_blockDecay
    (doubleKoopmanProduct M hM F G hFtop)
    (CF * ‖G‖)
    (norm_doubleKoopmanProduct_le M hM F G hFtop CF hCF hFbound)
    (doubleKoopmanProduct_hasBlockDecay_left
      M hM hErg F G hFtop hGtop CG hCG hGbound hFcont)

/-- The `L²` indicator vector used to compare set intersections with
Hilbert-space progression correlations. -/
noncomputable def indicatorLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    MeasureTheory.Lp ℂ 2 M.μ :=
  (CorrelationMean.indicatorComplex_memLp M hM A hA 2).toLp
    (CorrelationMean.indicatorComplex A)

lemma indicatorLp_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    (fun x ↦ indicatorLp M hM A hA x) =ᵐ[M.μ]
      CorrelationMean.indicatorComplex A :=
  (CorrelationMean.indicatorComplex_memLp M hM A hA 2).coeFn_toLp

lemma indicatorLp_norm_le_one
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∀ᵐ x ∂M.μ, ‖indicatorLp M hM A hA x‖ ≤ (1 : ℝ) := by
  filter_upwards [indicatorLp_coe M hM A hA] with x hx
  rw [hx]
  by_cases hxin : x ∈ A <;>
    simp [CorrelationMean.indicatorComplex, Set.indicator, hxin]

lemma indicatorLp_mem_top
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) :
    MeasureTheory.MemLp (fun x ↦ indicatorLp M hM A hA x) ⊤ M.μ := by
  exact MeasureTheory.memLp_top_of_bound
    (MeasureTheory.Lp.memLp (indicatorLp M hM A hA)).1 1
    (indicatorLp_norm_le_one M hM A hA)

lemma indicatorLp_iterate_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    (fun x ↦
      (show MeasureTheory.Lp ℂ 2 M.μ from
        ((KData M hM).U^[n]) (indicatorLp M hM A hA)) x) =ᵐ[M.μ]
      (fun x ↦ CorrelationMean.indicatorComplex A ((M.T^[n]) x)) := by
  refine
    (MultipleKhintchineKronecker.koopmanData_iter_ae M hM n
      (indicatorLp M hM A hA)).trans ?_
  simpa only [Function.comp_apply] using
    (hM.2.iterate n).quasiMeasurePreserving.ae_eq
      (indicatorLp_coe M hM A hA)

/-- Products of bounded forward-Kronecker iterates remain in the
almost-periodic subspace. -/
lemma doubleKoopmanProduct_almostPeriodic
    (M : System.{u}) (hM : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hFap : IsAlmostPeriodicVector (KData M hM.1) F)
    (hGap : IsAlmostPeriodicVector (KData M hM.1) G)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (n : ℕ) :
    IsAlmostPeriodicVector (KData M hM.1)
      (doubleKoopmanProduct M hM.1 F G hFtop n) := by
  unfold doubleKoopmanProduct
  apply MultipleKhintchineKronecker.almostPeriodic_mul_of_bounded_left
    M hM
      (((KData M hM.1).U^[2 * n]) G)
      (((KData M hM.1).U^[n]) F)
  · exact AlmostPeriodicIsometry.iterate_almostPeriodic
      (KData M hM.1) G hGap (2 * n)
  · exact AlmostPeriodicIsometry.iterate_almostPeriodic
      (KData M hM.1) F hFap n
  · exact hC
  · exact MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM.1 n F C hFbound

/-- The set-theoretic triple intersection is exactly the real part of the
corresponding `L²` bilinear correlation. -/
lemma tripleCorrelation_eq_re_inner_indicator
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    MultipleKhintchineSyndetic.tripleCorrelation M A n =
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (indicatorLp M hM A hA)
        (doubleKoopmanProduct M hM
          (indicatorLp M hM A hA)
          (indicatorLp M hM A hA)
          (indicatorLp_mem_top M hM A hA) n)).re := by
  let F := indicatorLp M hM A hA
  let C : Set M.X :=
    A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A
  have hC : MeasurableSet C := by
    dsimp [C]
    exact (hA.inter
      (hA.preimage (hM.2.measurable.iterate n))).inter
      (hA.preimage (hM.2.measurable.iterate (2 * n)))
  have hfun :
      (fun x ↦ @inner ℂ ℂ _ (F x)
        (doubleKoopmanProduct M hM F F
          (indicatorLp_mem_top M hM A hA) n x)) =ᵐ[M.μ]
        CorrelationMean.indicatorComplex C := by
    filter_upwards [
      indicatorLp_coe M hM A hA,
      doubleKoopmanProduct_coe M hM F F
        (indicatorLp_mem_top M hM A hA) n,
      indicatorLp_iterate_coe M hM A hA n,
      indicatorLp_iterate_coe M hM A hA (2 * n)]
        with x hFx hprod hn h2n
    simp only [RCLike.inner_apply, starRingEnd_apply]
    rw [hprod, hn, h2n, hFx]
    by_cases hx0 : x ∈ A <;>
      by_cases hx1 : (M.T^[n]) x ∈ A <;>
      by_cases hx2 : (M.T^[2 * n]) x ∈ A <;>
      simp [CorrelationMean.indicatorComplex, Set.indicator, C,
        preimageIter, Chapter01.iterateMap, hx0, hx1, hx2]
  unfold MultipleKhintchineSyndetic.tripleCorrelation
  rw [MeasureTheory.L2.inner_def,
    MeasureTheory.integral_congr_ae hfun,
    CorrelationMean.integral_indicatorComplex M C hC]
  simp [C]

/-- The concrete clipped forward-Kronecker indicator vector is exactly the
`L²` conditional expectation of the complex indicator vector. -/
lemma forwardKroneckerIndicatorLp_eq_condExp_indicatorLp
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA =
      ((MeasureTheory.condExpL2
          (m := ForwardKroneckerFactor.forwardKroneckerMeasurableSpace M hM)
          (m0 := M.measurableSpace) (μ := M.μ) ℂ ℂ
          (ForwardKroneckerFactor.forwardKroneckerMeasurableSpace_le M hM))
        (indicatorLp M hM.1 A hA) :
        MeasureTheory.Lp ℂ 2 M.μ) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let mK := ForwardKroneckerFactor.forwardKroneckerMeasurableSpace M hM
  let r : M.X → ℝ := A.indicator (fun _ ↦ (1 : ℝ))
  have hrint : MeasureTheory.Integrable r M.μ := by
    have hrTop : MeasureTheory.MemLp r ⊤ M.μ :=
      MeasureTheory.memLp_indicator_const ⊤ hA 1 (Or.inr (by simp))
    exact hrTop.integrable (by simp)
  have hcomm :
      Complex.ofRealCLM ∘ M.μ[r | mK] =ᵐ[M.μ]
        M.μ[Complex.ofRealCLM ∘ r | mK] :=
    Complex.ofRealCLM.comp_condExp_comm hrint
  have hraw :
      (Complex.ofRealCLM ∘ r) =
        CorrelationMean.indicatorComplex A := by
    funext x
    by_cases hx : x ∈ A <;>
      simp [r, CorrelationMean.indicatorComplex, Set.indicator, hx]
  have hfint :
      MeasureTheory.Integrable
        (CorrelationMean.indicatorComplex A) M.μ :=
    (CorrelationMean.indicatorComplex_memLp M hM.1 A hA 2).integrable
      (by norm_num)
  have hcond :=
    (CorrelationMean.indicatorComplex_memLp M hM.1 A hA 2).condExpL2_ae_eq_condExp'
      (𝕜 := ℂ)
      (ForwardKroneckerFactor.forwardKroneckerMeasurableSpace_le M hM)
      hfint
  apply MeasureTheory.Lp.ext
  filter_upwards [
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp_coe_clipped
      M hM A hA,
    ForwardKroneckerFactor.forwardKroneckerIndicator_ae_clipped
      M hM A hA,
    hcond, hcomm] with x hgclip hgraw hce hc
  rw [hgclip, ← hgraw]
  change (M.μ[r | mK] x : ℂ) =
    (show ℂ from
      ((MeasureTheory.condExpL2
          (m := mK) (m0 := M.measurableSpace) (μ := M.μ) ℂ ℂ
          (ForwardKroneckerFactor.forwardKroneckerMeasurableSpace_le M hM))
        (indicatorLp M hM.1 A hA) :
        MeasureTheory.Lp ℂ 2 M.μ) x)
  simp only [indicatorLp]
  rw [hce]
  rw [← hraw, ← hc]
  rfl

lemma indicator_sub_forwardKronecker_continuous
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    InContinuousSpectralSubspace (KData M hM.1)
      (indicatorLp M hM.1 A hA -
        ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA) := by
  rw [forwardKroneckerIndicatorLp_eq_condExp_indicatorLp M hM A hA]
  exact ForwardKroneckerFactor.sub_condExpL2_forwardKronecker_continuous
    M hM (indicatorLp M hM.1 A hA)

lemma forwardKroneckerIndicatorLp_norm_le_one
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∀ᵐ x ∂M.μ,
      ‖ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA x‖ ≤
        (1 : ℝ) := by
  filter_upwards [
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp_coe_clipped
      M hM A hA] with x hx
  rw [hx]
  exact
    ForwardKroneckerFactor.forwardKroneckerIndicatorClipped_norm_le_one
      M hM A x

lemma forwardKroneckerIndicatorLp_mem_top
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    MeasureTheory.MemLp
      (fun x ↦
        ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA x)
      ⊤ M.μ := by
  exact MeasureTheory.memLp_top_of_bound
    (MeasureTheory.Lp.memLp
      (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)).1
    1 (forwardKroneckerIndicatorLp_norm_le_one M hM A hA)

lemma indicatorResidual_norm_le_two
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    ∀ᵐ x ∂M.μ,
      ‖(indicatorLp M hM.1 A hA -
        ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA) x‖ ≤
        (2 : ℝ) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub
      (indicatorLp M hM.1 A hA)
      (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA),
    indicatorLp_norm_le_one M hM.1 A hA,
    forwardKroneckerIndicatorLp_norm_le_one M hM A hA] with
      x hsub hf hg
  rw [hsub]
  calc
    ‖indicatorLp M hM.1 A hA x -
        ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA x‖ ≤
      ‖indicatorLp M hM.1 A hA x‖ +
        ‖ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA x‖ :=
      norm_sub_le _ _
    _ ≤ 2 := by linarith

lemma indicatorResidual_mem_top
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    MeasureTheory.MemLp
      (fun x ↦
        (indicatorLp M hM.1 A hA -
          ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA) x)
      ⊤ M.μ := by
  exact MeasureTheory.memLp_top_of_bound
    (MeasureTheory.Lp.memLp
      (indicatorLp M hM.1 A hA -
        ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)).1
    2 (indicatorResidual_norm_le_two M hM A hA)

/-- The time-zero continuous residual is exactly orthogonal to every
two-fold product of forward-Kronecker iterates. -/
lemma inner_indicatorResidual_doubleKronecker_eq_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (indicatorLp M hM.1 A hA -
        ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
      (doubleKoopmanProduct M hM.1
        (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
        (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
        (forwardKroneckerIndicatorLp_mem_top M hM A hA) n) = 0 := by
  apply AlmostPeriodicIsometry.continuous_inner_almostPeriodic_eq_zero
    (KData M hM.1)
    (fun G ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map G)
  · exact indicator_sub_forwardKronecker_continuous M hM A hA
  · exact doubleKoopmanProduct_almostPeriodic
      M hM
      (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
      (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
      (forwardKroneckerIndicatorLp_mem_top M hM A hA)
      (ForwardKroneckerFactor.forwardKroneckerIndicatorLp_almostPeriodic
        M hM A hA)
      (ForwardKroneckerFactor.forwardKroneckerIndicatorLp_almostPeriodic
        M hM A hA)
      1 (by norm_num)
      (forwardKroneckerIndicatorLp_norm_le_one M hM A hA) n

lemma doubleKoopmanProduct_sub_right
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (n : ℕ) :
    doubleKoopmanProduct M hM F (G - H) hFtop n =
      doubleKoopmanProduct M hM F G hFtop n -
        doubleKoopmanProduct M hM F H hFtop n := by
  unfold doubleKoopmanProduct
  have hiter :
      ((KData M hM).U^[2 * n]) (G - H) =
        ((KData M hM).U^[2 * n]) G -
          ((KData M hM).U^[2 * n]) H := by
    induction (2 * n) with
    | zero => simp
    | succ m ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih, map_sub]
  rw [hiter, MultipleKhintchineKronecker.lpPointwiseMul_sub_right]

lemma doubleKoopmanProduct_sub_left
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ)
    (hHtop : MeasureTheory.MemLp (fun x ↦ H x) ⊤ M.μ)
    (hFHtop : MeasureTheory.MemLp (fun x ↦ (F - H) x) ⊤ M.μ)
    (n : ℕ) :
    doubleKoopmanProduct M hM (F - H) G hFHtop n =
      doubleKoopmanProduct M hM F G hFtop n -
        doubleKoopmanProduct M hM H G hHtop n := by
  have hiter :
      ((KData M hM).U^[n]) (F - H) =
        ((KData M hM).U^[n]) F -
          ((KData M hM).U^[n]) H := by
    induction n with
    | zero => simp
    | succ m ih =>
        simp only [Function.iterate_succ_apply']
        rw [ih, map_sub]
  apply MeasureTheory.Lp.ext
  filter_upwards [
    doubleKoopmanProduct_coe M hM (F - H) G hFHtop n,
    doubleKoopmanProduct_coe M hM F G hFtop n,
    doubleKoopmanProduct_coe M hM H G hHtop n,
    MeasureTheory.Lp.coeFn_sub
      (doubleKoopmanProduct M hM F G hFtop n)
      (doubleKoopmanProduct M hM H G hHtop n),
    MeasureTheory.Lp.coeFn_sub
      (((KData M hM).U^[n]) F)
      (((KData M hM).U^[n]) H)] with
      x hl hfg hhg hout hitersub
  have hxiter :
      (show MeasureTheory.Lp ℂ 2 M.μ from
        ((KData M hM).U^[n]) (F - H)) x =
      (show MeasureTheory.Lp ℂ 2 M.μ from
        ((KData M hM).U^[n]) F -
          ((KData M hM).U^[n]) H) x :=
    congrArg (fun Z : MeasureTheory.Lp ℂ 2 M.μ ↦ Z x) hiter
  rw [hl, hout]
  simp only [Pi.sub_apply]
  rw [hfg, hhg, hxiter, hitersub]
  simp only [Pi.sub_apply]
  ring

/-- Pointwise telescoping of the original triple correlation against its
forward-Kronecker counterpart.  The time-zero residual vanishes exactly,
leaving only the two dynamic residual terms controlled by van der Corput. -/
lemma tripleCorrelation_sub_forwardKronecker
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    MultipleKhintchineSyndetic.tripleCorrelation M A n -
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA n =
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (indicatorLp M hM.1 A hA)
        (doubleKoopmanProduct M hM.1
          (indicatorLp M hM.1 A hA)
          (indicatorLp M hM.1 A hA -
            ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
          (indicatorLp_mem_top M hM.1 A hA) n)).re +
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (indicatorLp M hM.1 A hA)
        (doubleKoopmanProduct M hM.1
          (indicatorLp M hM.1 A hA -
            ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
          (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA)
          (indicatorResidual_mem_top M hM A hA) n)).re := by
  let F := indicatorLp M hM.1 A hA
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let R := F - G
  have hFtop := indicatorLp_mem_top M hM.1 A hA
  have hGtop := forwardKroneckerIndicatorLp_mem_top M hM A hA
  have hRtop := indicatorResidual_mem_top M hM A hA
  let PFF := doubleKoopmanProduct M hM.1 F F hFtop n
  let PFG := doubleKoopmanProduct M hM.1 F G hFtop n
  let PGG := doubleKoopmanProduct M hM.1 G G hGtop n
  let PFR := doubleKoopmanProduct M hM.1 F R hFtop n
  let PRG := doubleKoopmanProduct M hM.1 R G hRtop n
  have hpfr : PFR = PFF - PFG := by
    simpa only [PFR, PFF, PFG, R, F, G] using
      doubleKoopmanProduct_sub_right M hM.1 F F G hFtop n
  have hprg : PRG = PFG - PGG := by
    simpa only [PRG, PFG, PGG, R, F, G] using
      doubleKoopmanProduct_sub_left
        M hM.1 F G G hFtop hGtop hRtop n
  have horth :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ R PGG = 0 := by
    simpa only [R, PGG, F, G] using
      inner_indicatorResidual_doubleKronecker_eq_zero M hM A hA n
  have houter :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PGG =
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G PGG := by
    rw [← sub_eq_zero, ← inner_sub_left]
    exact horth
  have hcomplex :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFF -
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G PGG =
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFR +
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PRG := by
    rw [hpfr, hprg, inner_sub_right, inner_sub_right, houter]
    ring
  rw [tripleCorrelation_eq_re_inner_indicator M hM.1 A hA n]
  unfold ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
  change
    (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFF).re -
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G PGG).re =
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PFR).re +
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F PRG).re
  rw [← Complex.sub_re, hcomplex, Complex.add_re]

/-- Taking the inner product with a fixed vector and then real parts
preserves zero Cesàro convergence of a Hilbert-valued sequence. -/
lemma tendsto_cesaro_re_inner_of_vector
    (M : System.{u})
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (v : ℕ → MeasureTheory.Lp ℂ 2 M.μ)
    (hv :
      Tendsto
        (fun N : ℕ ↦ (((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n)
        atTop (nhds 0)) :
    Tendsto
      (fun N ↦ cesaroAverage
        (fun n ↦
          (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v n)).re) N)
      atTop (nhds 0) := by
  have hcont :
      Continuous (fun Z : MeasureTheory.Lp ℂ 2 M.μ ↦
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F Z) :=
    continuous_const.inner continuous_id
  have hi :
      Tendsto
        (fun N : ℕ ↦
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
            ((((N + 1 : ℕ) : ℂ)⁻¹) •
              ∑ n ∈ Finset.range (N + 1), v n))
        atTop (nhds 0) := by
    simpa using hcont.continuousAt.tendsto.comp hv
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hi
  convert hre using 1
  funext N
  unfold cesaroAverage
  simp only [Function.comp_apply]
  simp only [inner_smul_right, inner_sum, Complex.mul_re,
    Complex.inv_re, Complex.inv_im]
  simp only [Complex.natCast_re, Complex.natCast_im,
    Complex.normSq_natCast, zero_div, neg_zero, zero_mul, sub_zero]
  have hsum_re :
      (∑ n ∈ Finset.range (N + 1),
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v n)).re =
      ∑ n ∈ Finset.range (N + 1),
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v n)).re := by
    change Complex.reAddGroupHom
      (∑ n ∈ Finset.range (N + 1),
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F (v n)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  rw [hsum_re]
  have hNR : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The original triple progression correlation and its forward-Kronecker
model have the same Cesàro asymptotics. -/
theorem tripleCorrelation_sub_forwardKronecker_cesaro_tendsto_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    Tendsto
      (fun N ↦ cesaroAverage
        (fun n ↦
          MultipleKhintchineSyndetic.tripleCorrelation M A n -
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA n) N)
      atTop (nhds 0) := by
  let F := indicatorLp M hM.1 A hA
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let R := F - G
  have hFtop := indicatorLp_mem_top M hM.1 A hA
  have hGtop := forwardKroneckerIndicatorLp_mem_top M hM A hA
  have hRtop := indicatorResidual_mem_top M hM A hA
  have hRcont := indicator_sub_forwardKronecker_continuous M hM A hA
  have hright :=
    doubleKoopmanProduct_cesaro_tendsto_zero
      M hM.1 hM F R hFtop hRtop 1 (by norm_num)
      (indicatorLp_norm_le_one M hM.1 A hA) hRcont
  have hleft :=
    doubleKoopmanProduct_cesaro_tendsto_zero_left
      M hM.1 hM R G hRtop hGtop 2 1
      (by norm_num) (by norm_num)
      (indicatorResidual_norm_le_two M hM A hA)
      (forwardKroneckerIndicatorLp_norm_le_one M hM A hA)
      hRcont
  have hr :=
    tendsto_cesaro_re_inner_of_vector M F
      (doubleKoopmanProduct M hM.1 F R hFtop) hright
  have hl :=
    tendsto_cesaro_re_inner_of_vector M F
      (doubleKoopmanProduct M hM.1 R G hRtop) hleft
  have hadd := hr.add hl
  convert hadd using 1
  · funext N
    unfold cesaroAverage
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 2
    funext n
    exact tripleCorrelation_sub_forwardKronecker M hM A hA n
  · norm_num

end Chapter02.MultipleKhintchineCharacteristic
