import Chapter02.Spectral.AlmostPeriodicIsometry
import Chapter02.Ergodic.ZeroDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Real

open Classical Filter Set Topology
open scoped BigOperators ComplexOrder

noncomputable section

namespace Chapter02.IsometryWiener

universe u

/-- The Hermitian two-sided extension of the forward correlation sequence of
an isometry. -/
def vectorCorrelation
    (D : HilbertOperatorData.{u}) (x : D.H) : ℤ → ℂ
  | Int.ofNat n => @inner ℂ D.H _ x ((D.U^[n]) x)
  | Int.negSucc n => star (@inner ℂ D.H _ x ((D.U^[n + 1]) x))

lemma iterate_inner_map_map
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x y : D.H) (n : ℕ) :
    @inner ℂ D.H _ ((D.U^[n]) x) ((D.U^[n]) y) =
      @inner ℂ D.H _ x y := by
  let V : D.H →ₗᵢ[ℂ] D.H :=
    { toLinearMap := D.U.toLinearMap
      norm_map' := hU }
  have hp (z : D.H) : (V ^ n) z = (D.U^[n]) z := by
    induction n generalizing z with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ']
        change D.U ((V ^ n) z) = (D.U^[n + 1]) z
        rw [ih, Function.iterate_succ_apply']
  have hi := (V ^ n).inner_map_map x y
  simpa only [hp] using hi

/-- A Toeplitz entry of the extended correlation is an inner product of
forward orbit points after translating both indices into `ℕ`. -/
lemma correlation_sub_eq_inner_shifted
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (N m n : ℕ) (hm : m ≤ N) (hn : n ≤ N) :
    vectorCorrelation D x ((m : ℤ) - (n : ℤ)) =
      @inner ℂ D.H _ ((D.U^[N - m]) x) ((D.U^[N - n]) x) := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hNk : N - (n + k) + k = N - n := by omega
    have hiter :
        (D.U^[N - n]) x =
          (D.U^[N - (n + k)]) ((D.U^[k]) x) := by
      rw [← Function.iterate_add_apply, hNk]
    rw [hiter, iterate_inner_map_map D hU]
    simp [vectorCorrelation]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have hNk : N - (m + k) + k = N - m := by omega
    have hiter :
        (D.U^[N - m]) x =
          (D.U^[N - (m + k)]) ((D.U^[k]) x) := by
      rw [← Function.iterate_add_apply, hNk]
    rw [hiter, iterate_inner_map_map D hU]
    have hsub : ((m : ℤ) - (m + k : ℕ)) = -(k : ℤ) := by omega
    rw [hsub]
    cases k with
    | zero => simp [vectorCorrelation]
    | succ k =>
        change star (@inner ℂ D.H _ x ((D.U^[k + 1]) x)) =
          @inner ℂ D.H _ ((D.U^[k + 1]) x) x
        exact inner_conj_symm (𝕜 := ℂ) ((D.U^[k + 1]) x) x

/-- Forward correlations of a linear isometry form a positive-definite
two-sided sequence. -/
theorem vectorCorrelation_positiveDefinite
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    IsPositiveDefinite (vectorCorrelation D x) := by
  intro N a
  let y : D.H := ∑ m : Fin (N + 1),
    star (a m) • (D.U^[N - (m : ℕ)]) x
  have hq :
      (∑ m : Fin (N + 1), ∑ n : Fin (N + 1),
        a m * star (a n) *
          vectorCorrelation D x
            (((m : ℕ) : ℤ) - ((n : ℕ) : ℤ))) =
        @inner ℂ D.H _ y y := by
    simp only [y, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    simp_rw [Finset.mul_sum]
    nth_rewrite 2 [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [correlation_sub_eq_inner_shifted D hU x N m n
      (Nat.le_of_lt_succ m.isLt) (Nat.le_of_lt_succ n.isLt)]
    simp
    ring
  rw [hq]
  constructor
  · exact inner_self_im (𝕜 := ℂ) y
  · have hre : (@inner ℂ D.H _ y y).re = ‖y‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) y)
    rw [hre]
    positivity

/-- Herglotz spectral measure of the forward orbit of a linear isometry. -/
theorem exists_spectralMeasure
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    ∃ μ : CircleMeasureData,
      ∀ n : ℕ, circleFourierCoefficient μ n =
        @inner ℂ D.H _ x ((D.U^[n]) x) := by
  obtain ⟨μ, hμ, _⟩ :=
    Herglotz.herglotz (vectorCorrelation D x)
      (vectorCorrelation_positiveDefinite D hU x)
  refine ⟨μ, ?_⟩
  intro n
  simpa [vectorCorrelation] using hμ (n : ℤ)

/-- Once the Herglotz measure of an isometric forward orbit is atomless, the
required square-correlation decay is exactly the already formalized circle
Wiener theorem. -/
theorem autocorrelation_sq_tendsto_zero_of_continuous_measure
    (D : HilbertOperatorData.{u}) (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ n : ℕ, circleFourierCoefficient μ n =
      @inner ℂ D.H _ x ((D.U^[n]) x))
    (hcont : IsContinuousCircleMeasure μ) :
    Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖ ^ 2)
      atTop (nhds 0) := by
  have hw := (SpectralWiener.circle_wiener_zero_iff_continuous μ).mpr hcont
  convert hw using 1
  funext N
  by_cases hN : N = 0
  · simp [hN]
  simp only [hN, if_false]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [hμ n, norm_inner_symm]

/-- The phase-modulated isometry used to detect an atom at `z`. -/
def modulatedOperator
    (D : HilbertOperatorData.{u}) (z : Circle) : D.H →L[ℂ] D.H :=
  star (z : ℂ) • D.U

lemma modulatedOperator_iterate
    (D : HilbertOperatorData.{u}) (z : Circle) (x : D.H) (n : ℕ) :
    ((modulatedOperator D z)^[n]) x =
      (star (z : ℂ) ^ n) • ((D.U^[n]) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp [modulatedOperator, pow_succ', smul_smul]
      rw [mul_comm]

lemma modulatedOperator_norm_le_one
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (z : Circle) :
    ‖modulatedOperator D z‖ ≤ 1 := by
  apply (modulatedOperator D z).opNorm_le_bound (by norm_num)
  intro x
  rw [modulatedOperator, ContinuousLinearMap.smul_apply, norm_smul, norm_star,
    Circle.norm_coe, hU]

/-- If `x` is orthogonal to all eigenvectors, every phase-modulated forward
Cesàro average converges to zero.  This is the mean-ergodic half of the
atom/eigenvector correspondence and requires no surjectivity. -/
theorem modulated_cesaro_tendsto_zero
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : InContinuousSpectralSubspace D x) (z : Circle) :
    Tendsto
      (fun N : ℕ => birkhoffAverage ℂ (modulatedOperator D z)
        _root_.id N x)
      atTop (nhds 0) := by
  let V := modulatedOperator D z
  let S : Submodule ℂ D.H :=
    LinearMap.eqLocus V (1 : D.H →L[ℂ] D.H)
  have hxS : x ∈ Sᗮ := by
    intro y hy
    have hyfix : V y = y := hy
    have hzy : D.U y = (z : ℂ) • y := by
      have hzunit : (z : ℂ) * star (z : ℂ) = 1 := by
        have hzstar : star (z : ℂ) = (z : ℂ)⁻¹ := by
          apply Complex.ext <;> simp [Complex.inv_def]
        rw [hzstar]
        apply mul_inv_cancel₀
        intro hz0
        have hnorm := Circle.norm_coe z
        simp [hz0] at hnorm
      change star (z : ℂ) • D.U y = y at hyfix
      calc
        D.U y = (1 : ℂ) • D.U y := (one_smul ℂ _).symm
        _ = ((z : ℂ) * star (z : ℂ)) • D.U y := by rw [hzunit]
        _ = (z : ℂ) • (star (z : ℂ) • D.U y) := by rw [smul_smul]
        _ = (z : ℂ) • y := congrArg (fun w : D.H => (z : ℂ) • w) hyfix
    by_cases hy0 : y = 0
    · simp [hy0]
    exact inner_eq_zero_symm.mpr (hx y ⟨hy0, z, hzy⟩)
  have hproj :
      (S.orthogonalProjection x : D.H) = 0 := by
    have hs : S.starProjection x = 0 := by
      apply S.eq_starProjection_of_mem_orthogonal
      · exact S.zero_mem
      · simpa using hxS
    exact hs
  have ht :=
    V.tendsto_birkhoffAverage_orthogonalProjection
      (modulatedOperator_norm_le_one D hU z) x
  change Tendsto
    (fun N : ℕ => birkhoffAverage ℂ V _root_.id N x)
      atTop (nhds (S.orthogonalProjection x : D.H)) at ht
  simpa [hproj] using ht

/-- Complex conjugation as a self-map of the unit circle. -/
def circleConj (z : Circle) : Circle :=
  ⟨star (z : ℂ), by simp [Submonoid.unitSphere]⟩

@[simp] lemma circleConj_coe (z : Circle) :
    (circleConj z : ℂ) = star (z : ℂ) := rfl

@[simp] lemma circleConj_circleConj (z : Circle) :
    circleConj (circleConj z) = z := by
  apply Subtype.ext
  simp [circleConj]

/-- The one-variable specialization of the circle kernel that detects the
atom at `z`. -/
def pointKernel (z : Circle) (N : ℕ) (w : Circle) : ℂ :=
  SpectralWiener.circleKernel N (w, z)

lemma pointKernel_measurable (z : Circle) (N : ℕ) :
    Measurable (pointKernel z N) := by
  unfold pointKernel
  exact (SpectralWiener.circleKernel_measurable N).comp
    (measurable_id.prod measurable_const)

lemma norm_pointKernel_le (z : Circle) (N : ℕ) (w : Circle) :
    ‖pointKernel z N w‖ ≤ 1 :=
  SpectralWiener.norm_circleKernel_le N (w, z)

lemma tendsto_pointKernel (z w : Circle) :
    Tendsto (fun N => pointKernel z N w) atTop
      (nhds (if w = z then 1 else 0)) := by
  simpa [pointKernel] using
    SpectralWiener.tendsto_circleKernel (w, z)

lemma tendsto_integral_pointKernel (μ : CircleMeasureData) (z : Circle) :
    Tendsto (fun N => ∫ w, pointKernel z N w ∂μ.μ) atTop
      (nhds (∫ w, (if w = z then (1 : ℂ) else 0) ∂μ.μ)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro N
    exact (pointKernel_measurable z N).aestronglyMeasurable
  · exact MeasureTheory.integrable_const 1
  · intro N
    filter_upwards [] with w
    simpa using norm_pointKernel_le z N w
  · filter_upwards [] with w
    exact tendsto_pointKernel z w

lemma integral_pointKernel_eq
    (D : HilbertOperatorData.{u}) (x : D.H) (μ : CircleMeasureData)
    (hμ : ∀ n : ℕ, circleFourierCoefficient μ n =
      @inner ℂ D.H _ x ((D.U^[n]) x))
    (z : Circle) (N : ℕ) :
    (∫ w, pointKernel z N w ∂μ.μ) =
      @inner ℂ D.H _ x
        (birkhoffAverage ℂ (modulatedOperator D z) _root_.id N x) := by
  by_cases hN : N = 0
  · simp [hN, pointKernel, SpectralWiener.circleKernel,
      SpectralWiener.geometricAverage, birkhoffAverage, birkhoffSum]
  rw [show pointKernel z N = fun w : Circle =>
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        (((w : ℂ) * star (z : ℂ)) ^ n) by
    funext w
    simp [pointKernel, SpectralWiener.circleKernel,
      SpectralWiener.geometricAverage, SpectralWiener.circleRatio, hN]]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum]
  · rw [birkhoffAverage, birkhoffSum, inner_smul_right,
      inner_sum]
    apply congrArg
    apply Finset.sum_congr rfl
    intro n hn
    simp_rw [mul_pow]
    rw [MeasureTheory.integral_mul_const]
    change circleFourierCoefficient μ n * star (z : ℂ) ^ n = _
    rw [hμ n, modulatedOperator_iterate]
    simp only [id_eq]
    rw [inner_smul_right]
    ring
  · intro n hn
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)

lemma integral_pointKernel_limit (μ : CircleMeasureData) (z : Circle) :
    (∫ w, (if w = z then (1 : ℂ) else 0) ∂μ.μ) =
      (μ.μ.real {z} : ℂ) := by
  change (∫ w, (if w = z then (1 : ℂ) else 0) ∂μ.μ) =
    ((μ.μ {z}).toReal : ℂ)
  rw [show (fun w : Circle => if w = z then (1 : ℂ) else 0) =
      ({z} : Set Circle).indicator (fun _ => (1 : ℂ)) by
    funext w
    by_cases hw : w = z <;> simp [Set.indicator, hw]]
  rw [MeasureTheory.integral_indicator
    (measurableSet_singleton z)]
  simp

/-- For a linear isometry, orthogonality to all eigenvectors forces every
Herglotz spectral measure of the forward correlation sequence to be atomless.
This is the non-surjective atom/eigenvector bridge. -/
theorem continuous_subspace_implies_continuous_measure
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : InContinuousSpectralSubspace D x)
    (μ : CircleMeasureData)
    (hμ : ∀ n : ℕ, circleFourierCoefficient μ n =
      @inner ℂ D.H _ x ((D.U^[n]) x)) :
    IsContinuousCircleMeasure μ := by
  intro q
  let z : Circle := q
  have havg := modulated_cesaro_tendsto_zero D hU x hx z
  have hinner :
      Tendsto
        (fun N => @inner ℂ D.H _ x
          (birkhoffAverage ℂ (modulatedOperator D z) _root_.id N x))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.inner havg
  have hk := tendsto_integral_pointKernel μ z
  rw [integral_pointKernel_limit] at hk
  have heq :
      (fun N => ∫ w, pointKernel z N w ∂μ.μ) =
        fun N => @inner ℂ D.H _ x
          (birkhoffAverage ℂ (modulatedOperator D z) _root_.id N x) := by
    funext N
    exact integral_pointKernel_eq D x μ hμ z N
  rw [heq] at hk
  have hzreal : μ.μ.real {z} = 0 := by
    exact_mod_cast tendsto_nhds_unique hk hinner
  have hz : μ.μ {z} = 0 :=
    (MeasureTheory.measureReal_eq_zero_iff).mp hzreal
  simpa [z] using hz

/-- Wiener square-correlation decay for the continuous spectral subspace of
an arbitrary linear isometry. -/
theorem continuous_autocorrelation_sq_tendsto_zero
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : InContinuousSpectralSubspace D x) :
    Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖ ^ 2)
      atTop (nhds 0) := by
  obtain ⟨μ, hμ⟩ := exists_spectralMeasure D hU x
  exact autocorrelation_sq_tendsto_zero_of_continuous_measure D x μ hμ
    (continuous_subspace_implies_continuous_measure D hU x hx μ hμ)

/-- The continuous component supplied by the almost-periodic projection has
Wiener square-correlation decay, with no surjectivity assumption. -/
theorem projection_residual_autocorrelation_sq_tendsto_zero
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) :
    Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          ‖@inner ℂ D.H _
            ((D.U^[n]) (x -
              AlmostPeriodicIsometry.almostPeriodicProjection D hU x))
            (x - AlmostPeriodicIsometry.almostPeriodicProjection D hU x)‖ ^ 2)
      atTop (nhds 0) :=
  continuous_autocorrelation_sq_tendsto_zero D hU _
    (AlmostPeriodicIsometry.sub_almostPeriodicProjection_continuous D hU x)

/-- Unsquared absolute autocorrelations also have Cesàro limit zero. -/
theorem continuous_autocorrelation_abs_cesaro
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : InContinuousSpectralSubspace D x) :
    cesaroTendsTo
      (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖) 0 := by
  have hw := continuous_autocorrelation_sq_tendsto_zero D hU x hx
  have hsq : cesaroTendsTo
      (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖ ^ 2) 0 := by
    unfold cesaroTendsTo seqTendsTo cesaroAverage
    have hcomp := hw.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun N : ℕ => if N + 1 = 0 then 0 else
      (((N + 1 : ℕ) : ℝ)⁻¹) * ∑ n ∈ Finset.range (N + 1),
        ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖ ^ 2) atTop (nhds 0) at hcomp
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  exact ZeroDensity.cesaro_norm_of_cesaro_norm_sq
    (fun n => @inner ℂ D.H _ ((D.U^[n]) x) x) hsq

end Chapter02.IsometryWiener
