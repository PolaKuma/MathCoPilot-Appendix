import Chapter02.Ergodic.MeanErgodicL2
import Chapter02.Ergodic.CorrelationMean

noncomputable section

open Classical Filter MeasureTheory

namespace Chapter02
namespace Khintchine

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma iterate_isometry_norm (V : E →ₗᵢ[ℂ] E) (n : ℕ) (x : E) :
    ‖(V.toContinuousLinearMap^[n]) x‖ = ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ‖V ((V.toContinuousLinearMap^[n]) x)‖ = ‖x‖
      rw [V.norm_map, ih]

lemma iterate_fixed (V : E →ₗᵢ[ℂ] E) {x : E} (hx : V x = x) (n : ℕ) :
    (V.toContinuousLinearMap^[n]) x = x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      exact hx

lemma iterate_birkhoffAverage_sub_fixed_norm
    (V : E →ₗᵢ[ℂ] E) (F G : E) (hG : V G = G) (i N : ℕ) :
    ‖(V.toContinuousLinearMap^[i])
        (birkhoffAverage ℂ V.toContinuousLinearMap id N F) - G‖ =
      ‖birkhoffAverage ℂ V.toContinuousLinearMap id N F - G‖ := by
  have hGi := iterate_fixed V hG i
  calc
    _ = ‖(V.toContinuousLinearMap ^ i)
        (birkhoffAverage ℂ V.toContinuousLinearMap id N F) -
          (V.toContinuousLinearMap ^ i) G‖ := by
      rw [ContinuousLinearMap.coe_pow, hGi]
    _ = ‖(V.toContinuousLinearMap ^ i)
        (birkhoffAverage ℂ V.toContinuousLinearMap id N F - G)‖ := by
      rw [map_sub]
    _ = _ := by
      rw [ContinuousLinearMap.coe_pow]
      exact iterate_isometry_norm V i _

lemma iterate_birkhoffAverage_eq_block
    (V : E →ₗᵢ[ℂ] E) (F : E) (i N : ℕ) :
    (V.toContinuousLinearMap^[i])
        (birkhoffAverage ℂ V.toContinuousLinearMap id N F) =
      (N : ℂ)⁻¹ • ∑ j ∈ Finset.range N,
        (V.toContinuousLinearMap^[i + j]) F := by
  simp only [birkhoffAverage, birkhoffSum, id_eq]
  rw [← ContinuousLinearMap.coe_pow, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← ContinuousLinearMap.coe_pow]
  rw [← ContinuousLinearMap.mul_apply, ← pow_add]

lemma re_inner_iterate_birkhoffAverage_eq_block
    (V : E →ₗᵢ[ℂ] E) (F : E) (i N : ℕ) :
    (@inner ℂ E _ F ((V.toContinuousLinearMap^[i])
        (birkhoffAverage ℂ V.toContinuousLinearMap id N F))).re =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
        (@inner ℂ E _ F ((V.toContinuousLinearMap^[i + j]) F)).re := by
  rw [iterate_birkhoffAverage_eq_block]
  simp only [inner_smul_right, inner_sum, Complex.mul_re,
    Complex.inv_re, Complex.inv_im]
  simp only [Complex.natCast_re, Complex.natCast_im,
    Complex.normSq_natCast, zero_div, neg_zero, zero_mul, sub_zero]
  have hsum_re :
      (∑ j ∈ Finset.range N,
        @inner ℂ E _ F ((V.toContinuousLinearMap^[i + j]) F)).re =
      ∑ j ∈ Finset.range N,
        (@inner ℂ E _ F ((V.toContinuousLinearMap^[i + j]) F)).re := by
    change Complex.reAddGroupHom
      (∑ j ∈ Finset.range N,
        @inner ℂ E _ F ((V.toContinuousLinearMap^[i + j]) F)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rfl
  rw [hsum_re]
  by_cases hN : N = 0
  · subst N
    simp
  · have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp

lemma inner_recurrence_isSyndetic
    (V : E →ₗᵢ[ℂ] E) (F G : E) (r : ℝ)
    (hG : V G = G)
    (havg : Tendsto (fun N =>
      birkhoffAverage ℂ V.toContinuousLinearMap id N F) atTop (nhds G))
    (hlower : r ≤ (@inner ℂ E _ F G).re)
    {ε : ℝ} (hε : 0 < ε) :
    IsSyndetic {n : ℕ |
      r - ε < (@inner ℂ E _ F ((V.toContinuousLinearMap^[n]) F)).re} := by
  let δ : ℝ := ε / (‖F‖ + 1)
  have hden : 0 < ‖F‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hnorm : Tendsto (fun N =>
      ‖birkhoffAverage ℂ V.toContinuousLinearMap id N F - G‖)
      atTop (nhds 0) := by
    exact (tendsto_iff_norm_sub_tendsto_zero.mp havg)
  have hevent : ∀ᶠ N in atTop,
      ‖birkhoffAverage ℂ V.toContinuousLinearMap id N F - G‖ < δ :=
    (tendsto_order.mp hnorm).2 δ hδ
  rcases Filter.eventually_atTop.mp hevent with ⟨N₀, hN₀⟩
  let N := N₀ + 1
  have hNpos : 0 < N := by dsimp [N]; omega
  have havg_close :
      ‖birkhoffAverage ℂ V.toContinuousLinearMap id N F - G‖ < δ :=
    hN₀ N (by dsimp [N]; omega)
  refine ⟨N, hNpos, ?_⟩
  intro i
  by_contra hnone
  push_neg at hnone
  have hcoeff (j : ℕ) (hj : j ∈ Finset.range N) :
      (@inner ℂ E _ F ((V.toContinuousLinearMap^[i + j]) F)).re ≤ r - ε := by
    apply le_of_not_gt
    intro hgood
    have hfar := hnone (i + j) hgood (Nat.le_add_right i j)
    have hjlt := Finset.mem_range.mp hj
    omega
  have hsum :
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
          (@inner ℂ E _ F ((V.toContinuousLinearMap^[i + j]) F)).re ≤
        r - ε := by
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ _j ∈ Finset.range N, (r - ε) := by
        gcongr with j hj
        exact hcoeff j hj
      _ = r - ε := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
        field_simp
  let H := (V.toContinuousLinearMap^[i])
    (birkhoffAverage ℂ V.toContinuousLinearMap id N F)
  have hHG : ‖H - G‖ < δ := by
    change ‖(V.toContinuousLinearMap^[i])
      (birkhoffAverage ℂ V.toContinuousLinearMap id N F) - G‖ < δ
    rw [iterate_birkhoffAverage_sub_fixed_norm V F G hG i N]
    exact havg_close
  have hinner_error :
      |(@inner ℂ E _ F H).re - (@inner ℂ E _ F G).re| < ε := by
    have hre :
        |(@inner ℂ E _ F H).re - (@inner ℂ E _ F G).re| ≤
          ‖@inner ℂ E _ F (H - G)‖ := by
      calc
        _ = |(@inner ℂ E _ F H - @inner ℂ E _ F G).re| := rfl
        _ ≤ ‖@inner ℂ E _ F H - @inner ℂ E _ F G‖ :=
          Complex.abs_re_le_norm _
        _ = _ := by rw [inner_sub_right]
    have hcs : ‖@inner ℂ E _ F (H - G)‖ ≤ ‖F‖ * ‖H - G‖ :=
      norm_inner_le_norm F (H - G)
    have hmul_le : ‖F‖ * ‖H - G‖ ≤ (‖F‖ + 1) * ‖H - G‖ := by
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (norm_nonneg _)
    have hmul_lt : (‖F‖ + 1) * ‖H - G‖ < ε := by
      calc
        _ < (‖F‖ + 1) * δ := mul_lt_mul_of_pos_left hHG hden
        _ = ε := by dsimp [δ]; field_simp
    exact hre.trans_lt (hcs.trans_lt (hmul_le.trans_lt hmul_lt))
  have hHlower : r - ε < (@inner ℂ E _ F H).re := by
    rw [abs_lt] at hinner_error
    linarith
  have hblock := re_inner_iterate_birkhoffAverage_eq_block V F i N
  change r - ε < (@inner ℂ E _ F ((V.toContinuousLinearMap^[i])
    (birkhoffAverage ℂ V.toContinuousLinearMap id N F))).re at hHlower
  rw [hblock] at hHlower
  exact (not_lt_of_ge hsum) hHlower

lemma inner_indicator_iterate_re_eq_correlation (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    let f := CorrelationMean.indicatorComplex A
    let hf := CorrelationMean.indicatorComplex_memLp M hM A hA 2
    let V : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
      MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
    (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hf.toLp f)
      ((V.toContinuousLinearMap^[n]) (hf.toLp f))).re =
        correlation M A A n := by
  dsimp only
  let f := CorrelationMean.indicatorComplex A
  let hf := CorrelationMean.indicatorComplex_memLp M hM A hA 2
  let V : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  have hiter := MeanErgodicL2.koopmanLp_iterate_toLp M hM f hf n
  have hcomplex :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hf.toLp f)
          ((V.toContinuousLinearMap^[n]) (hf.toLp f)) =
        functionCorrelation M f f n := by
    rw [hiter]
    rw [MeasureTheory.L2.inner_def]
    unfold functionCorrelation
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hf.coeFn_toLp,
      (hf.comp_measurePreserving (hM.2.iterate n)).coeFn_toLp] with x hx hxn
    rw [RCLike.inner_apply, hx, hxn]
    rfl
  rw [hcomplex]
  exact (CorrelationMean.correlation_eq_re_functionCorrelation_indicator
    M hM A A hA hA n).symm

lemma sq_le_re_inner_orthogonalProjection
    (S : Submodule ℂ E) [S.HasOrthogonalProjection] (F One : E) (r : ℝ)
    (hOneS : One ∈ S) (hOneNorm : ‖One‖ = 1)
    (hr0 : 0 ≤ r) (hOneF : @inner ℂ E _ One F = (r : ℂ)) :
    r ^ 2 ≤ (@inner ℂ E _ F (S.orthogonalProjection F)).re := by
  let G : E := S.orthogonalProjection F
  have hGS : G ∈ S := by
    exact S.starProjection_apply_mem F
  have horth : F - G ∈ Sᗮ := by
    exact S.sub_starProjection_mem_orthogonal F
  have hFG : @inner ℂ E _ F G = @inner ℂ E _ G G := by
    have hz : @inner ℂ E _ (F - G) G = 0 :=
      S.inner_left_of_mem_orthogonal hGS horth
    calc
      @inner ℂ E _ F G = @inner ℂ E _ ((F - G) + G) G := by
        congr 1
        abel
      _ = @inner ℂ E _ (F - G) G + @inner ℂ E _ G G := inner_add_left _ _ _
      _ = _ := by rw [hz, zero_add]
  have hOneG : @inner ℂ E _ One G = (r : ℂ) := by
    have hz : @inner ℂ E _ One (F - G) = 0 :=
      S.inner_right_of_mem_orthogonal hOneS horth
    have hsplit : @inner ℂ E _ One F =
        @inner ℂ E _ One (F - G) + @inner ℂ E _ One G := by
      calc
        _ = @inner ℂ E _ One ((F - G) + G) := by
          congr 1
          abel
        _ = _ := inner_add_right _ _ _
    rw [hOneF, hz, zero_add] at hsplit
    exact hsplit.symm
  have hrG : r ≤ ‖G‖ := by
    have hcs : ‖@inner ℂ E _ One G‖ ≤ ‖One‖ * ‖G‖ :=
      norm_inner_le_norm One G
    rw [hOneG, Complex.norm_real, Real.norm_of_nonneg hr0,
      hOneNorm, one_mul] at hcs
    exact hcs
  rw [hFG]
  have hnormsq := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) G
  change ‖G‖ ^ 2 = (@inner ℂ E _ G G).re at hnormsq
  nlinarith [sq_nonneg (‖G‖ - r)]

theorem khintchineRecurrence (M : System.{u}) :
    KhintchineRecurrenceStatement M := by
  intro hM A hA hApos ε hε
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1
  let f := CorrelationMean.indicatorComplex A
  let hf := CorrelationMean.indicatorComplex_memLp M hM A hA 2
  let V : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
  let U : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ :=
    V.toContinuousLinearMap
  let S : Submodule ℂ (MeasureTheory.Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus U (1 : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ]
      MeasureTheory.Lp ℂ 2 M.μ)
  let F : MeasureTheory.Lp ℂ 2 M.μ := hf.toLp f
  let G : MeasureTheory.Lp ℂ 2 M.μ := S.orthogonalProjection F
  have hUnorm : ‖U‖ ≤ 1 := by
    apply U.opNorm_le_bound (by norm_num)
    intro H
    dsimp [U]
    rw [one_mul, V.norm_map]
  have havg : Tendsto (fun N => birkhoffAverage ℂ U id N F)
      atTop (nhds G) := by
    exact U.tendsto_birkhoffAverage_orthogonalProjection hUnorm F
  have hGS : G ∈ S := by
    exact S.starProjection_apply_mem F
  have hGfix : V G = G := by
    have hfix : U G = G := hGS
    exact hfix
  let one : M.X → ℂ := fun _ => 1
  let hone : MeasureTheory.MemLp one 2 M.μ :=
    MeasureTheory.memLp_const (μ := M.μ) (p := 2) 1
  let One : MeasureTheory.Lp ℂ 2 M.μ := hone.toLp one
  have hOneS : One ∈ S := by
    have hSK := MeanErgodicL2.fixedSpace_eq_invariantLpMeas M hM
    change One ∈ LinearMap.eqLocus U
      (1 : MeasureTheory.Lp ℂ 2 M.μ →L[ℂ] MeasureTheory.Lp ℂ 2 M.μ)
    rw [hSK, MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
    let mInv : MeasurableSpace M.X :=
      MeasurableSpace.generateFrom (invariantSigmaAlgebra M)
    have honeMeas : AEStronglyMeasurable[mInv] one M.μ :=
      measurable_const.aestronglyMeasurable
    exact honeMeas.congr hone.coeFn_toLp.symm
  have hOneInner : @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ One One = 1 := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ x, @inner ℂ ℂ _ (One x) (One x) ∂M.μ) = ∫ _x, (1 : ℂ) ∂M.μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hone.coeFn_toLp] with x hx
        rw [RCLike.inner_apply, hx]
        simp [one]
      _ = 1 := by simp
  have hOneNorm : ‖One‖ = 1 := by
    have hs := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) One
    rw [hOneInner] at hs
    change ‖One‖ ^ 2 = 1 at hs
    nlinarith [norm_nonneg One]
  have hOneF : @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ One F =
      (realMeasure M A : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ x, @inner ℂ ℂ _ (One x) (F x) ∂M.μ) =
          ∫ x, f x ∂M.μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hone.coeFn_toLp, hf.coeFn_toLp] with x hxOne hxF
        rw [RCLike.inner_apply, hxOne, hxF]
        simp [one, f]
      _ = (realMeasure M A : ℂ) :=
        CorrelationMean.integral_indicatorComplex M A hA
  have hr0 : 0 ≤ realMeasure M A := MeasureTheory.measureReal_nonneg
  have hlower : (realMeasure M A) ^ 2 ≤
      (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F G).re := by
    exact sq_le_re_inner_orthogonalProjection S F One (realMeasure M A)
      hOneS hOneNorm hr0 hOneF
  have hsyn := inner_recurrence_isSyndetic V F G
    ((realMeasure M A) ^ 2) hGfix havg hlower hε
  rcases hsyn with ⟨N, hN, hall⟩
  refine ⟨N, hN, ?_⟩
  intro i
  rcases hall i with ⟨a, ha, hia, hai⟩
  refine ⟨a, ?_, hia, hai⟩
  have hid := inner_indicator_iterate_re_eq_correlation M hM A hA a
  change (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F
    ((V.toContinuousLinearMap^[a]) F)).re = correlation M A A a at hid
  simp only [Set.mem_setOf_eq] at ha ⊢
  rw [hid] at ha
  simpa only [correlation, pow_two] using ha

end Khintchine
end Chapter02
