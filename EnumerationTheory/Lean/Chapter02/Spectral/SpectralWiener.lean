import Chapter02.Spectral.SpectralRelations
import Chapter02.Spectral.SpectralPointMass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.SpectralWiener

def geometricAverage (r : ℂ) (N : ℕ) : ℂ :=
  if N = 0 then 0 else (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, r ^ n

lemma norm_geometricAverage_le (r : ℂ) (hr : ‖r‖ = 1) (N : ℕ) :
    ‖geometricAverage r N‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [geometricAverage, hN]
  · rw [geometricAverage, if_neg hN, norm_mul, norm_inv, norm_natCast]
    calc
      (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, r ^ n‖ ≤
          (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖r ^ n‖ := by
        gcongr
        exact norm_sum_le _ _
      _ = 1 := by
        simp [norm_pow, hr, hN]

lemma tendsto_geometricAverage (r : ℂ) (hr : ‖r‖ = 1) :
    Tendsto (geometricAverage r) atTop (nhds (if r = 1 then 1 else 0)) := by
  by_cases hr1 : r = 1
  · subst r
    apply (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp [geometricAverage, Nat.ne_of_gt hN]
  · simp only [if_neg hr1]
    have hgeom (N : ℕ) :
        (∑ n ∈ Finset.range N, r ^ n) * (r - 1) = r ^ N - 1 := by
      simpa [sub_eq_add_neg, mul_comm] using geom_sum_mul r N
    have hbound : ∀ N : ℕ, ‖geometricAverage r N‖ ≤
        2 * (‖r - 1‖⁻¹ * (N : ℝ)⁻¹) := by
      intro N
      by_cases hN : N = 0
      · simp [geometricAverage, hN]
      · have hrsub : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
        have hformula : geometricAverage r N =
            (r ^ N - 1) / ((N : ℂ) * (r - 1)) := by
          rw [geometricAverage, if_neg hN]
          field_simp
          simpa [mul_comm] using hgeom N
        rw [hformula, norm_div, norm_mul, norm_natCast]
        have hp : ‖r ^ N - 1‖ ≤ 2 := by
          calc
            ‖r ^ N - 1‖ ≤ ‖r ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by simp [norm_pow, hr]; norm_num
        calc
          ‖r ^ N - 1‖ / ((N : ℝ) * ‖r - 1‖) ≤
              2 / ((N : ℝ) * ‖r - 1‖) := by
                exact div_le_div_of_nonneg_right hp (by positivity)
          _ = 2 * (‖r - 1‖⁻¹ * (N : ℝ)⁻¹) := by
            field_simp
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) := by
      simpa [one_div] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hb : Tendsto (fun N : ℕ =>
        2 * (‖r - 1‖⁻¹ * (N : ℝ)⁻¹)) atTop (nhds 0) := by
      convert tendsto_const_nhds.mul (tendsto_const_nhds.mul hinv) using 1
      simp
    simpa using squeeze_zero (fun N => norm_nonneg (geometricAverage r N - 0))
      (fun N => by simpa using hbound N)
      hb

def circleRatio (p : Circle × Circle) : ℂ :=
  (p.1 : ℂ) * star (p.2 : ℂ)

lemma norm_circleRatio (p : Circle × Circle) : ‖circleRatio p‖ = 1 := by
  simp [circleRatio]

lemma circleRatio_eq_one_iff (p : Circle × Circle) :
    circleRatio p = 1 ↔ p.1 = p.2 := by
  rw [circleRatio]
  have hb : (starRingEnd ℂ) (p.2 : ℂ) * (p.2 : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
  constructor
  · intro h
    change (p.1 : ℂ) * (starRingEnd ℂ) (p.2 : ℂ) = 1 at h
    apply Subtype.ext
    calc
      (p.1 : ℂ) = (p.1 : ℂ) * 1 := by ring
      _ = (p.1 : ℂ) * ((starRingEnd ℂ) (p.2 : ℂ) * (p.2 : ℂ)) := by rw [hb]
      _ = ((p.1 : ℂ) * (starRingEnd ℂ) (p.2 : ℂ)) * (p.2 : ℂ) := by ring
      _ = (p.2 : ℂ) := by rw [h]; ring
  · intro h
    rw [h]
    rw [mul_comm]
    exact hb

def circleKernel (N : ℕ) (p : Circle × Circle) : ℂ :=
  geometricAverage (circleRatio p) N

lemma circleKernel_measurable (N : ℕ) : Measurable (circleKernel N) := by
  by_cases hN : N = 0
  · subst N
    change Measurable (fun _ : Circle × Circle => 0)
    fun_prop
  · rw [show circleKernel N = fun p : Circle × Circle =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, circleRatio p ^ n by
      funext p
      simp [circleKernel, geometricAverage, hN]]
    unfold circleRatio
    fun_prop

lemma norm_circleKernel_le (N : ℕ) (p : Circle × Circle) :
    ‖circleKernel N p‖ ≤ 1 :=
  norm_geometricAverage_le _ (norm_circleRatio p) N

lemma tendsto_circleKernel (p : Circle × Circle) :
    Tendsto (fun N => circleKernel N p) atTop
      (nhds (if p.1 = p.2 then 1 else 0)) := by
  simpa [circleKernel, circleRatio_eq_one_iff] using
    tendsto_geometricAverage (circleRatio p) (norm_circleRatio p)

lemma tendsto_integral_circleKernel (μ : CircleMeasureData) :
    Tendsto (fun N => ∫ p, circleKernel N p ∂μ.μ.prod μ.μ) atTop
      (nhds (∫ p, (if p.1 = p.2 then (1 : ℂ) else 0) ∂μ.μ.prod μ.μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro N
    exact (circleKernel_measurable N).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    filter_upwards [] with p
    simpa using norm_circleKernel_le N p
  · filter_upwards [] with p
    exact tendsto_circleKernel p

lemma integral_circleRatio_pow (μ : CircleMeasureData) (n : ℕ) :
    (∫ p, circleRatio p ^ n ∂μ.μ.prod μ.μ) =
      circleFourierCoefficient μ n * star (circleFourierCoefficient μ n) := by
  rw [show (fun p : Circle × Circle => circleRatio p ^ n) =
      fun p => (p.1 : ℂ) ^ n * star (p.2 : ℂ) ^ n by
    funext p
    unfold circleRatio
    rw [mul_pow]]
  rw [integral_prod_mul (fun z : Circle => (z : ℂ) ^ n)
    (fun z : Circle => star (z : ℂ) ^ n)]
  change (∫ x : Circle, (x : ℂ) ^ n ∂μ.μ) *
      (∫ y : Circle, star (y : ℂ) ^ n ∂μ.μ) = _
  simp_rw [← star_pow]
  rw [Complex.star_def, integral_conj]
  simp only [circleFourierCoefficient, zpow_natCast]

lemma integral_circleKernel_eq (μ : CircleMeasureData) (N : ℕ) :
    (∫ p, circleKernel N p ∂μ.μ.prod μ.μ) =
      if N = 0 then 0 else
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
          (‖circleFourierCoefficient μ n‖ ^ 2 : ℂ) := by
  by_cases hN : N = 0
  · subst N
    simp [circleKernel, geometricAverage]
  · rw [if_neg hN]
    rw [show circleKernel N = fun p =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, circleRatio p ^ n by
      funext p
      simp [circleKernel, geometricAverage, hN]]
    rw [integral_const_mul]
    rw [integral_finset_sum]
    · apply congrArg
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_circleRatio_pow]
      change circleFourierCoefficient μ n *
        (starRingEnd ℂ) (circleFourierCoefficient μ n) = _
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      norm_cast
    · intro n hn
      exact Continuous.integrable_of_hasCompactSupport (by
        unfold circleRatio
        fun_prop)
        (HasCompactSupport.of_compactSpace _)

lemma integral_diagonal_indicator (μ : CircleMeasureData) :
    (∫ p : Circle × Circle, (if p.1 = p.2 then (1 : ℂ) else 0)
        ∂μ.μ.prod μ.μ) = ((μ.μ.prod μ.μ).real (Set.diagonal Circle) : ℂ) := by
  rw [show (fun p : Circle × Circle => if p.1 = p.2 then (1 : ℂ) else 0) =
      (Set.diagonal Circle).indicator (fun _ => (1 : ℂ)) by
    funext p
    by_cases hp : p.1 = p.2 <;> simp [Set.indicator, hp, Set.mem_diagonal_iff]]
  rw [integral_indicator measurableSet_diagonal]
  simp

lemma circle_wiener_limit (μ : CircleMeasureData) :
    Tendsto (fun N : ℕ => if N = 0 then 0 else
      ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
        ‖circleFourierCoefficient μ n‖ ^ 2) atTop
      (nhds ((μ.μ.prod μ.μ).real (Set.diagonal Circle))) := by
  have h := tendsto_integral_circleKernel μ
  rw [integral_diagonal_indicator] at h
  have hrewrite : (fun N => ∫ p, circleKernel N p ∂μ.μ.prod μ.μ) =
      fun N : ℕ => ((if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          ‖circleFourierCoefficient μ n‖ ^ 2 : ℝ) : ℂ) := by
    funext N
    rw [integral_circleKernel_eq]
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false]
      push_cast
      rfl
  rw [hrewrite] at h
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa using hre

lemma diagonal_measure_zero_iff_continuous (μ : CircleMeasureData) :
    (μ.μ.prod μ.μ).real (Set.diagonal Circle) = 0 ↔
      IsContinuousCircleMeasure μ := by
  constructor
  · intro hdiag z
    have hdiag' : (μ.μ.prod μ.μ) (Set.diagonal Circle) = 0 :=
      (measureReal_eq_zero_iff).mp hdiag
    have hrect : (μ.μ.prod μ.μ) ({z} ×ˢ {z}) = 0 :=
      measure_mono_null (by
        intro p hp
        rcases hp with ⟨hp1, hp2⟩
        rw [Set.mem_singleton_iff] at hp1 hp2
        rw [Set.mem_diagonal_iff]
        exact hp1.trans hp2.symm) hdiag'
    rw [Measure.prod_prod] at hrect
    simpa using hrect
  · intro hcont
    rw [measureReal_eq_zero_iff]
    rw [Measure.prod_apply measurableSet_diagonal]
    calc
      (∫⁻ z, μ.μ (Prod.mk z ⁻¹' Set.diagonal Circle) ∂μ.μ) =
          ∫⁻ _z : Circle, 0 ∂μ.μ := by
        apply lintegral_congr
        intro z
        rw [show Prod.mk z ⁻¹' Set.diagonal Circle = {z} by
          ext w
          simp [Set.mem_diagonal_iff, eq_comm]]
        exact hcont z
      _ = 0 := lintegral_zero

lemma circle_wiener_zero_iff_continuous (μ : CircleMeasureData) :
    Tendsto (fun N : ℕ => if N = 0 then 0 else
      ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
        ‖circleFourierCoefficient μ n‖ ^ 2) atTop (nhds 0) ↔
      IsContinuousCircleMeasure μ := by
  constructor
  · intro h
    have hz : (μ.μ.prod μ.μ).real (Set.diagonal Circle) = 0 :=
      tendsto_nhds_unique (circle_wiener_limit μ) h
    exact (diagonal_measure_zero_iff_continuous μ).mp hz
  · intro h
    have hz := (diagonal_measure_zero_iff_continuous μ).mpr h
    simpa [hz] using circle_wiener_limit μ

lemma eigenvalue_norm_one (D : HilbertOperatorData) (hD : IsUnitary D)
    (y : D.H) (hy0 : y ≠ 0) (lam : ℂ) (hy : D.U y = lam • y) :
    ‖lam‖ = 1 := by
  have hn := hD.2 y
  rw [hy, norm_smul] at hn
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
  apply mul_right_cancel₀ hny
  simpa using hn

lemma continuous_measure_implies_continuous_subspace
    (D : HilbertOperatorData) (hD : IsUnitary D) (x : D.H)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ)
    (hcont : IsContinuousCircleMeasure μ) :
    InContinuousSpectralSubspace D x := by
  intro y hy
  obtain ⟨hy0, lam, hlam⟩ := hy
  let z : Circle := ⟨lam, by
    exact mem_sphere_zero_iff_norm.mpr
      (eigenvalue_norm_one D hD y hy0 lam hlam)⟩
  obtain ⟨ν, hν, _⟩ := SpectralMeasure.spectralMeasure D hD y
  have hνeq : ν.μ = ENNReal.ofReal (‖y‖ ^ 2) • Measure.dirac z :=
    SpectralPointMass.eigenvector_spectral_measure_point_mass D hD y z hy0 hlam ν hν
  have hsingDirac : Measure.MutuallySingular μ.μ (Measure.dirac z) := by
    refine ⟨{z}, measurableSet_singleton z, hcont z, ?_⟩
    simp
  have hsing : Measure.MutuallySingular μ.μ ν.μ := by
    rw [hνeq]
    exact (hsingDirac.symm.smul (ENNReal.ofReal (‖y‖ ^ 2))).symm
  have horth := SpectralRelations.singular_spectral_measures_orthogonal
    D hD x y μ ν hμ hν hsing
  exact horth x y (SpectralRelations.self_mem_cyclic D x)
    (SpectralRelations.self_mem_cyclic D y)

lemma eigen_hyperplane_reducing (D : HilbertOperatorData) (hD : IsUnitary D)
    (y : D.H) (lam : ℂ) (hlam0 : lam ≠ 0) (hy : D.U y = lam • y) :
    IsClosedReducingSubspace D {a | @inner ℂ D.H _ a y = 0} := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro a ha b hb c d
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [inner_add_left, inner_smul_left, inner_smul_left, ha, hb]
    simp
  · intro seq hseq a hlim
    simp only [Set.mem_setOf_eq] at hseq ⊢
    have ht : Tendsto (fun n => @inner ℂ D.H _ (seq n) y) atTop
        (nhds (@inner ℂ D.H _ a y)) :=
      hlim.inner (𝕜 := ℂ)
        (show Tendsto (fun _n : ℕ => y) atTop (nhds y) from tendsto_const_nhds)
    have hz : Tendsto (fun n => @inner ℂ D.H _ (seq n) y) atTop (nhds 0) := by
      simp [hseq]
    exact tendsto_nhds_unique ht hz
  · intro a
    simp only [Set.mem_setOf_eq]
    have hi := (SpectralMeasure.unitaryEquiv D hD).inner_map_map a y
    change @inner ℂ D.H _ (D.U a) (D.U y) = @inner ℂ D.H _ a y at hi
    rw [hy, inner_smul_right] at hi
    constructor
    · intro ha
      apply (mul_eq_zero.mp ?_).resolve_left hlam0
      rw [hi, ha]
    · intro ha
      rw [← hi, ha, mul_zero]

lemma cyclic_eigenvector_inner_ne_zero (D : HilbertOperatorData) (hD : IsUnitary D)
    (x y : D.H) (hycyc : InCyclicSubspace D x y)
    (hy0 : y ≠ 0) (lam : ℂ) (hy : D.U y = lam • y) :
    @inner ℂ D.H _ x y ≠ 0 := by
  have hlam : ‖lam‖ = 1 := eigenvalue_norm_one D hD y hy0 lam hy
  have hlam0 : lam ≠ 0 := by
    intro h
    simp [h] at hlam
  intro hxy
  have hyy := hycyc {a | @inner ℂ D.H _ a y = 0}
    (eigen_hyperplane_reducing D hD y lam hlam0 hy) hxy
  exact hy0 (inner_self_eq_zero.mp hyy)

lemma continuous_subspace_implies_continuous_measure
    (D : HilbertOperatorData) (hD : IsUnitary D) (x : D.H)
    (μ : CircleMeasureData) (hμ : HasSpectralMeasure D x μ)
    (hxcont : InContinuousSpectralSubspace D x) :
    IsContinuousCircleMeasure μ := by
  intro z
  by_contra hμz
  have hμzpos : 0 < μ.μ {z} := (pos_iff_ne_zero).mpr hμz
  obtain ⟨μ₀, hμ₀, _⟩ := Herglotz.herglotz
    (SpectralMeasure.vectorCorrelation D hD x)
    (SpectralMeasure.vectorCorrelation_positiveDefinite D hD x)
  have hμ₀spec : HasSpectralMeasure D x μ₀ := by
    intro n
    rw [hμ₀ (n : ℤ)]
    exact congrArg (fun v : D.H => @inner ℂ D.H _ x v)
      (SpectralMeasure.unitaryEquiv_zpow_nat D hD x n)
  have hμeq : μ₀ = μ := SpectralMeasure.eq_of_nat_moments μ₀ μ
    (fun n => (hμ₀spec n).trans (hμ n).symm)
  subst μ₀
  let f : Circle → ℂ := fun w => if w = z then 1 else 0
  have hf : MemLp f 2 μ.μ := by
    convert (memLp_indicator_const (μ := μ.μ) 2 (measurableSet_singleton z) (1 : ℂ)
      (Or.inr (measure_ne_top μ.μ {z}))) using 1
  let F : Lp ℂ 2 μ.μ := hf.toLp f
  let y : D.H := CyclicSpectralModel.cyclicCLM D hD x μ F
  have hycyc : InCyclicSubspace D x y :=
    (CyclicSpectralModel.inCyclicSubspace_iff_range D hD x y μ hμ₀).2 ⟨F, rfl⟩
  have hF0 : F ≠ 0 := by
    intro hzero
    have hcoe := hf.coeFn_toLp
    change hf.toLp f = 0 at hzero
    rw [hzero] at hcoe
    have hae : ∀ᵐ w ∂μ.μ, w ∉ ({z} : Set Circle) := by
      filter_upwards [hcoe, Lp.coeFn_zero ℂ 2 μ.μ] with w hw hw0
      intro hwz
      have hw_eq : w = z := by simpa using hwz
      rw [hw0] at hw
      simp [f, hw_eq] at hw
    have : μ.μ {z} = 0 := measure_eq_zero_iff_ae_notMem.mpr hae
    exact hμz this
  have hy0 : y ≠ 0 := by
    intro hyzero
    have heq : CyclicSpectralModel.cyclicIsometry D hD x μ hμ₀ F =
        CyclicSpectralModel.cyclicIsometry D hD x μ hμ₀ 0 := by
      change CyclicSpectralModel.cyclicCLM D hD x μ F =
        CyclicSpectralModel.cyclicCLM D hD x μ 0
      simpa [y] using hyzero
    exact hF0 ((CyclicSpectralModel.cyclicIsometry D hD x μ hμ₀).injective heq)
  have hcoord : CyclicSpectralModel.coordinateLinear μ F = (z : ℂ) • F := by
    change CyclicSpectralModel.coordinateLinear μ (hf.toLp f) =
      (z : ℂ) • hf.toLp f
    apply Lp.ext
    filter_upwards [CyclicSpectralModel.coordinateLp_coe μ (hf.toLp f),
      hf.coeFn_toLp, Lp.coeFn_smul (z : ℂ) (hf.toLp f)] with w hcoord hF hsmul
    change CyclicSpectralModel.coordinateLp μ (hf.toLp f) w =
      ((z : ℂ) • hf.toLp f) w
    rw [hcoord, hsmul, hF]
    by_cases hw : w = z
    · subst w
      simp [f, hF, smul_eq_mul]
    · simp [f, hw, hF, smul_eq_mul]
  have hyeig : D.U y = (z : ℂ) • y := by
    change D.U (CyclicSpectralModel.cyclicCLM D hD x μ F) =
      (z : ℂ) • CyclicSpectralModel.cyclicCLM D hD x μ F
    rw [← CyclicSpectralModel.cyclicCLM_intertwines D hD x μ hμ₀, hcoord]
    exact map_smul _ _ _
  exact (cyclic_eigenvector_inner_ne_zero D hD x y hycyc hy0 (z : ℂ) hyeig)
    (hxcont y ⟨hy0, z, hyeig⟩)

theorem wienerTheorem (D : HilbertOperatorData) : WienerTheoremStatement D := by
  intro hD x
  obtain ⟨μ, hμ, _⟩ := SpectralMeasure.spectralMeasure D hD x
  have hcont : InContinuousSpectralSubspace D x ↔ IsContinuousCircleMeasure μ :=
    ⟨continuous_subspace_implies_continuous_measure D hD x μ hμ,
      continuous_measure_implies_continuous_subspace D hD x μ hμ⟩
  have havg : (fun N : ℕ => if N = 0 then 0 else
      ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
        ‖@inner ℂ D.H _ ((D.U^[n]) x) x‖ ^ 2) =
      fun N : ℕ => if N = 0 then 0 else
      ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
        ‖circleFourierCoefficient μ n‖ ^ 2 := by
    funext N
    by_cases hN : N = 0
    · simp [hN]
    simp only [hN, if_false]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [hμ n]
    rw [norm_inner_symm]
  rw [hcont, havg]
  exact (circle_wiener_zero_iff_continuous μ).symm

end Chapter02.SpectralWiener
