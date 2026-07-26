import Chapter02.Spectral.WeakSpectrum
import Chapter02.Spectral.EigenfunctionLemmas
import Chapter02.Spectral.SpectralWiener

noncomputable section

open Classical Filter MeasureTheory Topology
open scoped BigOperators ENNReal ComplexConjugate

namespace Chapter02.SpectralMixing

def fourierCesaroKernel (N : ℕ) (z : Circle) : ℂ :=
  if N = 0 then 0 else (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (z : ℂ) ^ n

lemma fourierCesaroKernel_norm_le_one (N : ℕ) (z : Circle) :
    ‖fourierCesaroKernel N z‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [fourierCesaroKernel, hN]
  rw [fourierCesaroKernel, if_neg hN, norm_mul]
  calc
    ‖(N : ℂ)⁻¹‖ * ‖∑ n ∈ Finset.range N, (z : ℂ) ^ n‖
        ≤ ‖(N : ℂ)⁻¹‖ * ∑ n ∈ Finset.range N, ‖(z : ℂ) ^ n‖ := by
          gcongr
          exact norm_sum_le _ _
    _ = 1 := by
      simp [hN]

lemma fourierCesaroKernel_tendsto (z : Circle) :
    Tendsto (fun N => fourierCesaroKernel N z) atTop
      (nhds (if z = 1 then 1 else 0)) := by
  by_cases hz : z = 1
  · subst z
    rw [if_pos rfl]
    have hevent : ∀ᶠ N : ℕ in atTop, fourierCesaroKernel N 1 = 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      simp [fourierCesaroKernel, Nat.ne_of_gt hN]
    exact tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  · simp only [hz, if_false]
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hden : ‖(z : ℂ) - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr (by
      exact fun h => hz (Circle.ext h)))
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 / ‖(z : ℂ) - 1‖ / ε < N := by
      exact exists_nat_gt (2 / ‖(z : ℂ) - 1‖ / ε)
    refine ⟨max 1 N, ?_⟩
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hnN : N ≤ n := le_trans (le_max_right _ _) hn
    have hsum : (∑ k ∈ Finset.range n, (z : ℂ) ^ k) * ((z : ℂ) - 1) =
        (z : ℂ) ^ n - 1 := by
      calc
        _ = -((∑ k ∈ Finset.range n, (z : ℂ) ^ k) * (1 - (z : ℂ))) := by ring
        _ = -(1 - (z : ℂ) ^ n) := by rw [geom_sum_mul_neg]
        _ = _ := by ring
    have hsum_bound : ‖∑ k ∈ Finset.range n, (z : ℂ) ^ k‖ ≤
        2 / ‖(z : ℂ) - 1‖ := by
      have hprod : ‖∑ k ∈ Finset.range n, (z : ℂ) ^ k‖ * ‖(z : ℂ) - 1‖ ≤ 2 := by
        rw [← norm_mul, hsum]
        calc
          ‖(z : ℂ) ^ n - 1‖ ≤ ‖(z : ℂ) ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by
            rw [norm_pow, Circle.norm_coe, one_pow, norm_one]
            norm_num only
      exact (le_div_iff₀ hden).mpr hprod
    rw [dist_zero_right, fourierCesaroKernel, if_neg hn0, norm_mul]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    rw [norm_inv, Complex.norm_natCast]
    calc
      (n : ℝ)⁻¹ * ‖∑ k ∈ Finset.range n, (z : ℂ) ^ k‖
          ≤ (n : ℝ)⁻¹ * (2 / ‖(z : ℂ) - 1‖) := by
            gcongr
      _ < ε := by
        rw [inv_mul_eq_div]
        have hlt : 2 / ‖(z : ℂ) - 1‖ / ε < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
        have hpos : 0 < 2 / ‖(z : ℂ) - 1‖ := div_pos (by norm_num) hden
        exact (div_lt_iff₀ hnpos).2 (by
          simpa [mul_comm] using (div_lt_iff₀ hε).1 hlt)

lemma integral_fourierCesaroKernel (μ : CircleMeasureData) (N : ℕ) :
    (∫ z, fourierCesaroKernel N z ∂μ.μ) =
      if N = 0 then 0 else
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, circleFourierCoefficient μ n := by
  by_cases hN : N = 0
  · simp [fourierCesaroKernel, hN]
  simp only [fourierCesaroKernel, hN, if_false]
  rw [MeasureTheory.integral_const_mul]
  have hint : ∀ n ∈ Finset.range N,
      Integrable (fun z : Circle => (z : ℂ) ^ n) μ.μ := by
    intro n hn
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop : Continuous (fun z : Circle => (z : ℂ) ^ n))
      (HasCompactSupport.of_compactSpace _)
  apply congrArg (fun w : ℂ => (N : ℂ)⁻¹ * w)
  rw [integral_finset_sum (Finset.range N) hint]
  rfl

lemma circle_fourier_cesaro_tendsto_mass_one (μ : CircleMeasureData) :
    Tendsto (fun N : ℕ => if N = 0 then 0 else
      (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, circleFourierCoefficient μ n)
      atTop (nhds ((μ.μ.real ({1} : Set Circle) : ℂ))) := by
  letI : MeasureTheory.IsFiniteMeasure μ.μ := μ.isFinite
  have hdc := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := μ.μ) (F := fun N z => fourierCesaroKernel N z)
    (f := fun z : Circle => if z = 1 then (1 : ℂ) else 0)
    (fun _ : Circle => (1 : ℝ))
    (fun N => (by
      apply Continuous.aestronglyMeasurable
      by_cases hN : N = 0
      · simp only [fourierCesaroKernel, hN, if_pos]
        exact continuous_const
      · simp only [fourierCesaroKernel, hN, if_false]
        fun_prop))
    (MeasureTheory.integrable_const 1)
    (fun N => Filter.Eventually.of_forall (fourierCesaroKernel_norm_le_one N))
    (Filter.Eventually.of_forall fourierCesaroKernel_tendsto)
  have hlimit :
      (∫ z : Circle, (if z = 1 then (1 : ℂ) else 0) ∂μ.μ) =
        (μ.μ.real ({1} : Set Circle) : ℂ) := by
    rw [show (fun z : Circle => if z = 1 then (1 : ℂ) else 0) =
        ({1} : Set Circle).indicator (fun _ => (1 : ℂ)) by
      funext z
      simp [Set.indicator]]
    rw [MeasureTheory.integral_indicator (measurableSet_singleton (1 : Circle))]
    simp [MeasureTheory.Measure.real]
  rw [hlimit] at hdc
  convert hdc using 1
  funext N
  exact (integral_fourierCesaroKernel μ N).symm

lemma ergodic_iff_spectral_condition (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsErgodic M ↔
      HasSimpleTrivialEigenvalue M ∧
      ∀ f : M.X → ℂ, IsZeroMeanFunction M f →
        ∀ μ : CircleMeasureData, HasFunctionSpectralMeasure M f μ → μ.μ {1} = 0 := by
  constructor
  · intro hErg
    refine ⟨?_, ?_⟩
    · refine ⟨(Section05.eigenvalues_group_property M hErg).1, ?_⟩
      intro f hf
      exact (Section01.ergodicityInvariantFunctionCharacterizations M hM).mp hErg
        f hf.1 (by simpa using hf.2.2)
    · intro f hf μ hμ
      have hcorr := CorrelationMean.ergodic_cesaroFunctionCorrelations
        M hM hErg f f hf.1 hf.1
      have hmean : productOfMeans M f f = 0 := by
        simp [productOfMeans, hf.2]
      rw [hmean] at hcorr
      have hfourier : Tendsto (fun N : ℕ => if N = 0 then 0 else
          (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, circleFourierCoefficient μ n)
          atTop (nhds 0) := by
        convert hcorr using 1
        funext N
        by_cases hN : N = 0
        · simp [hN]
        simp only [if_neg hN]
        apply congrArg (fun s : ℂ ↦ (N : ℂ)⁻¹ * s)
        apply Finset.sum_congr rfl
        intro n hn
        exact hμ n
      have hreal : μ.μ.real ({1} : Set Circle) = 0 := by
        have heq : (μ.μ.real ({1} : Set Circle) : ℂ) = 0 :=
          tendsto_nhds_unique (circle_fourier_cesaro_tendsto_mass_one μ) hfourier
        exact_mod_cast heq
      exact (measureReal_eq_zero_iff).mp hreal
  · rintro ⟨hsimple, _hatom⟩
    exact (Section01.ergodicityInvariantFunctionCharacterizations M hM).mpr
      (fun f hf hinv => by
        by_cases hz : f =ᵐ[M.μ] 0
        · exact ⟨0, hz⟩
        · exact hsimple.2 f ⟨hf, hz, by simpa using hinv⟩)

lemma weakMixing_implies_zeroMean_spectral (M : System.{u})
    (hweak : IsWeakMixing M) :
    ∀ f : M.X → ℂ, IsZeroMeanFunction M f →
      (∀ μ : CircleMeasureData, HasFunctionSpectralMeasure M f μ →
        IsContinuousCircleMeasure μ) ∧
      Tendsto (spectralAbsoluteCesaro M f) atTop (nhds 0) := by
  intro f hf
  have habsCes : cesaroTendsTo (fun n => ‖functionCorrelation M f f n‖) 0 := by
    have h := CorrelationMean.weakMixing_functionCorrelations
      M hweak f f hf.1 hf.1
    simpa [productOfMeans, hf.2] using h
  have habs : Tendsto (spectralAbsoluteCesaro M f) atTop (nhds 0) := by
    apply (Filter.tendsto_add_atTop_iff_nat (f := spectralAbsoluteCesaro M f) 1).mp
    unfold cesaroTendsTo seqTendsTo cesaroAverage at habsCes
    convert habsCes using 1
  refine ⟨?_, habs⟩
  intro μ hμ
  have hnormCes : cesaroTendsTo
      (fun n => ‖circleFourierCoefficient μ n‖) 0 := by
    convert habsCes using 1
    funext n
    rw [hμ n]
  have hbounded : BddAbove
      (Set.range fun n : ℕ => ‖circleFourierCoefficient μ n‖) := by
    refine ⟨μ.μ.real Set.univ, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa [circleFourierCoefficient] using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := μ.μ) (f := fun z : Circle => (z : ℂ) ^ (n : ℤ))
        (C := 1) (by filter_upwards with z; simp))
  have hsquareCes := ZeroDensity.cesaro_norm_sq_of_cesaro_norm
    (fun n => circleFourierCoefficient μ n) hbounded hnormCes
  have hsquare : Tendsto (fun N : ℕ => if N = 0 then 0 else
      ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
        ‖circleFourierCoefficient μ n‖ ^ 2) atTop (nhds 0) := by
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    unfold cesaroTendsTo seqTendsTo cesaroAverage at hsquareCes
    convert hsquareCes using 1
  exact (SpectralWiener.circle_wiener_zero_iff_continuous μ).mp hsquare

set_option maxHeartbeats 800000 in
lemma cross_abs_cesaro_of_self (D : HilbertOperatorData)
    (u : D.H)
    (hself : ∀ z : D.H, @inner ℂ D.H _ u z = 0 →
      cesaroTendsTo (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) z) z‖) 0)
    (x y : D.H) (hx : @inner ℂ D.H _ u x = 0)
    (hy : @inner ℂ D.H _ u y = 0) :
    cesaroTendsTo (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) x) y‖) 0 := by
  let z₁ := x + y
  let z₂ := x - y
  let z₃ := x + Complex.I • y
  let z₄ := x - Complex.I • y
  let q : ℕ → ℝ := fun n =>
    (‖@inner ℂ D.H _ ((D.U^[n]) z₁) z₁‖ +
      ‖@inner ℂ D.H _ ((D.U^[n]) z₂) z₂‖ +
      ‖@inner ℂ D.H _ ((D.U^[n]) z₃) z₃‖ +
      ‖@inner ℂ D.H _ ((D.U^[n]) z₄) z₄‖) / 4
  have hz₁ : @inner ℂ D.H _ u z₁ = 0 := by simp [z₁, hx, hy]
  have hz₂ : @inner ℂ D.H _ u z₂ = 0 := by simp [z₂, hx, hy]
  have hz₃ : @inner ℂ D.H _ u z₃ = 0 := by simp [z₃, hx, hy]
  have hz₄ : @inner ℂ D.H _ u z₄ = 0 := by simp [z₄, hx, hy]
  have hq : cesaroTendsTo q 0 := by
    have hs := WeakSpectrum.cesaroTendsTo_add
      (WeakSpectrum.cesaroTendsTo_add
        (WeakSpectrum.cesaroTendsTo_add (hself z₁ hz₁) (hself z₂ hz₂))
          (hself z₃ hz₃)) (hself z₄ hz₄)
    have hc := WeakSpectrum.cesaroTendsTo_const_mul (1 / 4) hs
    simpa [q, div_eq_mul_inv, mul_comm] using hc
  apply WeakSpectrum.cesaroTendsTo_of_nonneg_le
    (fun n => norm_nonneg _) (b := q) ?_ hq
  intro n
  have hiter (v : D.H) : ((D.U ^ n).toLinearMap) v = (D.U^[n]) v := by
    change (D.U ^ n) v = (D.U^[n]) v
    rw [ContinuousLinearMap.coe_pow]
  have hadd (v w : D.H) :
      (D.U^[n]) (v + w) = (D.U^[n]) v + (D.U^[n]) w := by
    rw [← hiter, ← hiter, ← hiter]
    exact map_add _ v w
  have hsub (v w : D.H) :
      (D.U^[n]) (v - w) = (D.U^[n]) v - (D.U^[n]) w := by
    rw [← hiter, ← hiter, ← hiter]
    exact map_sub _ v w
  have hpol := inner_map_polarization' ((D.U ^ n).toLinearMap) x y
  simp_rw [hiter] at hpol
  rw [hpol]
  have htri :
    ‖@inner ℂ D.H _ ((D.U^[n]) (x + y)) (x + y) -
        @inner ℂ D.H _ ((D.U^[n]) (x - y)) (x - y) -
        Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x + Complex.I • y))
          (x + Complex.I • y) +
        Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x - Complex.I • y))
          (x - Complex.I • y)‖ ≤
      ‖@inner ℂ D.H _ ((D.U^[n]) (x + y)) (x + y)‖ +
        ‖@inner ℂ D.H _ ((D.U^[n]) (x - y)) (x - y)‖ +
        ‖Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x + Complex.I • y))
          (x + Complex.I • y)‖ +
        ‖Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x - Complex.I • y))
          (x - Complex.I • y)‖ := by
      calc
        _ ≤ ‖@inner ℂ D.H _ ((D.U^[n]) (x + y)) (x + y) -
              @inner ℂ D.H _ ((D.U^[n]) (x - y)) (x - y) -
              Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x + Complex.I • y))
                (x + Complex.I • y)‖ +
            ‖Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x - Complex.I • y))
                (x - Complex.I • y)‖ := norm_add_le _ _
        _ ≤ (‖@inner ℂ D.H _ ((D.U^[n]) (x + y)) (x + y) -
              @inner ℂ D.H _ ((D.U^[n]) (x - y)) (x - y)‖ +
            ‖Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x + Complex.I • y))
                (x + Complex.I • y)‖) + _ := by
                  gcongr
                  exact norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
  rw [norm_div]
  rw [Complex.norm_ofNat]
  calc
    _ ≤ (‖@inner ℂ D.H _ ((D.U^[n]) (x + y)) (x + y)‖ +
          ‖@inner ℂ D.H _ ((D.U^[n]) (x - y)) (x - y)‖ +
          ‖Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x + Complex.I • y))
            (x + Complex.I • y)‖ +
          ‖Complex.I * @inner ℂ D.H _ ((D.U^[n]) (x - Complex.I • y))
            (x - Complex.I • y)‖) / 4 := by
      exact div_le_div_of_nonneg_right htri (by norm_num)
    _ = q n := by
      dsimp only [q, z₁, z₂, z₃, z₄]
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      ring

set_option maxRecDepth 10000 in
lemma centered_self_abs_cesaro_of_spectral_condition (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hcond : ∀ f : M.X → ℂ, IsZeroMeanFunction M f →
      (∀ μ : CircleMeasureData, HasFunctionSpectralMeasure M f μ →
        IsContinuousCircleMeasure μ) ∧
      Tendsto (spectralAbsoluteCesaro M f) atTop (nhds 0))
    (H : MeasureTheory.Lp ℂ 2 M.μ)
    (hH : @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (CorrelationMean.oneLp M hM) H = 0) :
    cesaroTendsTo (fun n => ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
      (((WeakSpectrum.koopmanData M hM).U^[n]) H) H‖) 0 := by
  let f : M.X → ℂ := fun x => H x
  have hf : M.lpMember 2 f := MeasureTheory.Lp.memLp H
  have hmean : ∫ x, f x ∂M.μ = 0 := by
    change ∫ x, H x ∂M.μ = 0
    rw [CorrelationMean.integral_eq_inner_oneLp M hM H]
    exact hH
  have habs := (hcond f ⟨hf, hmean⟩).2
  have hcorr (n : ℕ) : functionCorrelation M f f n =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ H
        (((WeakSpectrum.koopmanData M hM).U^[n]) H) := by
    rw [CorrelationMean.functionCorrelation_eq_innerLp M hM f f hf hf n]
    rw [← CorrelationMean.koopmanIterLp_apply_toLp M hM n f hf]
    have hfH : hf.toLp f = H := by
      exact MeasureTheory.Lp.toLp_coeFn H hf
    rw [hfH]
    exact congrArg
      (fun K => @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ H K)
      (WeakSpectrum.koopmanData_iter_eq_koopmanIterLp M hM n H).symm
  unfold cesaroTendsTo seqTendsTo cesaroAverage
  have hshift := habs.comp (Filter.tendsto_add_atTop_nat 1)
  convert hshift using 1
  funext N
  simp [spectralAbsoluteCesaro, hcorr, norm_inner_symm,
    Nat.cast_add, Nat.cast_one]

lemma zeroMean_spectral_implies_weakMixing (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hcond : ∀ f : M.X → ℂ, IsZeroMeanFunction M f →
      (∀ μ : CircleMeasureData, HasFunctionSpectralMeasure M f μ →
        IsContinuousCircleMeasure μ) ∧
      Tendsto (spectralAbsoluteCesaro M f) atTop (nhds 0)) :
    IsWeakMixing M := by
  rw [CorrelationMean.weakMixing_iff_functionCorrelations M hM]
  intro f g hf hg
  let F : MeasureTheory.Lp ℂ 2 M.μ := hf.toLp f
  let G : MeasureTheory.Lp ℂ 2 M.μ := hg.toLp g
  let u := CorrelationMean.oneLp M hM
  have hself (H : MeasureTheory.Lp ℂ 2 M.μ)
      (hH : @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ u H = 0) :
      cesaroTendsTo (fun n => ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((WeakSpectrum.koopmanData M hM).U^[n]) H) H‖) 0 :=
    centered_self_abs_cesaro_of_spectral_condition M hM hcond H hH
  have hcross := cross_abs_cesaro_of_self (WeakSpectrum.koopmanData M hM) u
    hself (WeakSpectrum.centerLp M hM F) (WeakSpectrum.centerLp M hM G)
    (WeakSpectrum.inner_oneLp_centerLp M hM F)
    (WeakSpectrum.inner_oneLp_centerLp M hM G)
  have hprod :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ u F *
        star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ u G) =
          productOfMeans M f g := by
    dsimp only [u, F, G]
    rw [← CorrelationMean.integral_eq_inner_oneLp,
      ← CorrelationMean.integral_eq_inner_oneLp]
    rw [MeasureTheory.integral_congr_ae hf.coeFn_toLp,
      MeasureTheory.integral_congr_ae hg.coeFn_toLp]
    rfl
  have hcoeff (n : ℕ) :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (WeakSpectrum.centerLp M hM G)
          (((WeakSpectrum.koopmanData M hM).U^[n])
            (WeakSpectrum.centerLp M hM F)) =
        functionCorrelation M f g n - productOfMeans M f g := by
    rw [WeakSpectrum.centered_koopman_coefficient,
      WeakSpectrum.koopmanData_iter_eq_koopmanIterLp, hprod]
    change @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hg.toLp g)
      (CorrelationMean.koopmanIterLp M hM n (hf.toLp f)) -
        productOfMeans M f g = _
    rw [CorrelationMean.koopmanIterLp_apply_toLp]
    rw [← CorrelationMean.functionCorrelation_eq_innerLp M hM f g hf hg n]
  convert hcross using 1
  funext n
  rw [norm_inner_symm, hcoeff]

lemma cross_tendsto_zero_of_self (D : HilbertOperatorData) (u : D.H)
    (hself : ∀ z : D.H, @inner ℂ D.H _ u z = 0 →
      Tendsto (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) z) z‖) atTop (nhds 0))
    (x y : D.H) (hx : @inner ℂ D.H _ u x = 0)
    (hy : @inner ℂ D.H _ u y = 0) :
    Tendsto (fun n => @inner ℂ D.H _ ((D.U^[n]) x) y) atTop (nhds 0) := by
  let z₁ := x + y
  let z₂ := x - y
  let z₃ := x + Complex.I • y
  let z₄ := x - Complex.I • y
  have hz₁ : @inner ℂ D.H _ u z₁ = 0 := by simp [z₁, hx, hy]
  have hz₂ : @inner ℂ D.H _ u z₂ = 0 := by simp [z₂, hx, hy]
  have hz₃ : @inner ℂ D.H _ u z₃ = 0 := by simp [z₃, hx, hy]
  have hz₄ : @inner ℂ D.H _ u z₄ = 0 := by simp [z₄, hx, hy]
  have h₁ : Tendsto (fun n => @inner ℂ D.H _ ((D.U^[n]) z₁) z₁)
      atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (hself z₁ hz₁)
  have h₂ : Tendsto (fun n => @inner ℂ D.H _ ((D.U^[n]) z₂) z₂)
      atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (hself z₂ hz₂)
  have h₃ : Tendsto (fun n => @inner ℂ D.H _ ((D.U^[n]) z₃) z₃)
      atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (hself z₃ hz₃)
  have h₄ : Tendsto (fun n => @inner ℂ D.H _ ((D.U^[n]) z₄) z₄)
      atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (hself z₄ hz₄)
  have hI₃ := h₃.const_mul Complex.I
  have hI₄ := h₄.const_mul Complex.I
  have hcomb : Tendsto (fun n =>
      @inner ℂ D.H _ ((D.U^[n]) z₁) z₁ -
      @inner ℂ D.H _ ((D.U^[n]) z₂) z₂ -
      Complex.I * @inner ℂ D.H _ ((D.U^[n]) z₃) z₃ +
      Complex.I * @inner ℂ D.H _ ((D.U^[n]) z₄) z₄) atTop (nhds 0) := by
    simpa using ((h₁.sub h₂).sub hI₃).add hI₄
  have hdiv := hcomb.div_const (4 : ℂ)
  convert hdiv using 1
  · funext n
    have hiter (v : D.H) : ((D.U ^ n).toLinearMap) v = (D.U^[n]) v := by
      change (D.U ^ n) v = (D.U^[n]) v
      rw [ContinuousLinearMap.coe_pow]
    have hpol := inner_map_polarization' ((D.U ^ n).toLinearMap) x y
    simpa only [z₁, z₂, z₃, z₄, hiter, map_add, map_sub, map_smul] using hpol
  · norm_num

lemma strongMixing_iff_zeroMean_autocorrelation (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    IsStrongMixing M ↔
      ∀ f : M.X → ℂ, IsZeroMeanFunction M f →
        Tendsto (fun n => ‖functionCorrelation M f f n‖) atTop (nhds 0) := by
  constructor
  · intro hstrong f hf
    have h := CorrelationMean.strongMixing_functionCorrelations
      M hstrong f f hf.1 hf.1
    have hzero : productOfMeans M f f = 0 := by
      simp [productOfMeans, hf.2]
    rw [hzero] at h
    exact tendsto_norm_zero.comp h
  · intro hcond
    rw [CorrelationMean.strongMixing_iff_functionCorrelations M hM]
    intro f g hf hg
    let F : MeasureTheory.Lp ℂ 2 M.μ := hf.toLp f
    let G : MeasureTheory.Lp ℂ 2 M.μ := hg.toLp g
    let u := CorrelationMean.oneLp M hM
    have hself (H : MeasureTheory.Lp ℂ 2 M.μ)
        (hH : @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ u H = 0) :
        Tendsto (fun n => ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (((WeakSpectrum.koopmanData M hM).U^[n]) H) H‖) atTop (nhds 0) := by
      let h : M.X → ℂ := fun x => H x
      have hh : M.lpMember 2 h := MeasureTheory.Lp.memLp H
      have hmean : ∫ x, h x ∂M.μ = 0 := by
        rw [CorrelationMean.integral_eq_inner_oneLp]
        exact hH
      have hc := hcond h ⟨hh, hmean⟩
      have hcorr (n : ℕ) : functionCorrelation M h h n =
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ H
            (((WeakSpectrum.koopmanData M hM).U^[n]) H) := by
        rw [CorrelationMean.functionCorrelation_eq_innerLp M hM h h hh hh n]
        rw [← CorrelationMean.koopmanIterLp_apply_toLp M hM n h hh]
        have hhH : hh.toLp h = H := by
          exact MeasureTheory.Lp.toLp_coeFn H hh
        rw [hhH]
        exact congrArg
          (fun K => @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ H K)
          (WeakSpectrum.koopmanData_iter_eq_koopmanIterLp M hM n H).symm
      simpa only [hcorr, norm_inner_symm] using hc
    have hcross := cross_tendsto_zero_of_self (WeakSpectrum.koopmanData M hM) u
      hself (WeakSpectrum.centerLp M hM F) (WeakSpectrum.centerLp M hM G)
      (WeakSpectrum.inner_oneLp_centerLp M hM F)
      (WeakSpectrum.inner_oneLp_centerLp M hM G)
    have hprod :
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ u F *
          star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ u G) =
            productOfMeans M f g := by
      dsimp only [u, F, G]
      rw [← CorrelationMean.integral_eq_inner_oneLp,
        ← CorrelationMean.integral_eq_inner_oneLp]
      rw [MeasureTheory.integral_congr_ae hf.coeFn_toLp,
        MeasureTheory.integral_congr_ae hg.coeFn_toLp]
      rfl
    have hcoeff (n : ℕ) :
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
            (WeakSpectrum.centerLp M hM G)
            (((WeakSpectrum.koopmanData M hM).U^[n])
              (WeakSpectrum.centerLp M hM F)) =
          functionCorrelation M f g n - productOfMeans M f g := by
      rw [WeakSpectrum.centered_koopman_coefficient,
        WeakSpectrum.koopmanData_iter_eq_koopmanIterLp, hprod]
      change @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ (hg.toLp g)
        (CorrelationMean.koopmanIterLp M hM n (hf.toLp f)) -
          productOfMeans M f g = _
      rw [CorrelationMean.koopmanIterLp_apply_toLp]
      rw [← CorrelationMean.functionCorrelation_eq_innerLp M hM f g hf hg n]
    rw [← tendsto_sub_nhds_zero_iff]
    have hcross' : Tendsto (fun n => star
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          (((WeakSpectrum.koopmanData M hM).U^[n])
            (WeakSpectrum.centerLp M hM F))
          (WeakSpectrum.centerLp M hM G))) atTop (nhds 0) := by
      simpa using hcross.star
    convert hcross' using 1
    funext n
    rw [show star (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((WeakSpectrum.koopmanData M hM).U^[n])
          (WeakSpectrum.centerLp M hM F))
        (WeakSpectrum.centerLp M hM G)) =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (WeakSpectrum.centerLp M hM G)
        (((WeakSpectrum.koopmanData M hM).U^[n])
          (WeakSpectrum.centerLp M hM F)) by
            exact inner_conj_symm _ _]
    exact (hcoeff n).symm

theorem spectralCharacterizationsOfMixing (M : System.{u}) :
    SpectralCharacterizationsOfMixing M := by
  intro hM
  refine ⟨ergodic_iff_spectral_condition M hM, ?_,
    strongMixing_iff_zeroMean_autocorrelation M hM⟩
  constructor
  · exact weakMixing_implies_zeroMean_spectral M
  · exact zeroMean_spectral_implies_weakMixing M hM

end Chapter02.SpectralMixing
