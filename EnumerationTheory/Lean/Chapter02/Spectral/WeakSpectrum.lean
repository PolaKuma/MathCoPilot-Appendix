import Chapter02.Spectral.SpectralMeasureType
import Chapter02.Section01
import Chapter02.Ergodic.ZeroDensity
import Chapter02.Ergodic.CorrelationMean

open Classical MeasureTheory Filter Topology
open scoped BigOperators ComplexOrder ENNReal

noncomputable section

namespace Chapter02.WeakSpectrum

universe u

noncomputable def koopmanData (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) : HilbertOperatorData where
  H := Lp ℂ 2 M.μ
  normedAddCommGroup := inferInstance
  innerProductSpace := inferInstance
  completeSpace := inferInstance
  U := (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).toContinuousLinearMap

lemma measurePreserving_of_project_map (M : System.{u}) (S : M.X → M.X)
    (hS : Chapter01.IsMeasurePreservingMap M.𝓧 M.μ M.𝓧 M.μ S) :
    MeasurePreserving S M.μ M.μ := by
  have hmeas : Measurable S := by
    intro A hA
    exact hS.1 A hA
  refine ⟨hmeas, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hmeas hA]
  exact hS.2 A hA

lemma koopmanData_unitary (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hInv : Chapter01.IsInvertibleMeasurePreservingMap
      M.𝓧 M.μ M.𝓧 M.μ M.T) : IsUnitary (koopmanData M hM) := by
  constructor
  · rintro (F : Lp ℂ 2 M.μ)
    obtain ⟨S, _hTmp, hSmap, hleft, hright⟩ := hInv
    let hS : MeasurePreserving S M.μ M.μ :=
      measurePreserving_of_project_map M S hSmap
    let G : Lp ℂ 2 M.μ := Lp.compMeasurePreserving S hS F
    refine ⟨G, ?_⟩
    change Lp.compMeasurePreserving M.T hM.2 G = F
    apply Lp.ext
    have hSFcomp := hM.2.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving F hS)
    filter_upwards [Lp.coeFn_compMeasurePreserving G hM.2, hSFcomp] with x hTG hSF
    rw [hTG]
    change G (M.T x) = F x
    have hSF' : G (M.T x) = F (S (M.T x)) := by
      simpa [G, Function.comp_def] using hSF
    rw [hSF']
    exact congrArg (fun z => F z) (hleft x)
  · rintro (F : Lp ℂ 2 M.μ)
    exact (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map F

lemma koopmanData_apply_toLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f 2 M.μ) :
    (koopmanData M hM).U (hf.toLp f) =
      (hf.comp_measurePreserving hM.2).toLp (Chapter01.koopman M.T f) := by
  rfl

lemma koopmanData_iter_ae (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ)
    (F : Lp ℂ 2 M.μ) :
    ((show Lp ℂ 2 M.μ from ((koopmanData M hM).U^[n]) F) : M.X → ℂ) =ᵐ[M.μ]
      fun x => (F : M.X → ℂ) ((M.T^[n]) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hcoe := Lp.coeFn_compMeasurePreserving
        (((koopmanData M hM).U^[n]) F) hM.2
      have hih := hM.2.quasiMeasurePreserving.ae_eq_comp ih
      filter_upwards [hcoe, hih] with x hx hix
      change (Lp.compMeasurePreserving M.T hM.2
        (((koopmanData M hM).U^[n]) F)) x = _
      rw [hx, hix]
      simp only [Function.comp_apply, ← Function.iterate_succ_apply]

lemma koopmanData_iter_eq_koopmanIterLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ)
    (F : Lp ℂ 2 M.μ) :
    ((koopmanData M hM).U^[n]) F =
      CorrelationMean.koopmanIterLp M hM n F := by
  apply Lp.ext
  filter_upwards [koopmanData_iter_ae M hM n F,
    Lp.coeFn_compMeasurePreserving F (hM.2.iterate n)] with x hx hy
  rw [hx]
  change F ((M.T^[n]) x) =
    (Lp.compMeasurePreserving (M.T^[n]) (hM.2.iterate n) F) x
  exact hy.symm

lemma eigenfunction_to_eigenvector (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (lam : ℂ) (f : M.X → ℂ) (hf : Eigenfunction M lam f) :
    IsEigenvector (koopmanData M hM) (hf.1.toLp f) := by
  refine ⟨?_, lam, ?_⟩
  · intro hzero
    apply hf.2.1
    filter_upwards [hf.1.coeFn_toLp, Lp.coeFn_zero ℂ 2 M.μ] with x hx hz
    rw [hzero] at hx
    exact hx.symm.trans hz
  · rw [koopmanData_apply_toLp]
    apply Lp.ext
    filter_upwards [(hf.1.comp_measurePreserving hM.2).coeFn_toLp,
      Lp.coeFn_smul lam (hf.1.toLp f), hf.1.coeFn_toLp, hf.2.2] with x hcomp hsmul hcoe heig
    have hcomp' :
        ((hf.1.comp_measurePreserving hM.2).toLp (Chapter01.koopman M.T f)) x =
          Chapter01.koopman M.T f x := by
      simpa [Chapter01.koopman, Function.comp_def] using hcomp
    rw [hcomp', hsmul]
    change Chapter01.koopman M.T f x = lam * (hf.1.toLp f) x
    rw [hcoe]
    exact heig

lemma eigenvector_to_eigenfunction (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) (hF : IsEigenvector (koopmanData M hM) F) :
    ∃ lam : ℂ, Eigenfunction M lam (fun x => F x) := by
  obtain ⟨hF0, lam, hlam⟩ := hF
  refine ⟨lam, Lp.memLp F, ?_, ?_⟩
  · intro hzero
    apply hF0
    apply Lp.ext
    exact hzero.trans (Lp.coeFn_zero ℂ 2 M.μ).symm
  · have hcoe := Lp.coeFn_compMeasurePreserving F hM.2
    have hsmul := Lp.coeFn_smul lam F
    change Lp.compMeasurePreserving M.T hM.2 F = lam • F at hlam
    have heq : (fun x => (Lp.compMeasurePreserving M.T hM.2 F) x) =ᵐ[M.μ]
        fun x => (lam • F) x := by rw [hlam]
    filter_upwards [hcoe, hsmul, heq] with x hcx hsx heq
    rw [hcx, hsx] at heq
    simpa [Chapter01.koopman, Function.comp_def, Pi.smul_apply, smul_eq_mul] using heq

lemma zeroMean_to_continuous (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hcont : HasContinuousSpectrum M)
    (f : M.X → ℂ) (hf : MemLp f 2 M.μ) (hmean : ∫ x, f x ∂M.μ = 0) :
    InContinuousSpectralSubspace (koopmanData M hM) (hf.toLp f) := by
  rintro (Y : Lp ℂ 2 M.μ) hY
  obtain ⟨lam, hYeig⟩ := eigenvector_to_eigenfunction M hM Y hY
  have hlam : lam = 1 := hcont.1 lam ⟨fun x => Y x, hYeig⟩
  subst lam
  obtain ⟨c, hYc⟩ := hcont.2 (fun x => Y x) hYeig
  rw [L2.inner_def]
  calc
    (∫ x, @inner ℂ ℂ _ ((hf.toLp f) x) (Y x) ∂M.μ) =
        ∫ x, c * (starRingEnd ℂ) (f x) ∂M.μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hYc] with x hfx hYx
      rw [hfx, hYx, RCLike.inner_apply]
    _ = c * ∫ x, (starRingEnd ℂ) (f x) ∂M.μ := integral_const_mul c _
    _ = c * (starRingEnd ℂ) (∫ x, f x ∂M.μ) := by rw [integral_conj]
    _ = 0 := by simp [hmean]

lemma continuous_autocorrelation_abs_cesaro (D : HilbertOperatorData)
    (hD : IsUnitary D) (z : D.H) (hz : InContinuousSpectralSubspace D z) :
    cesaroTendsTo
      (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) z) z‖) 0 := by
  have hw := (SpectralWiener.wienerTheorem D hD z).mp hz
  have hsq : cesaroTendsTo
      (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) z) z‖ ^ 2) 0 := by
    unfold cesaroTendsTo seqTendsTo cesaroAverage
    have hcomp := hw.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun N : ℕ => if N + 1 = 0 then 0 else
      (((N + 1 : ℕ) : ℝ)⁻¹) * ∑ n ∈ Finset.range (N + 1),
        ‖@inner ℂ D.H _ ((D.U^[n]) z) z‖ ^ 2) atTop (nhds 0) at hcomp
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  exact ZeroDensity.cesaro_norm_of_cesaro_norm_sq
    (fun n => @inner ℂ D.H _ ((D.U^[n]) z) z) hsq

lemma cesaroTendsTo_add {a b : ℕ → ℝ}
    (ha : cesaroTendsTo a 0) (hb : cesaroTendsTo b 0) :
    cesaroTendsTo (fun n => a n + b n) 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha hb ⊢
  have h := ha.add hb
  convert h using 1
  · funext N
    rw [Finset.sum_add_distrib]
    ring
  · simp

lemma cesaroTendsTo_const_mul {a : ℕ → ℝ} (c : ℝ)
    (ha : cesaroTendsTo a 0) : cesaroTendsTo (fun n => c * a n) 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha ⊢
  have h : Tendsto (fun N => c *
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), a n))
      atTop (nhds (c * 0)) := tendsto_const_nhds.mul ha
  convert h using 1
  · funext N
    rw [← Finset.mul_sum]
    ring
  · simp

lemma cesaroTendsTo_of_nonneg_le {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
    (hb : cesaroTendsTo b 0) : cesaroTendsTo a 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at hb ⊢
  apply squeeze_zero
    (f := fun N => (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), a n))
    (g := fun N => (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1), b n))
  · intro N
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun n _ => ha n)
  · intro N
    gcongr with n hn
    exact hab n
  · exact hb

lemma continuous_add (D : HilbertOperatorData) (x y : D.H)
    (hx : InContinuousSpectralSubspace D x)
    (hy : InContinuousSpectralSubspace D y) :
    InContinuousSpectralSubspace D (x + y) := by
  intro z hz
  rw [inner_add_left, hx z hz, hy z hz, add_zero]

lemma continuous_sub (D : HilbertOperatorData) (x y : D.H)
    (hx : InContinuousSpectralSubspace D x)
    (hy : InContinuousSpectralSubspace D y) :
    InContinuousSpectralSubspace D (x - y) := by
  intro z hz
  rw [inner_sub_left, hx z hz, hy z hz, sub_zero]

lemma continuous_smul (D : HilbertOperatorData) (c : ℂ) (x : D.H)
    (hx : InContinuousSpectralSubspace D x) :
    InContinuousSpectralSubspace D (c • x) := by
  intro z hz
  rw [inner_smul_left, hx z hz]
  simp

set_option maxHeartbeats 800000 in
lemma continuous_cross_abs_cesaro (D : HilbertOperatorData)
    (hD : IsUnitary D) (x y : D.H)
    (hx : InContinuousSpectralSubspace D x)
    (hy : InContinuousSpectralSubspace D y) :
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
  have h₁ := continuous_autocorrelation_abs_cesaro D hD z₁
    (continuous_add D x y hx hy)
  have h₂ := continuous_autocorrelation_abs_cesaro D hD z₂
    (continuous_sub D x y hx hy)
  have h₃ := continuous_autocorrelation_abs_cesaro D hD z₃
    (continuous_add D x (Complex.I • y) hx (continuous_smul D Complex.I y hy))
  have h₄ := continuous_autocorrelation_abs_cesaro D hD z₄
    (continuous_sub D x (Complex.I • y) hx (continuous_smul D Complex.I y hy))
  have hq : cesaroTendsTo q 0 := by
    have hs := cesaroTendsTo_add
      (cesaroTendsTo_add (cesaroTendsTo_add h₁ h₂) h₃) h₄
    have hc := cesaroTendsTo_const_mul (1 / 4) hs
    simpa [q, div_eq_mul_inv, mul_comm] using hc
  apply cesaroTendsTo_of_nonneg_le (fun n => norm_nonneg _) (b := q) ?_ hq
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
  have hpol := inner_map_polarization'
    ((D.U ^ n).toLinearMap) x y
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
                (x + Complex.I • y)‖) + _ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by gcongr; exact norm_sub_le _ _
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

lemma oneLp_coe (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    ((CorrelationMean.oneLp M hM : Lp ℂ 2 M.μ) : M.X → ℂ) =ᵐ[M.μ]
      fun _ => 1 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  exact (memLp_const (p := (2 : ENNReal)) (c := (1 : ℂ))).coeFn_toLp

lemma inner_oneLp_self (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :
    @inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hM)
      (CorrelationMean.oneLp M hM) = 1 := by
  letI : IsProbabilityMeasure M.μ := hM.1
  rw [← CorrelationMean.integral_eq_inner_oneLp]
  rw [integral_congr_ae (oneLp_coe M hM)]
  simp

noncomputable def centerLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (F : Lp ℂ 2 M.μ) :
    Lp ℂ 2 M.μ :=
  F - (@inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hM) F) •
    CorrelationMean.oneLp M hM

lemma inner_oneLp_centerLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (F : Lp ℂ 2 M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hM)
      (centerLp M hM F) = 0 := by
  rw [centerLp, inner_sub_right, inner_smul_right, inner_oneLp_self]
  simp

lemma centerLp_continuous (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hcont : HasContinuousSpectrum M) (F : Lp ℂ 2 M.μ) :
    InContinuousSpectralSubspace (koopmanData M hM) (centerLp M hM F) := by
  let hf := Lp.memLp (centerLp M hM F)
  have hmean : ∫ x, (centerLp M hM F) x ∂M.μ = 0 := by
    rw [CorrelationMean.integral_eq_inner_oneLp]
    exact inner_oneLp_centerLp M hM F
  have h := zeroMean_to_continuous M hM hcont
    (fun x => (centerLp M hM F) x) hf hmean
  simpa only [Lp.toLp_coeFn] using h

lemma inner_oneLp_koopman_iter (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ)
    (F : Lp ℂ 2 M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hM)
      (((koopmanData M hM).U^[n]) F) =
    @inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hM) F := by
  rw [← CorrelationMean.integral_eq_inner_oneLp,
    ← CorrelationMean.integral_eq_inner_oneLp]
  rw [integral_congr_ae (koopmanData_iter_ae M hM n F)]
  have hstrong : AEStronglyMeasurable (fun x => F x)
      (Measure.map (M.T^[n]) M.μ) := by
    rw [(hM.2.iterate n).map_eq]
    exact (Lp.memLp F).1
  have hmap := MeasureTheory.integral_map
    (hM.2.iterate n).measurable.aemeasurable hstrong
  rw [(hM.2.iterate n).map_eq] at hmap
  exact hmap.symm

lemma koopmanData_iter_sub (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ)
    (F G : Lp ℂ 2 M.μ) :
    ((koopmanData M hM).U^[n]) (F - G) =
      ((koopmanData M hM).U^[n]) F - ((koopmanData M hM).U^[n]) G := by
  have hiter (H : Lp ℂ 2 M.μ) :
      ((koopmanData M hM).U ^ n) H = ((koopmanData M hM).U^[n]) H := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, ← hiter, ← hiter]
  exact map_sub _ F G

lemma koopmanData_iter_smul (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ)
    (c : ℂ) (F : Lp ℂ 2 M.μ) :
    ((koopmanData M hM).U^[n]) (c • F) =
      c • ((koopmanData M hM).U^[n]) F := by
  have hiter (H : Lp ℂ 2 M.μ) :
      ((koopmanData M hM).U ^ n) H = ((koopmanData M hM).U^[n]) H := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, ← hiter]
  exact map_smul _ c F

lemma centered_koopman_coefficient (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ)
    (F G : Lp ℂ 2 M.μ) :
    @inner ℂ (Lp ℂ 2 M.μ) _ (centerLp M hM G)
        (((koopmanData M hM).U^[n]) (centerLp M hM F)) =
      @inner ℂ (Lp ℂ 2 M.μ) _ G (((koopmanData M hM).U^[n]) F) -
        @inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hM) F *
          star (@inner ℂ (Lp ℂ 2 M.μ) _
            (CorrelationMean.oneLp M hM) G) := by
  let u := CorrelationMean.oneLp M hM
  let a := @inner ℂ (Lp ℂ 2 M.μ) _ u F
  let b := @inner ℂ (Lp ℂ 2 M.μ) _ u G
  have hu : ((koopmanData M hM).U^[n]) u = u := by
    apply Lp.ext
    filter_upwards [koopmanData_iter_ae M hM n u,
      (hM.2.iterate n).quasiMeasurePreserving.ae_eq_comp (oneLp_coe M hM),
      oneLp_coe M hM] with x hx hcomp hone
    rw [hx]
    exact hcomp.trans hone.symm
  have hmean := inner_oneLp_koopman_iter M hM n F
  change @inner ℂ (Lp ℂ 2 M.μ) _ (G - b • u)
      (((koopmanData M hM).U^[n]) (F - a • u)) = _
  rw [koopmanData_iter_sub, koopmanData_iter_smul, hu]
  rw [inner_sub_left]
  simp only [inner_sub_right, inner_smul_left, inner_smul_right]
  have hsymm : @inner ℂ (Lp ℂ 2 M.μ) _ G u = star b := by
    exact (inner_conj_symm G u).symm
  have huu : @inner ℂ (Lp ℂ 2 M.μ) _ u u = 1 :=
    inner_oneLp_self M hM
  rw [hsymm]
  change _ = _ - a * star b
  change @inner ℂ (Lp ℂ 2 M.μ) _ u
      (((koopmanData M hM).U^[n]) F) = a at hmean
  rw [hmean, huu]
  ring

lemma continuousSpectrum_to_weakMixing (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hInv : Chapter01.IsInvertibleMeasurePreservingMap
      M.𝓧 M.μ M.𝓧 M.μ M.T)
    (hcont : HasContinuousSpectrum M) : IsWeakMixing M := by
  rw [CorrelationMean.weakMixing_iff_functionCorrelations M hM]
  intro f g hf hg
  let F : Lp ℂ 2 M.μ := hf.toLp f
  let G : Lp ℂ 2 M.μ := hg.toLp g
  have hcross := continuous_cross_abs_cesaro (koopmanData M hM)
    (koopmanData_unitary M hM hInv) (centerLp M hM F) (centerLp M hM G)
    (centerLp_continuous M hM hcont F) (centerLp_continuous M hM hcont G)
  have hprod :
      @inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hM) F *
        star (@inner ℂ (Lp ℂ 2 M.μ) _
          (CorrelationMean.oneLp M hM) G) = productOfMeans M f g := by
    rw [← CorrelationMean.integral_eq_inner_oneLp,
      ← CorrelationMean.integral_eq_inner_oneLp]
    have hfint : (∫ x, F x ∂M.μ) = ∫ x, f x ∂M.μ :=
      integral_congr_ae hf.coeFn_toLp
    have hgint : (∫ x, G x ∂M.μ) = ∫ x, g x ∂M.μ :=
      integral_congr_ae hg.coeFn_toLp
    rw [hfint, hgint]
    rfl
  have hcoeff (n : ℕ) :
      @inner ℂ (Lp ℂ 2 M.μ) _ (centerLp M hM G)
          (((koopmanData M hM).U^[n]) (centerLp M hM F)) =
        functionCorrelation M f g n - productOfMeans M f g := by
    rw [centered_koopman_coefficient, koopmanData_iter_eq_koopmanIterLp,
      hprod]
    change @inner ℂ (Lp ℂ 2 M.μ) _ (hg.toLp g)
      (CorrelationMean.koopmanIterLp M hM n (hf.toLp f)) -
        productOfMeans M f g = _
    rw [CorrelationMean.koopmanIterLp_apply_toLp]
    rw [← CorrelationMean.functionCorrelation_eq_innerLp M hM f g hf hg n]
  convert hcross using 1
  funext n
  rw [norm_inner_symm, hcoeff]

lemma cesaroTendsTo_const_zero {c : ℝ}
    (h : cesaroTendsTo (fun _ : ℕ => c) 0) : c = 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at h
  have hc : Tendsto (fun _ : ℕ => c) atTop (nhds 0) := by
    convert h using 1
    funext N
    simp
    field_simp
  exact tendsto_nhds_unique tendsto_const_nhds hc

lemma koopmanData_iter_oneLp (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) (n : ℕ) :
    ((koopmanData M hM).U^[n]) (CorrelationMean.oneLp M hM) =
      CorrelationMean.oneLp M hM := by
  apply Lp.ext
  filter_upwards [koopmanData_iter_ae M hM n (CorrelationMean.oneLp M hM),
    (hM.2.iterate n).quasiMeasurePreserving.ae_eq_comp (oneLp_coe M hM),
    oneLp_coe M hM] with x hx hcomp hone
  rw [hx]
  exact hcomp.trans hone.symm

lemma weakMixing_fixed_center_zero (M : System.{u})
    (hweak : IsWeakMixing M) (F : Lp ℂ 2 M.μ)
    (hF : (koopmanData M hweak.1).U F = F) :
    centerLp M hweak.1 F = 0 := by
  let H := centerLp M hweak.1 F
  have hH : (koopmanData M hweak.1).U H = H := by
    dsimp [H, centerLp]
    rw [map_sub, map_smul, hF]
    have hu := koopmanData_iter_oneLp M hweak.1 1
    rw [show (koopmanData M hweak.1).U
      (CorrelationMean.oneLp M hweak.1) =
        CorrelationMean.oneLp M hweak.1 by simpa using hu]
  have hcorr := CorrelationMean.weakMixing_lpCorrelations M hweak H H
  have hconst : cesaroTendsTo (fun _ : ℕ => ‖H‖ ^ 2) 0 := by
    convert hcorr using 1
    funext n
    rw [← koopmanData_iter_eq_koopmanIterLp]
    rw [SpectralPointMass.eigen_iterate (koopmanData M hweak.1) H 1
      (by simpa using hH)]
    change ‖H‖ ^ 2 = ‖@inner ℂ (Lp ℂ 2 M.μ) _ H ((1 : ℂ) ^ n • H) -
      @inner ℂ (Lp ℂ 2 M.μ) _ (CorrelationMean.oneLp M hweak.1) H *
        star (@inner ℂ (Lp ℂ 2 M.μ) _
          (CorrelationMean.oneLp M hweak.1) H)‖
    rw [show @inner ℂ (Lp ℂ 2 M.μ) _
      (CorrelationMean.oneLp M hweak.1) H = 0 by
        exact inner_oneLp_centerLp M hweak.1 F]
    simp
  have hnormsq : ‖H‖ ^ 2 = 0 := cesaroTendsTo_const_zero hconst
  have hnorm : ‖H‖ = 0 := by nlinarith [norm_nonneg H]
  exact norm_eq_zero.mp hnorm

lemma weakMixing_to_ergodic (M : System.{u})
    (hweak : IsWeakMixing M) : IsErgodic M := by
  rw [Section01.ergodicityInvariantFunctionCharacterizations M hweak.1]
  intro f hf hinv
  let F : Lp ℂ 2 M.μ := hf.toLp f
  have hF : (koopmanData M hweak.1).U F = F := by
    rw [koopmanData_apply_toLp]
    apply Lp.ext
    filter_upwards [(hf.comp_measurePreserving hweak.1.2).coeFn_toLp,
      hf.coeFn_toLp, hinv] with x hcomp hcoe hfix
    have hcomp' :
        ((hf.comp_measurePreserving hweak.1.2).toLp
          (Chapter01.koopman M.T f)) x = Chapter01.koopman M.T f x := by
      simpa [Chapter01.koopman, Function.comp_def] using hcomp
    rw [hcomp', hcoe]
    exact hfix
  have hzero := weakMixing_fixed_center_zero M hweak F hF
  let c := @inner ℂ (Lp ℂ 2 M.μ) _
    (CorrelationMean.oneLp M hweak.1) F
  have hFEq : F = c • CorrelationMean.oneLp M hweak.1 := by
    apply sub_eq_zero.mp
    change centerLp M hweak.1 F = 0
    exact hzero
  refine ⟨c, ?_⟩
  have heq : (fun x => F x) =ᵐ[M.μ]
      fun x => (c • CorrelationMean.oneLp M hweak.1) x := by
    rw [hFEq]
  filter_upwards [hf.coeFn_toLp, heq,
    Lp.coeFn_smul c (CorrelationMean.oneLp M hweak.1),
    oneLp_coe M hweak.1] with x hfcoe hEq hsmul hone
  rw [← hfcoe, hEq, hsmul]
  change c * (CorrelationMean.oneLp M hweak.1 : M.X → ℂ) x = c
  rw [hone]
  simp

lemma weakMixing_eigenvalue_eq_one (M : System.{u})
    (hweak : IsWeakMixing M)
    (hInv : Chapter01.IsInvertibleMeasurePreservingMap
      M.𝓧 M.μ M.𝓧 M.μ M.T)
    (lam : ℂ) (hlam : Eigenvalue M lam) : lam = 1 := by
  by_contra hlam1
  obtain ⟨f, hf, hf0, heig⟩ := hlam
  let F : Lp ℂ 2 M.μ := hf.toLp f
  have hF0 : F ≠ 0 := by
    intro hzero
    apply hf0
    filter_upwards [hf.coeFn_toLp, Lp.coeFn_zero ℂ 2 M.μ] with x hfx hz
    change hf.toLp f = 0 at hzero
    rw [hzero] at hfx
    exact hfx.symm.trans hz
  have hU : (koopmanData M hweak.1).U F = lam • F := by
    dsimp [F]
    rw [koopmanData_apply_toLp]
    apply Lp.ext
    filter_upwards [(hf.comp_measurePreserving hweak.1.2).coeFn_toLp,
      Lp.coeFn_smul lam (hf.toLp f), hf.coeFn_toLp, heig] with
        x hcomp hsmul hcoe heigx
    have hcomp' :
        ((hf.comp_measurePreserving hweak.1.2).toLp
          (Chapter01.koopman M.T f)) x = Chapter01.koopman M.T f x := by
      simpa [Chapter01.koopman, Function.comp_def] using hcomp
    rw [hcomp', hsmul]
    change Chapter01.koopman M.T f x = lam * (hf.toLp f) x
    rw [hcoe]
    exact heigx
  let u := CorrelationMean.oneLp M hweak.1
  let a := @inner ℂ (Lp ℂ 2 M.μ) _ u F
  have hmeanrel : a = lam * a := by
    have hmean := inner_oneLp_koopman_iter M hweak.1 1 F
    have hmean' :
        @inner ℂ (Lp ℂ 2 M.μ) _ u ((koopmanData M hweak.1).U F) = a := by
      simpa [u, a] using hmean
    calc
      a = @inner ℂ (Lp ℂ 2 M.μ) _ u ((koopmanData M hweak.1).U F) := hmean'.symm
      _ = @inner ℂ (Lp ℂ 2 M.μ) _ u (lam • F) := by rw [hU]
      _ = lam * a := by rw [inner_smul_right]
  have ha0 : a = 0 := by
    have hz : (lam - 1) * a = 0 := by
      rw [sub_mul, one_mul, ← hmeanrel, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hlam1)
  have hD := koopmanData_unitary M hweak.1 hInv
  have hnormlam : ‖lam‖ = 1 := by
    have heq : ‖F‖ = ‖lam‖ * ‖F‖ := by
      calc
        ‖F‖ = ‖(koopmanData M hweak.1).U F‖ := (hD.2 F).symm
        _ = ‖lam • F‖ := by rw [hU]
        _ = ‖lam‖ * ‖F‖ := norm_smul lam F
    have hpos : 0 < ‖F‖ := norm_pos_iff.mpr hF0
    nlinarith
  have hcorr := CorrelationMean.weakMixing_lpCorrelations M hweak F F
  have hconst : cesaroTendsTo (fun _ : ℕ => ‖F‖ ^ 2) 0 := by
    convert hcorr using 1
    funext n
    rw [← koopmanData_iter_eq_koopmanIterLp]
    rw [SpectralPointMass.eigen_iterate (koopmanData M hweak.1) F lam hU]
    change ‖F‖ ^ 2 = ‖@inner ℂ (Lp ℂ 2 M.μ) _ F (lam ^ n • F) -
      a * star a‖
    rw [ha0]
    simp [hnormlam]
  have hsq : ‖F‖ ^ 2 = 0 := cesaroTendsTo_const_zero hconst
  have : ‖F‖ = 0 := by nlinarith [norm_nonneg F]
  exact hF0 (norm_eq_zero.mp this)

theorem weakMixing_iff_continuousSpectrum (M : System.{u}) :
    WeakMixingIffContinuousSpectrum M := by
  intro hM hInv
  constructor
  · intro hweak
    refine ⟨fun lam hlam => weakMixing_eigenvalue_eq_one M hweak hInv lam hlam, ?_⟩
    have herg := weakMixing_to_ergodic M hweak
    have hchar := Section01.ergodicityInvariantFunctionCharacterizations M hM
    intro f hf
    apply (hchar.mp herg) f hf.1
    simpa using hf.2.2
  · exact continuousSpectrum_to_weakMixing M hM hInv

end Chapter02.WeakSpectrum
