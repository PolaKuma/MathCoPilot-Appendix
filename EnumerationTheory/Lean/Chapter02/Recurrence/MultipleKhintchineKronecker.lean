import Chapter02.Spectral.IsometryWiener
import Chapter02.Ergodic.VanDerCorput
import Chapter02.Spectral.EigenfunctionLemmas

open Classical Filter
open scoped BigOperators

noncomputable section

namespace Chapter02.MultipleKhintchineKronecker

universe u

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
    (ha : cesaroTendsTo a 0) :
    cesaroTendsTo (fun n => c * a n) 0 := by
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
    (hb : cesaroTendsTo b 0) :
    cesaroTendsTo a 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at hb ⊢
  apply squeeze_zero
    (f := fun N => (((N + 1 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range (N + 1), a n))
    (g := fun N => (((N + 1 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range (N + 1), b n))
  · intro N
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun n _ => ha n)
  · intro N
    gcongr with n hn
    exact hab n
  · exact hb

lemma continuous_add (D : HilbertOperatorData.{u}) (x y : D.H)
    (hx : InContinuousSpectralSubspace D x)
    (hy : InContinuousSpectralSubspace D y) :
    InContinuousSpectralSubspace D (x + y) := by
  intro z hz
  rw [inner_add_left, hx z hz, hy z hz, add_zero]

lemma continuous_sub (D : HilbertOperatorData.{u}) (x y : D.H)
    (hx : InContinuousSpectralSubspace D x)
    (hy : InContinuousSpectralSubspace D y) :
    InContinuousSpectralSubspace D (x - y) := by
  intro z hz
  rw [inner_sub_left, hx z hz, hy z hz, sub_zero]

lemma continuous_smul (D : HilbertOperatorData.{u}) (c : ℂ) (x : D.H)
    (hx : InContinuousSpectralSubspace D x) :
    InContinuousSpectralSubspace D (c • x) := by
  intro z hz
  rw [inner_smul_left, hx z hz]
  simp

set_option maxHeartbeats 800000 in
/-- Polarization upgrades the Wiener autocorrelation theorem for a linear
isometry to cross-correlations of two continuous-spectral vectors. -/
theorem continuous_cross_abs_cesaro
    (D : HilbertOperatorData.{u}) (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x y : D.H)
    (hx : InContinuousSpectralSubspace D x)
    (hy : InContinuousSpectralSubspace D y) :
    cesaroTendsTo
      (fun n => ‖@inner ℂ D.H _ ((D.U^[n]) x) y‖) 0 := by
  let z₁ := x + y
  let z₂ := x - y
  let z₃ := x + Complex.I • y
  let z₄ := x - Complex.I • y
  let q : ℕ → ℝ := fun n =>
    (‖@inner ℂ D.H _ ((D.U^[n]) z₁) z₁‖ +
      ‖@inner ℂ D.H _ ((D.U^[n]) z₂) z₂‖ +
      ‖@inner ℂ D.H _ ((D.U^[n]) z₃) z₃‖ +
      ‖@inner ℂ D.H _ ((D.U^[n]) z₄) z₄‖) / 4
  have h₁ := IsometryWiener.continuous_autocorrelation_abs_cesaro
    D hU z₁ (continuous_add D x y hx hy)
  have h₂ := IsometryWiener.continuous_autocorrelation_abs_cesaro
    D hU z₂ (continuous_sub D x y hx hy)
  have h₃ := IsometryWiener.continuous_autocorrelation_abs_cesaro
    D hU z₃ (continuous_add D x (Complex.I • y) hx
      (continuous_smul D Complex.I y hy))
  have h₄ := IsometryWiener.continuous_autocorrelation_abs_cesaro
    D hU z₄ (continuous_sub D x (Complex.I • y) hx
      (continuous_smul D Complex.I y hy))
  have hq : cesaroTendsTo q 0 := by
    have hs := cesaroTendsTo_add
      (cesaroTendsTo_add (cesaroTendsTo_add h₁ h₂) h₃) h₄
    have hc := cesaroTendsTo_const_mul (1 / 4) hs
    simpa [q, div_eq_mul_inv, mul_comm] using hc
  apply cesaroTendsTo_of_nonneg_le
    (fun n => norm_nonneg _) (b := q) ?_ hq
  intro n
  have hiter (v : D.H) : ((D.U ^ n).toLinearMap) v = (D.U^[n]) v := by
    change (D.U ^ n) v = (D.U^[n]) v
    rw [ContinuousLinearMap.coe_pow]
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
              Complex.I * @inner ℂ D.H _
                ((D.U^[n]) (x + Complex.I • y)) (x + Complex.I • y)‖ +
            ‖Complex.I * @inner ℂ D.H _
                ((D.U^[n]) (x - Complex.I • y))
                (x - Complex.I • y)‖ := norm_add_le _ _
        _ ≤ (‖@inner ℂ D.H _ ((D.U^[n]) (x + y)) (x + y) -
              @inner ℂ D.H _ ((D.U^[n]) (x - y)) (x - y)‖ +
            ‖Complex.I * @inner ℂ D.H _
                ((D.U^[n]) (x + Complex.I • y))
                (x + Complex.I • y)‖) + _ := by
                  gcongr
                  exact norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
  rw [norm_div, Complex.norm_ofNat]
  calc
    _ ≤ (‖@inner ℂ D.H _ ((D.U^[n]) (x + y)) (x + y)‖ +
          ‖@inner ℂ D.H _ ((D.U^[n]) (x - y)) (x - y)‖ +
          ‖Complex.I * @inner ℂ D.H _
            ((D.U^[n]) (x + Complex.I • y)) (x + Complex.I • y)‖ +
          ‖Complex.I * @inner ℂ D.H _
            ((D.U^[n]) (x - Complex.I • y))
            (x - Complex.I • y)‖) / 4 := by
      exact div_le_div_of_nonneg_right htri (by norm_num)
    _ = q n := by
      dsimp only [q, z₁, z₂, z₃, z₄]
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      ring

/-- The clean Koopman Hilbert operator used in the BHK development.  This is
kept here rather than importing the older section-level spectral module,
whose import closure already contains the theorem currently being removed. -/
noncomputable def koopmanData (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) : HilbertOperatorData where
  H := MeasureTheory.Lp ℂ 2 M.μ
  normedAddCommGroup := inferInstance
  innerProductSpace := inferInstance
  completeSpace := inferInstance
  U := (MeasureTheory.Lp.compMeasurePreservingₗᵢ
    ℂ M.T hM.2).toContinuousLinearMap

lemma koopmanData_iter_ae
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (n : ℕ) (F : MeasureTheory.Lp ℂ 2 M.μ) :
    ((show MeasureTheory.Lp ℂ 2 M.μ from
        ((koopmanData M hM).U^[n]) F) : M.X → ℂ) =ᵐ[M.μ]
      fun x => (F : M.X → ℂ) ((M.T^[n]) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hcoe := MeasureTheory.Lp.coeFn_compMeasurePreserving
        (((koopmanData M hM).U^[n]) F) hM.2
      have hih := hM.2.quasiMeasurePreserving.ae_eq_comp ih
      filter_upwards [hcoe, hih] with x hx hix
      change (MeasureTheory.Lp.compMeasurePreserving M.T hM.2
        (((koopmanData M hM).U^[n]) F)) x = _
      rw [hx, hix]
      simp only [Function.comp_apply, ← Function.iterate_succ_apply]

/-- Essential boundedness is preserved by every Koopman iterate. -/
lemma koopmanData_iter_memLp_top
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (n : ℕ) (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ) :
    MeasureTheory.MemLp
      (fun x ↦
        (show MeasureTheory.Lp ℂ 2 M.μ from
          ((koopmanData M hM).U^[n]) F) x) ⊤ M.μ := by
  rw [MeasureTheory.memLp_congr_ae
    (koopmanData_iter_ae M hM n F)]
  exact hFtop.comp_measurePreserving (hM.2.iterate n)

/-- A uniform pointwise bound is preserved almost everywhere by every
Koopman iterate. -/
lemma koopmanData_iter_norm_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (n : ℕ) (F : MeasureTheory.Lp ℂ 2 M.μ) (C : ℝ)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C) :
    ∀ᵐ x ∂M.μ,
      ‖(show MeasureTheory.Lp ℂ 2 M.μ from
        ((koopmanData M hM).U^[n]) F) x‖ ≤ C := by
  filter_upwards [koopmanData_iter_ae M hM n F,
    (hM.2.iterate n).quasiMeasurePreserving.ae hFbound] with x hx hbound
  rw [hx]
  exact hbound

/-- Every common Koopman iterate preserves the complex inner product. -/
lemma koopmanData_iter_inner
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (n : ℕ) (F G : MeasureTheory.Lp ℂ 2 M.μ) :
    @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((koopmanData M hM).U^[n]) F)
        (((koopmanData M hM).U^[n]) G) =
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ F G := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      let V : MeasureTheory.Lp ℂ 2 M.μ →ₗᵢ[ℂ]
          MeasureTheory.Lp ℂ 2 M.μ :=
        MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2
      change @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (V (((koopmanData M hM).U^[n]) F))
        (V (((koopmanData M hM).U^[n]) G)) = _
      rw [V.inner_map_map, ih]

lemma koopmanData_apply_toLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MeasureTheory.MemLp f 2 M.μ) :
    (koopmanData M hM).U (hf.toLp f) =
      (hf.comp_measurePreserving hM.2).toLp
        (Chapter01.koopman M.T f) := by
  rfl

lemma eigenfunction_to_eigenvector
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (lam : ℂ) (f : M.X → ℂ) (hf : Eigenfunction M lam f) :
    IsEigenvector (koopmanData M hM) (hf.1.toLp f) := by
  refine ⟨?_, lam, ?_⟩
  · intro hzero
    apply hf.2.1
    filter_upwards [hf.1.coeFn_toLp,
      MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ] with x hx hz
    rw [hzero] at hx
    exact hx.symm.trans hz
  · rw [koopmanData_apply_toLp]
    apply MeasureTheory.Lp.ext
    filter_upwards [
      (hf.1.comp_measurePreserving hM.2).coeFn_toLp,
      MeasureTheory.Lp.coeFn_smul lam (hf.1.toLp f),
      hf.1.coeFn_toLp, hf.2.2] with x hcomp hsmul hcoe heig
    have hcomp' :
        ((hf.1.comp_measurePreserving hM.2).toLp
          (Chapter01.koopman M.T f)) x =
            Chapter01.koopman M.T f x := by
      simpa [Chapter01.koopman, Function.comp_def] using hcomp
    rw [hcomp', hsmul]
    change Chapter01.koopman M.T f x =
      lam * (hf.1.toLp f) x
    rw [hcoe]
    exact heig

lemma eigenvector_to_eigenfunction
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : IsEigenvector (koopmanData M hM) F) :
    ∃ lam : ℂ, Eigenfunction M lam (fun x => F x) := by
  obtain ⟨hF0, lam, hlam⟩ := hF
  refine ⟨lam, MeasureTheory.Lp.memLp F, ?_, ?_⟩
  · intro hzero
    apply hF0
    apply MeasureTheory.Lp.ext
    exact hzero.trans
      (MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ).symm
  · have hcoe :=
      MeasureTheory.Lp.coeFn_compMeasurePreserving F hM.2
    have hsmul := MeasureTheory.Lp.coeFn_smul lam F
    change MeasureTheory.Lp.compMeasurePreserving M.T hM.2 F =
      lam • F at hlam
    have heq :
        (fun x => (MeasureTheory.Lp.compMeasurePreserving
          M.T hM.2 F) x) =ᵐ[M.μ]
          fun x => (lam • F) x := by
      rw [hlam]
    filter_upwards [hcoe, hsmul, heq] with x hcx hsx heq
    rw [hcx, hsx] at heq
    simpa [Chapter01.koopman, Function.comp_def,
      Pi.smul_apply, smul_eq_mul] using heq

/-- In an ergodic system every Koopman eigenvector has an essentially
bounded representative (indeed, one of constant modulus). -/
theorem eigenvector_memLp_top
    (M : System.{u}) (hM : IsErgodic M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : IsEigenvector (koopmanData M hM.1) F) :
    MeasureTheory.MemLp (fun x => F x) ⊤ M.μ := by
  obtain ⟨lam, hlam⟩ :=
    eigenvector_to_eigenfunction M hM.1 F hF
  obtain ⟨_hlamNorm, c, _hcpos, hc⟩ :=
    Section05.eigen_norm_modulus M hM lam (fun x => F x) hlam
  exact MeasureTheory.memLp_top_of_bound
    (MeasureTheory.Lp.memLp F).1 c (by
      filter_upwards [hc] with x hx
      exact hx.le)

/-- Pointwise multiplication of two essentially bounded `L²` vectors. -/
noncomputable def lpPointwiseMul
    {M : System.{u}} (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ) :
    MeasureTheory.Lp ℂ 2 M.μ :=
  ((MeasureTheory.Lp.memLp G).mul hF).toLp
    (fun x => F x * G x)

lemma lpPointwiseMul_coe
    {M : System.{u}} (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ) :
    ((lpPointwiseMul F G hF :
      MeasureTheory.Lp ℂ 2 M.μ) : M.X → ℂ) =ᵐ[M.μ]
        fun x => F x * G x := by
  exact ((MeasureTheory.Lp.memLp G).mul hF).coeFn_toLp

/-- Koopman iteration commutes with bounded pointwise multiplication. -/
lemma koopmanData_iter_lpPointwiseMul
    {M : System.{u}} (hM : Chapter01.IsMeasurePreservingSystem M)
    (n : ℕ) (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x ↦ F x) ⊤ M.μ) :
    ((koopmanData M hM).U^[n]) (lpPointwiseMul F G hFtop) =
      lpPointwiseMul
        (((koopmanData M hM).U^[n]) F)
        (((koopmanData M hM).U^[n]) G)
        (koopmanData_iter_memLp_top M hM n F hFtop) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    koopmanData_iter_ae M hM n (lpPointwiseMul F G hFtop),
    lpPointwiseMul_coe
      (((koopmanData M hM).U^[n]) F)
      (((koopmanData M hM).U^[n]) G)
      (koopmanData_iter_memLp_top M hM n F hFtop),
    (hM.2.iterate n).quasiMeasurePreserving.ae
      (lpPointwiseMul_coe F G hFtop),
    koopmanData_iter_ae M hM n F,
    koopmanData_iter_ae M hM n G] with x hleft hright hprod hF hG
  rw [hleft, hright, hprod, hF, hG]

lemma norm_lpPointwiseMul_le
    {M : System.{u}} (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C) :
    ‖lpPointwiseMul F G hF‖ ≤ C * ‖G‖ := by
  have hpoint : ∀ᵐ x ∂M.μ,
      ‖F x * G x‖ ≤ C * ‖G x‖ := by
    filter_upwards [hbound] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have he := MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    hpoint (2 : ENNReal)
  change ‖((MeasureTheory.Lp.memLp G).mul hF).toLp
    (fun x => F x * G x)‖ ≤ C * ‖G‖
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_def]
  have hrightTop :
      ENNReal.ofReal C *
        MeasureTheory.eLpNorm (fun x => G x) 2 M.μ ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp)
      (MeasureTheory.Lp.memLp G).eLpNorm_ne_top
  calc
    (MeasureTheory.eLpNorm (fun x => F x * G x)
        2 M.μ).toReal ≤
        (ENNReal.ofReal C *
          MeasureTheory.eLpNorm (fun x => G x) 2 M.μ).toReal :=
      ENNReal.toReal_mono hrightTop he
    _ = C * (MeasureTheory.eLpNorm
        (fun x => G x) 2 M.μ).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]

lemma lpPointwiseMul_zero_right
    {M : System.{u}} (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ) :
    lpPointwiseMul F 0 hF = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [lpPointwiseMul_coe F 0 hF,
    MeasureTheory.Lp.coeFn_zero ℂ 2 M.μ] with x hmul hz
  rw [hmul, hz]
  simp

lemma lpPointwiseMul_add_right
    {M : System.{u}} (F G H : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ) :
    lpPointwiseMul F (G + H) hF =
      lpPointwiseMul F G hF + lpPointwiseMul F H hF := by
  apply MeasureTheory.Lp.ext
  filter_upwards [lpPointwiseMul_coe F (G + H) hF,
    lpPointwiseMul_coe F G hF, lpPointwiseMul_coe F H hF,
    MeasureTheory.Lp.coeFn_add G H,
    MeasureTheory.Lp.coeFn_add
      (lpPointwiseMul F G hF) (lpPointwiseMul F H hF)] with
      x hsum hG hH hGH hout
  rw [hsum, hGH, hout]
  simp only [Pi.add_apply]
  rw [hG, hH]
  ring

lemma lpPointwiseMul_sub_right
    {M : System.{u}} (F G H : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ) :
    lpPointwiseMul F (G - H) hF =
      lpPointwiseMul F G hF - lpPointwiseMul F H hF := by
  apply MeasureTheory.Lp.ext
  filter_upwards [lpPointwiseMul_coe F (G - H) hF,
    lpPointwiseMul_coe F G hF, lpPointwiseMul_coe F H hF,
    MeasureTheory.Lp.coeFn_sub G H,
    MeasureTheory.Lp.coeFn_sub
      (lpPointwiseMul F G hF) (lpPointwiseMul F H hF)] with
      x hsub hG hH hGH hout
  rw [hsub, hGH, hout]
  simp only [Pi.sub_apply]
  rw [hG, hH]
  ring

lemma lpPointwiseMul_smul_right
    {M : System.{u}} (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ)
    (c : ℂ) :
    lpPointwiseMul F (c • G) hF =
      c • lpPointwiseMul F G hF := by
  apply MeasureTheory.Lp.ext
  filter_upwards [lpPointwiseMul_coe F (c • G) hF,
    lpPointwiseMul_coe F G hF,
    MeasureTheory.Lp.coeFn_smul c G,
    MeasureTheory.Lp.coeFn_smul c
      (lpPointwiseMul F G hF)] with x hmul hG hcin hcout
  rw [hmul, hcin, hcout]
  simp only [Pi.smul_apply]
  rw [hG]
  change F x * (c * G x) = c * (F x * G x)
  ring

lemma lpPointwiseMul_finset_sum_right
    {M : System.{u}} {ι : Type*}
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ)
    (s : Finset ι) (G : ι → MeasureTheory.Lp ℂ 2 M.μ) :
    lpPointwiseMul F (∑ i ∈ s, G i) hF =
      ∑ i ∈ s, lpPointwiseMul F (G i) hF := by
  induction s using Finset.induction_on with
  | empty => simp [lpPointwiseMul_zero_right]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [lpPointwiseMul_add_right, ih]

/-- Products of eigenfunctions are eigenfunctions in an ergodic
probability-preserving system. -/
theorem eigenfunction_mul
    (M : System.{u}) (hM : IsErgodic M)
    (lam xi : ℂ) (f g : M.X → ℂ)
    (hf : Eigenfunction M lam f) (hg : Eigenfunction M xi g) :
    Eigenfunction M (lam * xi) (fun x => f x * g x) := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  obtain ⟨_hlam, cf, hcfpos, hcf⟩ :=
    Section05.eigen_norm_modulus M hM lam f hf
  obtain ⟨_hxi, cg, hcgpos, hcg⟩ :=
    Section05.eigen_norm_modulus M hM xi g hg
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x => f x * g x) M.μ := hf.1.1.mul hg.1.1
  have hbound : ∀ᵐ x ∂M.μ, ‖f x * g x‖ ≤ cf * cg := by
    filter_upwards [hcf, hcg] with x hfx hgx
    rw [norm_mul, hfx, hgx]
  have htop := MeasureTheory.memLp_top_of_bound
    hmeas (cf * cg) hbound
  refine ⟨htop.mono_exponent (by simp), ?_, ?_⟩
  · intro hzero
    have hz : ∀ᵐ x ∂M.μ, ‖f x * g x‖ = 0 := by
      filter_upwards [hzero] with x hx
      rw [hx]
      simp
    have hp : ∀ᵐ x ∂M.μ, ‖f x * g x‖ = cf * cg := by
      filter_upwards [hcf, hcg] with x hfx hgx
      rw [norm_mul, hfx, hgx]
    obtain ⟨x, hzx, hpx⟩ := (hz.and hp).exists
    rw [hzx] at hpx
    exact (mul_pos hcfpos hcgpos).ne' hpx.symm
  · filter_upwards [hf.2.2, hg.2.2] with x hfx hgx
    change f (M.T x) * g (M.T x) =
      (lam * xi) * (f x * g x)
    change f (M.T x) = lam * f x at hfx
    change g (M.T x) = xi * g x at hgx
    rw [hfx, hgx]
    ring

/-- Pointwise multiplication preserves Koopman eigenvectors in an ergodic
system. -/
theorem lpPointwiseMul_eigenvector
    (M : System.{u}) (hM : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : IsEigenvector (koopmanData M hM.1) F)
    (hG : IsEigenvector (koopmanData M hM.1) G) :
    IsEigenvector (koopmanData M hM.1)
      (lpPointwiseMul F G
        (eigenvector_memLp_top M hM F hF)) := by
  obtain ⟨lam, hlam⟩ :=
    eigenvector_to_eigenfunction M hM.1 F hF
  obtain ⟨xi, hxi⟩ :=
    eigenvector_to_eigenfunction M hM.1 G hG
  let hp := eigenfunction_mul M hM lam xi
    (fun x => F x) (fun x => G x) hlam hxi
  have heig := eigenfunction_to_eigenvector M hM.1
    (lam * xi) (fun x => F x * G x) hp
  have hprod :
      lpPointwiseMul F G
          (eigenvector_memLp_top M hM F hF) =
        hp.1.toLp (fun x => F x * G x) := by
    apply MeasureTheory.Lp.ext
    exact (lpPointwiseMul_coe F G
      (eigenvector_memLp_top M hM F hF)).trans
        hp.1.coeFn_toLp.symm
  rwa [hprod]

/-- A vector which can be approximated arbitrarily well by almost-periodic
vectors is almost periodic for an isometry. -/
theorem almostPeriodic_of_approximable
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ y : D.H, IsAlmostPeriodicVector D y ∧ ‖x - y‖ < ε) :
    IsAlmostPeriodicVector D x := by
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := happrox (ε / 3) (by positivity)
  obtain ⟨F, hF⟩ := hy (ε / 3) (by positivity)
  refine ⟨F, ?_⟩
  intro n
  obtain ⟨z, hzF, hyz⟩ := hF n
  refine ⟨z, hzF, ?_⟩
  calc
    ‖(D.U^[n]) x - z‖ =
        ‖((D.U^[n]) x - (D.U^[n]) y) +
          ((D.U^[n]) y - z)‖ := by
            congr 1
            abel
    _ ≤ ‖(D.U^[n]) x - (D.U^[n]) y‖ +
        ‖(D.U^[n]) y - z‖ := norm_add_le _ _
    _ = ‖x - y‖ + ‖(D.U^[n]) y - z‖ := by
      rw [AlmostPeriodicIsometry.iterate_sub_norm D hU]
    _ < ε / 3 + ε / 3 := add_lt_add hxy hyz
    _ < ε := by linarith

set_option maxHeartbeats 800000 in
/-- Multiplying an almost-periodic vector by a Koopman eigenvector preserves
almost periodicity in an ergodic system. -/
theorem almostPeriodic_mul_eigenvector
    (M : System.{u}) (hM : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : IsAlmostPeriodicVector (koopmanData M hM.1) F)
    (hG : IsEigenvector (koopmanData M hM.1) G) :
    IsAlmostPeriodicVector (koopmanData M hM.1)
      (lpPointwiseMul G F
        (eigenvector_memLp_top M hM G hG)) := by
  let D := koopmanData M hM.1
  have hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X => (MeasureTheory.Lp.compMeasurePreservingₗᵢ
      ℂ M.T hM.1.2).norm_map X
  obtain ⟨xi, hxi⟩ :=
    eigenvector_to_eigenfunction M hM.1 G hG
  obtain ⟨_hxiNorm, C, hCpos, hC⟩ :=
    Section05.eigen_norm_modulus M hM xi
      (fun x => G x) hxi
  let hGtop := eigenvector_memLp_top M hM G hG
  apply almostPeriodic_of_approximable D hU
  intro ε hε
  have hδ : 0 < ε / (C + 1) := by positivity
  obtain ⟨s, hs, c, hFc⟩ :=
    (AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      D hU F hF) (ε / (C + 1)) hδ
  let A : MeasureTheory.Lp ℂ 2 M.μ :=
    ∑ Y ∈ s, c Y • Y
  let P : MeasureTheory.Lp ℂ 2 M.μ :=
    ∑ Y ∈ s, c Y •
      lpPointwiseMul G Y hGtop
  have hP_ap : IsAlmostPeriodicVector D P := by
    change P ∈ AlmostPeriodicIsometry.almostPeriodicSubmodule D
    dsimp only [P]
    apply Submodule.sum_mem
    intro Y hYs
    apply Submodule.smul_mem
    exact AlmostPeriodicIsometry.eigenvector_almostPeriodic
      D hU _ (lpPointwiseMul_eigenvector M hM G Y hG (hs Y hYs))
  refine ⟨P, hP_ap, ?_⟩
  have hPA :
      P = lpPointwiseMul G A hGtop := by
    dsimp only [P, A]
    rw [lpPointwiseMul_finset_sum_right]
    apply Finset.sum_congr rfl
    intro Y hYs
    exact (lpPointwiseMul_smul_right G Y hGtop (c Y)).symm
  rw [hPA]
  have hdiff :
      lpPointwiseMul G F hGtop -
          lpPointwiseMul G A hGtop =
        lpPointwiseMul G (F - A) hGtop := by
    exact (lpPointwiseMul_sub_right G F A hGtop).symm
  rw [hdiff]
  have hbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C := by
    filter_upwards [hC] with x hx
    exact hx.le
  have hnorm := norm_lpPointwiseMul_le G (F - A)
    hGtop C hCpos.le hbound
  have hCratio : C * (ε / (C + 1)) < ε := by
    have hden : 0 < C + 1 := by positivity
    calc
      C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) := by
        gcongr
        linarith
      _ = ε := by field_simp
  calc
    ‖lpPointwiseMul G (F - A) hGtop‖ ≤ C * ‖F - A‖ := hnorm
    _ < C * (ε / (C + 1)) := by
      exact mul_lt_mul_of_pos_left hFc hCpos
    _ < ε := hCratio

/-- Pointwise multiplication in `L²` is commutative whenever either bounded
factor is used to construct the product. -/
lemma lpPointwiseMul_comm
    {M : System.{u}} (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ)
    (hG : MeasureTheory.MemLp (fun x => G x) ⊤ M.μ) :
    lpPointwiseMul F G hF = lpPointwiseMul G F hG := by
  apply MeasureTheory.Lp.ext
  filter_upwards [lpPointwiseMul_coe F G hF,
    lpPointwiseMul_coe G F hG] with x hFG hGF
  rw [hFG, hGF, mul_comm]

/-- A two-factor perturbation estimate for bounded pointwise products.  This
is the Lipschitz input for comparing compact triple correlations with their
zero-time cubic moment. -/
lemma norm_lpPointwiseMul_sub_self_le
    {M : System.{u}}
    (F G H : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x => G x) ⊤ M.μ)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ (1 : ℝ))
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ (1 : ℝ)) :
    ‖lpPointwiseMul F H hFtop -
        lpPointwiseMul G G hGtop‖ ≤
      ‖H - G‖ + ‖F - G‖ := by
  have hdecomp :
      lpPointwiseMul F H hFtop -
          lpPointwiseMul G G hGtop =
        lpPointwiseMul F (H - G) hFtop +
          lpPointwiseMul G (F - G) hGtop := by
    calc
      lpPointwiseMul F H hFtop -
          lpPointwiseMul G G hGtop =
        (lpPointwiseMul F H hFtop -
            lpPointwiseMul F G hFtop) +
          (lpPointwiseMul F G hFtop -
            lpPointwiseMul G G hGtop) := by abel
      _ = lpPointwiseMul F (H - G) hFtop +
          (lpPointwiseMul G F hGtop -
            lpPointwiseMul G G hGtop) := by
        rw [lpPointwiseMul_sub_right F H G hFtop,
          lpPointwiseMul_comm F G hFtop hGtop]
      _ = lpPointwiseMul F (H - G) hFtop +
          lpPointwiseMul G (F - G) hGtop := by
        rw [lpPointwiseMul_sub_right G F G hGtop]
  rw [hdecomp]
  calc
    ‖lpPointwiseMul F (H - G) hFtop +
        lpPointwiseMul G (F - G) hGtop‖ ≤
      ‖lpPointwiseMul F (H - G) hFtop‖ +
        ‖lpPointwiseMul G (F - G) hGtop‖ :=
      norm_add_le _ _
    _ ≤ 1 * ‖H - G‖ + 1 * ‖F - G‖ := by
      exact add_le_add
        (norm_lpPointwiseMul_le F (H - G) hFtop 1
          (by norm_num) hFbound)
        (norm_lpPointwiseMul_le G (F - G) hGtop 1
          (by norm_num) hGbound)
    _ = ‖H - G‖ + ‖F - G‖ := by ring

/-- Corresponding scalar perturbation estimate for the real part of a
triple-product inner product. -/
lemma abs_re_inner_lpPointwiseMul_sub_self_le
    {M : System.{u}}
    (F G H : MeasureTheory.Lp ℂ 2 M.μ)
    (hFtop : MeasureTheory.MemLp (fun x => F x) ⊤ M.μ)
    (hGtop : MeasureTheory.MemLp (fun x => G x) ⊤ M.μ)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ (1 : ℝ))
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ (1 : ℝ)) :
    |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          G (lpPointwiseMul F H hFtop)).re -
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
          G (lpPointwiseMul G G hGtop)).re| ≤
      ‖G‖ * (‖H - G‖ + ‖F - G‖) := by
  let P := lpPointwiseMul F H hFtop
  let Q := lpPointwiseMul G G hGtop
  have hprod : ‖P - Q‖ ≤ ‖H - G‖ + ‖F - G‖ :=
    norm_lpPointwiseMul_sub_self_le F G H hFtop hGtop
      hFbound hGbound
  have hinner :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G P -
          @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G Q =
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G (P - Q) := by
    rw [inner_sub_right]
  calc
    |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G P).re -
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G Q).re| =
      |(@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G P -
        @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G Q).re| := by
          rw [Complex.sub_re]
    _ ≤ ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        G (P - Q)‖ := by
          rw [hinner]
          exact Complex.abs_re_le_norm _
    _ ≤ ‖G‖ * ‖P - Q‖ := norm_inner_le_norm _ _
    _ ≤ ‖G‖ * (‖H - G‖ + ‖F - G‖) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg G)

set_option maxHeartbeats 800000 in
/-- A bounded almost-periodic Koopman vector multiplies every
almost-periodic vector to an almost-periodic vector. -/
theorem almostPeriodic_mul_of_bounded_left
    (M : System.{u}) (hM : IsErgodic M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : IsAlmostPeriodicVector (koopmanData M hM.1) F)
    (hG : IsAlmostPeriodicVector (koopmanData M hM.1) G)
    (hGtop : MeasureTheory.MemLp (fun x => G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ C) :
    IsAlmostPeriodicVector (koopmanData M hM.1)
      (lpPointwiseMul G F hGtop) := by
  let D := koopmanData M hM.1
  have hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X => (MeasureTheory.Lp.compMeasurePreservingₗᵢ
      ℂ M.T hM.1.2).norm_map X
  apply almostPeriodic_of_approximable D hU
  intro ε hε
  have hδ : 0 < ε / (C + 1) := by positivity
  obtain ⟨s, hs, c, hFc⟩ :=
    (AlmostPeriodicIsometry.almostPeriodic_implies_discrete
      D hU F hF) (ε / (C + 1)) hδ
  let A : MeasureTheory.Lp ℂ 2 M.μ :=
    ∑ Y ∈ s, c Y • Y
  let P : MeasureTheory.Lp ℂ 2 M.μ :=
    ∑ Y ∈ s, c Y •
      lpPointwiseMul G Y hGtop
  have hP_ap : IsAlmostPeriodicVector D P := by
    change P ∈ AlmostPeriodicIsometry.almostPeriodicSubmodule D
    dsimp only [P]
    apply Submodule.sum_mem
    intro Y hYs
    apply Submodule.smul_mem
    rw [lpPointwiseMul_comm G Y hGtop
      (eigenvector_memLp_top M hM Y (hs Y hYs))]
    exact almostPeriodic_mul_eigenvector M hM G Y hG (hs Y hYs)
  refine ⟨P, hP_ap, ?_⟩
  have hPA : P = lpPointwiseMul G A hGtop := by
    dsimp only [P, A]
    rw [lpPointwiseMul_finset_sum_right]
    apply Finset.sum_congr rfl
    intro Y hYs
    exact (lpPointwiseMul_smul_right G Y hGtop (c Y)).symm
  rw [hPA]
  have hdiff :
      lpPointwiseMul G F hGtop -
          lpPointwiseMul G A hGtop =
        lpPointwiseMul G (F - A) hGtop :=
    (lpPointwiseMul_sub_right G F A hGtop).symm
  rw [hdiff]
  have hnorm := norm_lpPointwiseMul_le G (F - A)
    hGtop C hC hGbound
  have hCratio : C * (ε / (C + 1)) < ε := by
    have hden : 0 < C + 1 := by positivity
    calc
      C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) := by
        gcongr
        linarith
      _ = ε := by field_simp
  calc
    ‖lpPointwiseMul G (F - A) hGtop‖ ≤ C * ‖F - A‖ := hnorm
    _ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hFc.le hC
    _ < ε := hCratio

/-- Koopman specialization of continuous-spectrum autocorrelation decay. -/
theorem koopman_continuous_autocorrelation_abs_cesaro
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : InContinuousSpectralSubspace
      (koopmanData M hM) F) :
    cesaroTendsTo
      (fun n => ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((koopmanData M hM).U^[n]) F) F‖) 0 := by
  exact IsometryWiener.continuous_autocorrelation_abs_cesaro
    (koopmanData M hM)
    (fun G => (MeasureTheory.Lp.compMeasurePreservingₗᵢ
      ℂ M.T hM.2).norm_map G) F hF

/-- Koopman specialization of the cross-correlation theorem. -/
theorem koopman_continuous_cross_abs_cesaro
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G : MeasureTheory.Lp ℂ 2 M.μ)
    (hF : InContinuousSpectralSubspace (koopmanData M hM) F)
    (hG : InContinuousSpectralSubspace (koopmanData M hM) G) :
    cesaroTendsTo
      (fun n => ‖@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _
        (((koopmanData M hM).U^[n]) F) G‖) 0 := by
  exact continuous_cross_abs_cesaro (koopmanData M hM)
    (fun H => (MeasureTheory.Lp.compMeasurePreservingₗᵢ
      ℂ M.T hM.2).norm_map H) F G hF hG

end Chapter02.MultipleKhintchineKronecker
