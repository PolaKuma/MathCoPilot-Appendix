import Chapter02.Common
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

open Classical Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Chapter02.HilbertSchmidtConsequences

universe u

theorem integrableKernelRange_of_memLp_two
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (g : M.X → ℂ) (hg : M.lpMember 2 g) :
    IsIntegrableKernelRangeFunction M g := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let H : M.X × M.X → ℂ := fun p ↦ g p.1
  let one : M.X → ℂ := fun _ ↦ 1
  have hg1 : Integrable g M.μ := hg.integrable (by norm_num)
  have hH : Integrable H (M.μ.prod M.μ) := by
    simpa [H] using hg1.comp_fst M.μ
  have hone : Integrable one M.μ := by
    exact integrable_const 1
  refine ⟨H, one, hH, hone, ?_⟩
  filter_upwards [] with x
  simp [kernelAction, H, one]

theorem denseCompactFunctions_imply_dense_integrableKernelRange
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (hdense : HasDenseCompactFunctions M) :
    ∀ f : M.X → ℂ, M.lpMember 2 f → ∀ ε : ℝ, 0 < ε →
      ∃ g : M.X → ℂ, IsIntegrableKernelRangeFunction M g ∧
        eLpNorm (fun x ↦ f x - g x) 2 M.μ < ENNReal.ofReal ε := by
  intro f hf ε hε
  obtain ⟨g, hgAP, hfg⟩ := hdense f hf ε hε
  exact ⟨g, integrableKernelRange_of_memLp_two M hM g hgAP.1, hfg⟩

set_option maxHeartbeats 800000 in
theorem kernelAction_memLp_two
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    M.lpMember 2 (kernelAction M H f) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let G : M.X × M.X → ℂ := fun p ↦ H p * f p.2
  have hfsnd : MemLp (fun p : M.X × M.X ↦ f p.2) 2 (M.μ.prod M.μ) :=
    hf.comp_snd M.μ
  have hG : Integrable G (M.μ.prod M.μ) := by
    simpa [G] using hH.integrable_mul hfsnd
  have hKint : Integrable (kernelAction M H f) M.μ := by
    simpa [kernelAction, G] using hG.integral_prod_left
  refine (memLp_two_iff_integrable_sq_norm hKint.1).2 ?_
  have hHmeas : AEMeasurable
      (fun p : M.X × M.X ↦ ‖H p‖ₑ ^ (2 : ℝ))
      (M.μ.prod M.μ) := hH.1.enorm.pow_const 2
  have hfmeas : AEMeasurable (fun y : M.X ↦ ‖f y‖ₑ) M.μ :=
    hf.1.enorm
  let A : M.X → ℝ≥0∞ := fun x ↦ ∫⁻ y, ‖H (x, y)‖ₑ ^ (2 : ℝ) ∂M.μ
  let B : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂M.μ
  have hBtop : B ≠ ⊤ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ENNReal)) (by norm_num) (by norm_num) hf.2).ne
  have hpoint : ∀ᵐ x ∂M.μ,
      ‖kernelAction M H f x‖ₑ ^ (2 : ℝ) ≤ A x * B := by
    filter_upwards [hH.1.prodMk_left] with x hxmeas
    have hfirst :
        ‖kernelAction M H f x‖ₑ ≤
          ∫⁻ y, ‖H (x, y)‖ₑ * ‖f y‖ₑ ∂M.μ := by
      apply (enorm_integral_le_lintegral_enorm _).trans_eq
      apply lintegral_congr
      intro y
      simp
    have hholder :
        (∫⁻ y, ‖H (x, y)‖ₑ * ‖f y‖ₑ ∂M.μ) ≤
          A x ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
      simpa [A, B] using
        ENNReal.lintegral_mul_le_Lp_mul_Lq M.μ Real.HolderConjugate.two_two
          hxmeas.enorm hfmeas
    have hsquare := ENNReal.rpow_le_rpow (hfirst.trans hholder) (by norm_num : (0 : ℝ) ≤ 2)
    calc
      ‖kernelAction M H f x‖ₑ ^ (2 : ℝ)
          ≤ (A x ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) :=
        hsquare
      _ = A x * B := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
  have hAtop : (∫⁻ x, A x ∂M.μ) ≠ ⊤ := by
    have hprod :
        (∫⁻ p, ‖H p‖ₑ ^ (2 : ℝ) ∂(M.μ.prod M.μ)) ≠ ⊤ :=
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ENNReal)) (by norm_num) (by norm_num) hH.2).ne
    rw [lintegral_prod _ hHmeas] at hprod
    exact hprod
  have hlin :
      (∫⁻ x, ‖kernelAction M H f x‖ₑ ^ (2 : ℝ) ∂M.μ) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono_ae hpoint)
    rw [lintegral_mul_const' B A hBtop]
    exact ENNReal.mul_lt_top hAtop.lt_top hBtop.lt_top
  have hnormsq : (fun x ↦ ‖kernelAction M H f x‖ ^ (2 : ℕ)) =
      fun x ↦ ENNReal.toReal (‖kernelAction M H f x‖ₑ ^ (2 : ℝ)) := by
    funext x
    simp
  rw [hnormsq]
  exact integrable_toReal_of_lintegral_ne_top
    (hKint.1.enorm.pow_const 2) hlin.ne

set_option maxHeartbeats 800000 in
theorem kernelAction_lintegral_sq_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    (∫⁻ x, ‖kernelAction M H f x‖ₑ ^ (2 : ℝ) ∂M.μ) ≤
      (∫⁻ p, ‖H p‖ₑ ^ (2 : ℝ) ∂(M.μ.prod M.μ)) *
        (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂M.μ) := by
  letI : IsProbabilityMeasure M.μ := hM.1
  let A : M.X → ℝ≥0∞ := fun x ↦ ∫⁻ y, ‖H (x, y)‖ₑ ^ (2 : ℝ) ∂M.μ
  let B : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂M.μ
  have hBtop : B ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ENNReal)) (by norm_num) (by norm_num) hf.2).ne
  have hpoint : ∀ᵐ x ∂M.μ,
      ‖kernelAction M H f x‖ₑ ^ (2 : ℝ) ≤ A x * B := by
    filter_upwards [hH.1.prodMk_left] with x hxmeas
    have hfirst :
        ‖kernelAction M H f x‖ₑ ≤
          ∫⁻ y, ‖H (x, y)‖ₑ * ‖f y‖ₑ ∂M.μ := by
      apply (enorm_integral_le_lintegral_enorm _).trans_eq
      exact lintegral_congr fun y ↦ by simp
    have hholder :
        (∫⁻ y, ‖H (x, y)‖ₑ * ‖f y‖ₑ ∂M.μ) ≤
          A x ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2) := by
      simpa [A, B] using
        ENNReal.lintegral_mul_le_Lp_mul_Lq M.μ Real.HolderConjugate.two_two
          hxmeas.enorm hf.1.enorm
    have hsquare :=
      ENNReal.rpow_le_rpow (hfirst.trans hholder) (by norm_num : (0 : ℝ) ≤ 2)
    calc
      ‖kernelAction M H f x‖ₑ ^ (2 : ℝ)
          ≤ (A x ^ ((1 : ℝ) / 2) * B ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) :=
        hsquare
      _ = A x * B := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
  calc
    (∫⁻ x, ‖kernelAction M H f x‖ₑ ^ (2 : ℝ) ∂M.μ)
        ≤ ∫⁻ x, A x * B ∂M.μ := lintegral_mono_ae hpoint
    _ = (∫⁻ x, A x ∂M.μ) * B := lintegral_mul_const' B A hBtop
    _ = (∫⁻ p, ‖H p‖ₑ ^ (2 : ℝ) ∂(M.μ.prod M.μ)) * B := by
      rw [lintegral_prod _ (hH.1.enorm.pow_const 2)]
    _ = _ := rfl

theorem kernelAction_eLpNorm_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    eLpNorm (kernelAction M H f) 2 M.μ ≤
      eLpNorm H 2 (M.μ.prod M.μ) * eLpNorm f 2 M.μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc
    (∫⁻ x, ‖kernelAction M H f x‖ₑ ^ (2 : ℝ) ∂M.μ) ^ (1 / (2 : ℝ))
        ≤ ((∫⁻ p, ‖H p‖ₑ ^ (2 : ℝ) ∂(M.μ.prod M.μ)) *
            (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂M.μ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow
        (kernelAction_lintegral_sq_le M hM H hH f hf) (by positivity)
    _ = (∫⁻ p, ‖H p‖ₑ ^ (2 : ℝ) ∂(M.μ.prod M.μ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂M.μ) ^ (1 / (2 : ℝ)) := by
      exact ENNReal.mul_rpow_of_nonneg _ _ (by positivity)

theorem kernelAction_congr_ae
    (M : System.{u}) (H : M.X × M.X → ℂ)
    {f g : M.X → ℂ} (hfg : f =ᵐ[M.μ] g) :
    kernelAction M H f = kernelAction M H g := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  simp only [hy]

theorem kernelAction_add_ae
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (f g : M.X → ℂ) (hf : M.lpMember 2 f) (hg : M.lpMember 2 g) :
    kernelAction M H (fun y ↦ f y + g y) =ᵐ[M.μ]
      fun x ↦ kernelAction M H f x + kernelAction M H g x := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hfprod : Integrable (fun p : M.X × M.X ↦ H p * f p.2)
      (M.μ.prod M.μ) :=
    hH.integrable_mul (hf.comp_snd M.μ)
  have hgprod : Integrable (fun p : M.X × M.X ↦ H p * g p.2)
      (M.μ.prod M.μ) :=
    hH.integrable_mul (hg.comp_snd M.μ)
  filter_upwards [hfprod.prod_right_ae, hgprod.prod_right_ae] with x hfx hgx
  simpa only [kernelAction, mul_add] using (integral_add hfx hgx)

theorem kernelAction_smul
    (M : System.{u}) (H : M.X × M.X → ℂ)
    (c : ℂ) (f : M.X → ℂ) :
    kernelAction M H (fun y ↦ c * f y) =
      fun x ↦ c * kernelAction M H f x := by
  funext x
  rw [kernelAction, kernelAction, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

noncomputable def kernelLinearMap
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ)) :
    Lp ℂ 2 M.μ →ₗ[ℂ] Lp ℂ 2 M.μ where
  toFun F :=
    (kernelAction_memLp_two M hM H hH F (Lp.memLp F)).toLp
      (kernelAction M H F)
  map_add' F G := by
    apply Lp.ext (μ := M.μ)
    let hFG := kernelAction_memLp_two M hM H hH
      (fun x ↦ (F + G) x) (Lp.memLp (F + G))
    let hF := kernelAction_memLp_two M hM H hH F (Lp.memLp F)
    let hG := kernelAction_memLp_two M hM H hH G (Lp.memLp G)
    have hadd := kernelAction_add_ae M hM H hH F G (Lp.memLp F) (Lp.memLp G)
    filter_upwards [hFG.coeFn_toLp, hF.coeFn_toLp, hG.coeFn_toLp,
      Lp.coeFn_add F G, Lp.coeFn_add
        (hF.toLp (kernelAction M H F)) (hG.toLp (kernelAction M H G)),
      hadd] with x hFGx hFx hGx hinput houtput haddx
    rw [hFGx, houtput]
    simp only [Pi.add_apply]
    rw [hFx, hGx]
    have hcongr := congrFun
      (kernelAction_congr_ae M H (Lp.coeFn_add F G)) x
    rw [hcongr]
    exact haddx
  map_smul' c F := by
    apply Lp.ext (μ := M.μ)
    let hcF := kernelAction_memLp_two M hM H hH
      (fun x ↦ (c • F) x) (Lp.memLp (c • F))
    let hF := kernelAction_memLp_two M hM H hH F (Lp.memLp F)
    have hsmul := congrFun (kernelAction_smul M H c F)
    filter_upwards [hcF.coeFn_toLp, hF.coeFn_toLp, Lp.coeFn_smul c F,
      Lp.coeFn_smul c (hF.toLp (kernelAction M H F))] with x hcFx hFx hinput houtput
    rw [hcFx]
    simp only [RingHom.id_apply]
    rw [houtput]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hFx]
    have hcongr := congrFun
      (kernelAction_congr_ae M H (Lp.coeFn_smul c F)) x
    rw [hcongr]
    exact hsmul x

theorem kernelLinearMap_norm_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (F : Lp ℂ 2 M.μ) :
    ‖kernelLinearMap M hM H hH F‖ ≤
      (eLpNorm H 2 (M.μ.prod M.μ)).toReal * ‖F‖ := by
  let hKF := kernelAction_memLp_two M hM H hH F (Lp.memLp F)
  change ‖hKF.toLp (kernelAction M H F)‖ ≤
    (eLpNorm H 2 (M.μ.prod M.μ)).toReal * ‖F‖
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  apply (ENNReal.toReal_le_toReal hKF.2.ne
    (ENNReal.mul_ne_top hH.2.ne (Lp.eLpNorm_ne_top F))).2
  exact kernelAction_eLpNorm_le M hM H hH F (Lp.memLp F)

noncomputable def kernelOperator
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ)) :
    Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ :=
  (kernelLinearMap M hM H hH).mkContinuous
    (eLpNorm H 2 (M.μ.prod M.μ)).toReal
    (kernelLinearMap_norm_le M hM H hH)

@[simp]
theorem kernelOperator_apply
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ))
    (F : Lp ℂ 2 M.μ) :
    kernelOperator M hM H hH F = kernelLinearMap M hM H hH F := by
  exact LinearMap.mkContinuous_apply _ _ _ _

theorem kernelAction_kernel_sub_ae
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H G : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ)) (hG : MemLp G 2 (M.μ.prod M.μ))
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    kernelAction M (fun p ↦ H p - G p) f =ᵐ[M.μ]
      fun x ↦ kernelAction M H f x - kernelAction M G f x := by
  letI : IsProbabilityMeasure M.μ := hM.1
  have hHprod : Integrable (fun p : M.X × M.X ↦ H p * f p.2)
      (M.μ.prod M.μ) :=
    hH.integrable_mul (hf.comp_snd M.μ)
  have hGprod : Integrable (fun p : M.X × M.X ↦ G p * f p.2)
      (M.μ.prod M.μ) :=
    hG.integrable_mul (hf.comp_snd M.μ)
  filter_upwards [hHprod.prod_right_ae, hGprod.prod_right_ae] with x hHx hGx
  simpa only [kernelAction, sub_mul] using (integral_sub hHx hGx)

theorem kernelOperator_sub
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H G : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ)) (hG : MemLp G 2 (M.μ.prod M.μ)) :
    kernelOperator M hM H hH - kernelOperator M hM G hG =
      kernelOperator M hM (fun p ↦ H p - G p) (hH.sub hG) := by
  ext F
  rw [ContinuousLinearMap.sub_apply, kernelOperator_apply, kernelOperator_apply,
    kernelOperator_apply]
  let hHF := kernelAction_memLp_two M hM H hH F (Lp.memLp F)
  let hGF := kernelAction_memLp_two M hM G hG F (Lp.memLp F)
  let hsubF := kernelAction_memLp_two M hM (fun p ↦ H p - G p)
    (hH.sub hG) F (Lp.memLp F)
  have haction :=
    kernelAction_kernel_sub_ae M hM H G hH hG F (Lp.memLp F)
  simp only [kernelLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  filter_upwards [hHF.coeFn_toLp, hGF.coeFn_toLp, hsubF.coeFn_toLp,
    Lp.coeFn_sub (hHF.toLp (kernelAction M H F))
      (hGF.toLp (kernelAction M G F)), haction] with
      x hHFx hGFx hsubx hout hactx
  rw [hout]
  simp only [Pi.sub_apply]
  rw [hHFx, hGFx, hsubx]
  exact hactx.symm

theorem kernelOperator_norm_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H : M.X × M.X → ℂ) (hH : MemLp H 2 (M.μ.prod M.μ)) :
    ‖kernelOperator M hM H hH‖ ≤
      (eLpNorm H 2 (M.μ.prod M.μ)).toReal := by
  exact LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg
    (kernelLinearMap_norm_le M hM H hH)

theorem kernelOperator_sub_norm_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (H G : M.X × M.X → ℂ)
    (hH : MemLp H 2 (M.μ.prod M.μ)) (hG : MemLp G 2 (M.μ.prod M.μ)) :
    ‖kernelOperator M hM H hH - kernelOperator M hM G hG‖ ≤
      (eLpNorm (fun p ↦ H p - G p) 2 (M.μ.prod M.μ)).toReal := by
  rw [kernelOperator_sub M hM H G hH hG]
  exact kernelOperator_norm_le M hM (fun p ↦ H p - G p) (hH.sub hG)

def IsFiniteSeparatedKernel (M : System.{u}) (G : M.X × M.X → ℂ) : Prop :=
  ∃ n : ℕ, ∃ a b : Fin n → M.X → ℂ,
    (∀ i, M.lpMember 2 (a i)) ∧
    (∀ i, M.lpMember 2 (b i)) ∧
    G = fun p ↦ ∑ i, a i p.1 * b i p.2

theorem finiteSeparatedKernel_action_eq
    (M : System.{u}) (G : M.X × M.X → ℂ)
    (n : ℕ) (a b : Fin n → M.X → ℂ)
    (hb : ∀ i, M.lpMember 2 (b i))
    (hG : G = fun p ↦ ∑ i, a i p.1 * b i p.2)
    (F : Lp ℂ 2 M.μ) :
    ∀ x, kernelAction M G F x =
      ∑ i, a i x * ∫ y, b i y * F y ∂M.μ := by
  rw [hG]
  intro x
  simp only [kernelAction]
  rw [show (fun y ↦ (∑ i, a i x * b i y) * F y) =
      fun y ↦ ∑ i, a i x * (b i y * F y) by
    funext y
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [integral_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← integral_const_mul]
  · intro i hi
    simpa only [mul_assoc] using
      ((hb i).integrable_mul (Lp.memLp F)).const_mul (a i x)

theorem finiteSeparatedKernel_operator_finite_range
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (G : M.X × M.X → ℂ) (hGLp : MemLp G 2 (M.μ.prod M.μ))
    (hG : IsFiniteSeparatedKernel M G) :
    ∃ s : Finset (Lp ℂ 2 M.μ),
      ∀ F, kernelOperator M hM G hGLp F ∈ Submodule.span ℂ (s : Set (Lp ℂ 2 M.μ)) := by
  obtain ⟨n, a, b, ha, hb, hform⟩ := hG
  let v : Fin n → Lp ℂ 2 M.μ := fun i ↦ (ha i).toLp (a i)
  let s : Finset (Lp ℂ 2 M.μ) := Finset.univ.image v
  refine ⟨s, ?_⟩
  intro F
  let coeff : Fin n → ℂ := fun i ↦ ∫ y, b i y * F y ∂M.μ
  have hsumMem :
      (∑ i, coeff i • (ha i).toLp (a i)) ∈
        Submodule.span ℂ (s : Set (Lp ℂ 2 M.μ)) := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    change v i ∈ Finset.univ.image v
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  suffices kernelOperator M hM G hGLp F =
      ∑ i, coeff i • (ha i).toLp (a i) by
    rwa [this]
  apply Lp.ext (μ := M.μ)
  let hKF := kernelAction_memLp_two M hM G hGLp F (Lp.memLp F)
  have hrawEq := finiteSeparatedKernel_action_eq M G n a b hb hform F
  have hsumcoe (u : Finset (Fin n)) : ∀ᵐ x ∂M.μ,
      (((∑ i ∈ u, coeff i • (ha i).toLp (a i) :
        Lp ℂ 2 M.μ) : M.X → ℂ) x) =
        ∑ i ∈ u, coeff i * a i x := by
    induction u using Finset.induction_on with
    | empty => exact Lp.coeFn_zero ℂ 2 M.μ
    | @insert i u hiu ih =>
        filter_upwards [
          Lp.coeFn_add (coeff i • (ha i).toLp (a i))
            (∑ j ∈ u, coeff j • (ha j).toLp (a j)),
          Lp.coeFn_smul (coeff i) ((ha i).toLp (a i)),
          (ha i).coeFn_toLp, ih] with x hadd hsmul hcoe htail
        rw [Finset.sum_insert hiu, Finset.sum_insert hiu, hadd]
        simp only [Pi.add_apply]
        rw [hsmul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hcoe, htail]
  simp only [kernelOperator_apply, kernelLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  filter_upwards [hKF.coeFn_toLp, hsumcoe Finset.univ] with x hKx hsumx
  rw [hKx]
  rw [hrawEq x]
  simp only [coeff]
  rw [hsumx]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def HasCompactClosedBallImage {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (K : E → F) : Prop :=
  ∀ r : ℝ, ∃ C : Set F, IsCompact C ∧
    K '' Metric.closedBall 0 r ⊆ C

theorem hasCompactClosedBallImage_of_finite_span_range
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K : E →L[ℂ] F) (s : Finset F)
    (hrange : ∀ x, K x ∈ Submodule.span ℂ (s : Set F)) :
    HasCompactClosedBallImage K := by
  let S : Submodule ℂ F := Submodule.span ℂ (s : Set F)
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  intro r
  let C : Set F :=
    (S.subtypeL '' Metric.closedBall (0 : S) (‖K‖ * max r 0))
  refine ⟨C, ?_, ?_⟩
  · exact (isCompact_closedBall (0 : S) (‖K‖ * max r 0)).image
      S.subtypeL.continuous
  · rintro y ⟨x, hx, rfl⟩
    have hxr : ‖x‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hr0 : 0 ≤ r := (norm_nonneg x).trans hxr
    let z : S := ⟨K x, hrange x⟩
    refine ⟨z, ?_, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right, z]
    calc
      ‖K x‖ ≤ ‖K‖ * ‖x‖ := K.le_opNorm x
      _ ≤ ‖K‖ * r := mul_le_mul_of_nonneg_left hxr (norm_nonneg K)
      _ = ‖K‖ * max r 0 := by rw [max_eq_left hr0]

theorem hasCompactClosedBallImage_of_finite_span_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (K : E →L[ℂ] F)
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ L : E →L[ℂ] F, ∃ s : Finset F,
        (∀ x, L x ∈ Submodule.span ℂ (s : Set F)) ∧ ‖K - L‖ < δ) :
    HasCompactClosedBallImage K := by
  intro r
  by_cases hr : 0 < r
  · let B : Set F := K '' Metric.closedBall 0 r
    have hBtot : TotallyBounded B := by
      rw [Metric.totallyBounded_iff]
      intro ε hε
      obtain ⟨L, s, hsrange, hKL⟩ := happrox (ε / (2 * r)) (by positivity)
      obtain ⟨D, hDcompact, hLD⟩ :=
        hasCompactClosedBallImage_of_finite_span_range L s hsrange r
      obtain ⟨t, htfin, htcover⟩ :=
        Metric.totallyBounded_iff.mp hDcompact.totallyBounded (ε / 2) (by positivity)
      refine ⟨t, htfin, ?_⟩
      rintro z ⟨x, hx, rfl⟩
      have hLxD : L x ∈ D := hLD ⟨x, hx, rfl⟩
      obtain ⟨y, hyt, hLxy⟩ := by
        simpa only [Set.mem_iUnion, Metric.mem_ball] using htcover hLxD
      simp only [Set.mem_iUnion, Metric.mem_ball]
      refine ⟨y, hyt, ?_⟩
      have hxr : ‖x‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hdiff :
          ‖(K - L) x‖ < ε / 2 := by
        calc
          ‖(K - L) x‖ ≤ ‖K - L‖ * ‖x‖ := (K - L).le_opNorm x
          _ ≤ ‖K - L‖ * r :=
            mul_le_mul_of_nonneg_left hxr (norm_nonneg (K - L))
          _ < (ε / (2 * r)) * r :=
            mul_lt_mul_of_pos_right hKL hr
          _ = ε / 2 := by field_simp
      calc
        dist (K x) y ≤ dist (K x) (L x) + dist (L x) y := dist_triangle _ _ _
        _ = ‖(K - L) x‖ + dist (L x) y := by
          congr 1
          simp [dist_eq_norm]
        _ < ε / 2 + ε / 2 := add_lt_add hdiff hLxy
        _ = ε := by ring
    refine ⟨closure B, ?_, subset_closure⟩
    exact isCompact_iff_totallyBounded_isComplete.2
      ⟨hBtot.closure, isClosed_closure.isComplete⟩
  · have hr0 : r ≤ 0 := le_of_not_gt hr
    refine ⟨{0}, isCompact_singleton, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have hx0 : x = 0 := by
      have hnorm : ‖x‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      exact norm_eq_zero.mp ((norm_nonneg x).antisymm (hnorm.trans hr0)).symm
    simp [hx0]

end Chapter02.HilbertSchmidtConsequences
