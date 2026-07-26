import Exp2BoundedProof

open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter

noncomputable section
namespace Exp2

theorem weakDerivative_zero_ae_eq_traceRhoIntegral {q : ℝ → ℝ}
    (hq : WeakDerivativeOn referenceCell q 0)
    (hqLp : MemLp q 2 (volume.restrict referenceCell)) :
    ∀ᵐ x ∂(volume.restrict referenceCell),
      q x = ∫ y, q y * traceRho y ∂(volume.restrict referenceCell) := by
  let μ := volume.restrict (referenceCell : Set ℝ)
  letI : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_iff]
    simp [μ, referenceCell, cell]
  let ρ := traceRho
  let c : ℝ := ∫ x, q x * ρ x ∂μ
  have hρLp : MemLp ρ 2 μ := by
    exact traceRho_contDiff.continuous.memLp_of_hasCompactSupport
      traceRho_hasCompactSupport
  have hqρ : Integrable (q * ρ) μ := hqLp.integrable_mul hρLp
  have hqInt : Integrable q μ := hqLp.integrable (by norm_num)
  have hzero : ∀ (g : ℝ → ℝ),
      ContDiff ℝ (↑(⊤ : ℕ∞)) g → HasCompactSupport g →
        tsupport g ⊆ (referenceCell : Set ℝ) →
        (∫ x, (g x) • (q x - c) ∂μ) = 0 := by
    intro g hgcd hgc hgs
    let gt : TestFunction referenceCell ℝ ⊤ :=
      { toFun := g
        contDiff' := hgcd
        hasCompactSupport' := hgc
        tsupport_subset' := hgs }
    have hweak := hq (primitiveTestFunction gt)
    have hder : deriv (primitiveTestFunction gt) = zeroMeanPart g := by
      funext x
      change deriv (zeroMeanPrimitive g) x = zeroMeanPart g x
      exact congrFun (zeroMeanPrimitive_deriv hgcd) x
    have hprim : (∫ x, q x * zeroMeanPart g x ∂μ) = 0 := by
      rw [← hder]
      simpa [μ] using hweak
    have hgLp : MemLp g 2 μ :=
      hgcd.continuous.memLp_of_hasCompactSupport hgc
    have hqg : Integrable (q * g) μ := hqLp.integrable_mul hgLp
    let a : ℝ := ∫ y, g y
    have hga : (∫ y, g y ∂μ) = a := by
      calc
        (∫ y, g y ∂μ) = ∫ y, (referenceCell : Set ℝ).indicator g y := by
          simpa [μ] using (integral_indicator (μ := volume) measurableSet_Ioo
            (f := g)).symm
        _ = ∫ y, g y := by
          apply integral_congr_ae
          filter_upwards with y
          by_cases hy : y ∈ (referenceCell : Set ℝ)
          · simp [hy]
          · have hgy : g y = 0 := by
              by_contra hn
              exact hy (hgs (subset_tsupport g hn))
            simp [hy, hgy]
    have hqρa : Integrable (fun x ↦ q x * (a * ρ x)) μ := by
      have h := hqρ.const_mul a
      apply h.congr
      filter_upwards with x
      simp only [Pi.mul_apply]
      ring
    have hzmp : zeroMeanPart g = fun x ↦ g x - a * ρ x := by
      funext x
      simp only [zeroMeanPart, a, ρ]
    have hprim' : (∫ x, q x * g x ∂μ) - a * c = 0 := by
      have hexpand : (∫ x, q x * zeroMeanPart g x ∂μ) =
          (∫ x, q x * g x ∂μ) - ∫ x, q x * (a * ρ x) ∂μ := by
        rw [hzmp]
        simpa only [mul_sub] using integral_sub hqg hqρa
      have hscaled : (∫ x, q x * (a * ρ x) ∂μ) = a * c := by
        rw [show (fun x ↦ q x * (a * ρ x)) = fun x ↦ a * (q x * ρ x) by
          funext x; ring]
        exact integral_const_mul a (fun x ↦ q x * ρ x)
      rw [hexpand, hscaled] at hprim
      exact hprim
    have hgInt : Integrable g μ := hgLp.integrable (by norm_num)
    calc
      (∫ x, (g x) • (q x - c) ∂μ) =
          (∫ x, q x * g x ∂μ) - c * (∫ x, g x ∂μ) := by
            rw [show (fun x ↦ (g x) • (q x - c)) =
                fun x ↦ q x * g x - c * g x by
              funext x
              simp only [smul_eq_mul]
              ring]
            simpa only [Pi.sub_apply, Pi.mul_apply, integral_const_mul] using
              integral_sub hqg (hgInt.const_mul c)
      _ = 0 := by
        rw [hga]
        rw [mul_comm c a]
        exact hprim'
  let q0 : ℝ → ℝ := fun x ↦ q x - c
  have hq0Int : Integrable q0 μ := by
    exact hqInt.sub (integrable_const c)
  have hloc : LocallyIntegrableOn q0 (referenceCell : Set ℝ) μ := by
    exact hq0Int.integrableOn.locallyIntegrableOn
  have hkernel := IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero
    (modelWithCornersSelf ℝ ℝ)
    (by simpa [referenceCell, cell] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1))) hloc (by
      intro g hg hgc hgs
      exact hzero g ((contMDiff_iff_contDiff).mp hg) hgc hgs)
  filter_upwards [hkernel, ae_restrict_mem measurableSet_Ioo] with x hx hxmem
  have hz := hx (by simpa [referenceCell, cell] using hxmem)
  simpa [q0, c, ρ, μ] using sub_eq_zero.mp hz

theorem weakDerivative_zero_ae_constant {q : ℝ → ℝ}
    (hq : WeakDerivativeOn referenceCell q 0)
    (hqLp : MemLp q 2 (volume.restrict referenceCell)) :
    ∃ c : ℝ, ∀ᵐ x ∂(volume.restrict referenceCell), q x = c := by
  exact ⟨∫ y, q y * traceRho y ∂(volume.restrict referenceCell),
    weakDerivative_zero_ae_eq_traceRhoIntegral hq hqLp⟩

def weakPrimitive (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t in (0 : ℝ)..x, g t

lemma integral_restrict_reference_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ x, f x ∂(volume.restrict referenceCell)) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  simp [referenceCell, cell]

theorem weakPrimitive_weakDerivative {g : ℝ → ℝ}
    (hgLp : MemLp g 2 (volume.restrict referenceCell)) :
    WeakDerivativeOn referenceCell (weakPrimitive g) g := by
  let μ := volume.restrict (referenceCell : Set ℝ)
  letI : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_iff]
    simp [μ, referenceCell, cell]
  have hgInt : Integrable g μ := by
    simpa [μ] using hgLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgIoo : IntegrableOn g (Set.Ioo (0 : ℝ) 1) volume := by
    simpa [μ, referenceCell, cell] using hgInt
  have hgInterval : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hgIoo
  have hGac : AbsolutelyContinuousOnInterval (weakPrimitive g) 0 1 := by
    exact hgInterval.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  intro φ
  have hφ0 : φ 0 = 0 := by
    have hnot : (0 : ℝ) ∉ tsupport (φ : ℝ → ℝ) := by
      intro h
      exact (φ.tsupport_subset h).1.false
    by_contra hn
    exact hnot (subset_tsupport (φ : ℝ → ℝ) hn)
  have hφac : AbsolutelyContinuousOnInterval (φ : ℝ → ℝ) 0 1 := by
    have hdcont : Continuous (deriv (φ : ℝ → ℝ)) :=
      φ.contDiff.continuous_deriv (by simp)
    have hdInterval : IntervalIntegrable (deriv (φ : ℝ → ℝ)) volume 0 1 :=
      hdcont.intervalIntegrable 0 1
    have hPac := hdInterval.absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by simp)
    have hφeq : (φ : ℝ → ℝ) = fun x ↦ ∫ t in (0 : ℝ)..x, deriv φ t := by
      funext x
      have hftc := intervalIntegral.integral_deriv_eq_sub
        (f := (φ : ℝ → ℝ))
        (fun y hy ↦ (φ.contDiff.differentiable (by simp)).differentiableAt)
        (hdcont.intervalIntegrable 0 x)
      rw [hftc, hφ0]
      ring
    rw [hφeq]
    exact hPac
  have hφ1 : φ 1 = 0 := by
    have hnot : (1 : ℝ) ∉ tsupport (φ : ℝ → ℝ) := by
      intro h
      have hh : (1 : ℝ) < 1 := by
        simpa [referenceCell, cell] using (φ.tsupport_subset h).2
      exact (lt_irrefl 1) hh
    by_contra hn
    exact hnot (subset_tsupport (φ : ℝ → ℝ) hn)
  have hGderiv : ∀ᵐ x ∂volume, x ∈ Set.Icc (0 : ℝ) 1 →
      deriv (weakPrimitive g) x = g x := by
    filter_upwards [hgInterval.ae_hasDerivAt_integral] with x hx hxi
    exact (hx (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hxi)
      0 (by simp)).deriv
  have hibp := hGac.integral_deriv_mul_eq_sub hφac
  have hderivIntegral :
      (∫ x in (0 : ℝ)..1, deriv (weakPrimitive g) x * φ x) =
        ∫ x in (0 : ℝ)..1, g x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hGderiv] with x hx hxi
    have hxi' : (0 : ℝ) < x ∧ x ≤ 1 := by simpa [Set.uIoc] using hxi
    rw [hx ⟨le_of_lt hxi'.1, hxi'.2⟩]
  have hboundary : weakPrimitive g 1 * φ 1 - weakPrimitive g 0 * φ 0 = 0 := by
    rw [hφ0, hφ1]
    ring
  have hφLp : MemLp (φ : ℝ → ℝ) 2 μ := by
    exact φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hgφInt : Integrable (g * (φ : ℝ → ℝ)) μ := by
    exact hgLp.integrable_mul hφLp
  have hgφIoo : IntegrableOn (fun x ↦ g x * φ x) (Set.Ioo (0 : ℝ) 1) volume := by
    simpa [μ, referenceCell, cell, Pi.mul_apply] using hgφInt
  have hgφInterval : IntervalIntegrable (fun x ↦ g x * φ x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hgφIoo
  have hGφInterval : IntervalIntegrable
      (fun x ↦ weakPrimitive g x * deriv φ x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hGac.continuousOn.mul
      ((φ.contDiff.continuous_deriv (by simp)).continuousOn)
  have hibp_g :
      (∫ x in (0 : ℝ)..1, g x * φ x + weakPrimitive g x * deriv φ x) = 0 := by
    calc
      (∫ x in (0 : ℝ)..1, g x * φ x + weakPrimitive g x * deriv φ x) =
          ∫ x in (0 : ℝ)..1,
            deriv (weakPrimitive g) x * φ x + weakPrimitive g x * deriv φ x := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards [hGderiv] with x hx hxi
              have hxi' : (0 : ℝ) < x ∧ x ≤ 1 := by simpa [Set.uIoc] using hxi
              rw [hx ⟨le_of_lt hxi'.1, hxi'.2⟩]
      _ = 0 := by rw [hibp, hboundary]
  rw [intervalIntegral.integral_add hgφInterval hGφInterval] at hibp_g
  have hleft := integral_restrict_reference_eq_intervalIntegral
    (fun x ↦ weakPrimitive g x * deriv φ x)
  have hright := integral_restrict_reference_eq_intervalIntegral
    (fun x ↦ g x * φ x)
  rw [hleft, hright]
  linarith [hibp_g]

theorem weakPrimitive_absolutelyContinuous {g : ℝ → ℝ}
    (hgLp : MemLp g 2 (volume.restrict referenceCell)) :
    AbsolutelyContinuousOnInterval (weakPrimitive g) 0 1 := by
  let μ := volume.restrict (referenceCell : Set ℝ)
  letI : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_iff]
    simp [μ, referenceCell, cell]
  have hgInt : Integrable g μ := by
    simpa [μ] using hgLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgIoo : IntegrableOn g (Set.Ioo (0 : ℝ) 1) volume := by
    simpa [μ, referenceCell, cell] using hgInt
  have hgInterval : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hgIoo
  exact hgInterval.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)

theorem weakPrimitive_memLp {g : ℝ → ℝ}
    (hgLp : MemLp g 2 (volume.restrict referenceCell)) :
    MemLp (weakPrimitive g) 2 (volume.restrict referenceCell) := by
  have hcont : ContinuousOn (weakPrimitive g) (Set.Icc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (weakPrimitive_absolutelyContinuous hgLp).continuousOn
  have hmeas : AEStronglyMeasurable (weakPrimitive g)
      (volume.restrict referenceCell) := by
    apply hcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      (by simpa [referenceCell, cell] using measurableSet_Ioo)
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt (by simpa using hx.2)⟩
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hIcc : IntegrableOn (fun x : ℝ ↦ ‖weakPrimitive g x‖ ^ 2)
      (Set.Icc 0 1) volume := (hcont.norm.pow 2).integrableOn_Icc
  apply hIcc.mono_set
  intro x hx
  exact ⟨le_of_lt hx.1, le_of_lt (by simpa [referenceCell, cell] using hx.2)⟩

theorem endpoint_representation_of_weakDerivative {f g : ℝ → ℝ}
    (hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hfLp : MemLp f 2 (volume.restrict referenceCell))
    (hgLp : MemLp g 2 (volume.restrict referenceCell))
    (hfg : WeakDerivativeOn referenceCell f g) :
    f 1 = (∫ y, (f y - weakPrimitive g y) * traceRho y
        ∂(volume.restrict referenceCell)) + weakPrimitive g 1 := by
  let G := weakPrimitive g
  have hGLp : MemLp G 2 (volume.restrict referenceCell) := weakPrimitive_memLp hgLp
  have hGweak : WeakDerivativeOn referenceCell G g := weakPrimitive_weakDerivative hgLp
  let q : ℝ → ℝ := fun x ↦ f x - G x
  have hqLp : MemLp q 2 (volume.restrict referenceCell) := by
    simpa [q] using hfLp.sub hGLp
  have hqweak : WeakDerivativeOn referenceCell q 0 := by
    have hneg := WeakDerivativeOn.const_smul (-1) hGweak
    have hadd := WeakDerivativeOn.add_of_memLp hfg hneg hfLp hgLp
      ((hGLp.const_smul (-1))) (hgLp.const_smul (-1))
    simpa [q, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadd
  let c : ℝ := ∫ y, q y * traceRho y ∂(volume.restrict referenceCell)
  have hqae : ∀ᵐ x ∂(volume.restrict referenceCell), q x = c := by
    simpa [c] using weakDerivative_zero_ae_eq_traceRhoIntegral hqweak hqLp
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    simpa [G, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (weakPrimitive_absolutelyContinuous hgLp).continuousOn
  let r : ℝ → ℝ := fun x ↦ c + G x
  have hqae' : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), q x = c := by
    simpa [referenceCell, cell] using hqae
  have hrae : f =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] r := by
    filter_upwards [hqae'] with x hx
    dsimp [q, r] at hx ⊢
    linarith
  have hraeIcc : f =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] r := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc :
      Set.Ioo (0 : ℝ) 1 =ᵐ[volume] Set.Icc 0 1)]
    exact hrae
  have hrcont : ContinuousOn r (Set.Icc (0 : ℝ) 1) := by
    exact continuousOn_const.add hGcont
  have heq := volume.eqOn_Icc_of_ae_eq (by norm_num : (0 : ℝ) ≠ 1)
    hraeIcc hfcont hrcont
  have h1 := heq (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  simpa [r, c, q, G] using h1

end Exp2
