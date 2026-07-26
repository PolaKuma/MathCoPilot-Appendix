import Exp2NormProbe
open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter
noncomputable section
namespace Exp2

lemma memLp_const_one_reference :
    MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict referenceCell) := by
  let μ := volume.restrict (referenceCell : Set ℝ)
  letI : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_iff]
    simp [μ, referenceCell, cell]
  simpa [μ] using (memLp_const (μ := μ) 1)

lemma l2NormOn_const_one_reference :
    l2NormOn referenceCell (fun _ : ℝ => (1 : ℝ)) = 1 := by
  rw [l2NormOn_eq_sqrt_integral_sq memLp_const_one_reference]
  simp [referenceCell, cell, MeasureTheory.Measure.real]

lemma weakPrimitive_endpoint_bound {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    |weakPrimitive g 1| ≤ l2NormOn referenceCell g := by
  rw [weakPrimitive]
  have h := abs_integral_mul_le_l2NormOn hg memLp_const_one_reference
  rw [← integral_restrict_reference_eq_intervalIntegral]
  simpa [Pi.mul_apply, l2NormOn_const_one_reference] using h

lemma endpoint_trace_bound_with_primitive {f g : ℝ → ℝ}
    (hfcont : ContinuousOn f (Set.Icc 0 1))
    (hf : MemLp f 2 (volume.restrict referenceCell))
    (hg : MemLp g 2 (volume.restrict referenceCell))
    (hfg : WeakDerivativeOn referenceCell f g) :
    |f 1| ≤
      (l2NormOn referenceCell f + l2NormOn referenceCell (weakPrimitive g)) *
          l2NormOn referenceCell traceRho +
        l2NormOn referenceCell g := by
  let G := weakPrimitive g
  let q : ℝ → ℝ := fun x ↦ f x - G x
  let c : ℝ := ∫ y, q y * traceRho y ∂(volume.restrict referenceCell)
  have hG : MemLp G 2 (volume.restrict referenceCell) := by
    simpa [G] using weakPrimitive_memLp hg
  have hq : MemLp q 2 (volume.restrict referenceCell) := by
    simpa [q, G, sub_eq_add_neg] using hf.add hG.neg
  have hρ : MemLp traceRho 2 (volume.restrict referenceCell) :=
    traceRho_contDiff.continuous.memLp_of_hasCompactSupport traceRho_hasCompactSupport
  have hc : |c| ≤ l2NormOn referenceCell q * l2NormOn referenceCell traceRho := by
    simpa [c] using abs_integral_mul_le_l2NormOn hq hρ
  have hqnorm : l2NormOn referenceCell q ≤
      l2NormOn referenceCell f + l2NormOn referenceCell G := by
    have hadd := l2NormOn_add_le hf hG.neg
    simpa [q, sub_eq_add_neg, l2NormOn_neg] using hadd
  have hrep := endpoint_representation_of_weakDerivative hfcont hf hg hfg
  have hrep' : f 1 = c + G 1 := by
    simpa [c, q, G] using hrep
  rw [hrep']
  calc
    |c + G 1| ≤ |c| + |G 1| := abs_add_le _ _
    _ ≤ (l2NormOn referenceCell f + l2NormOn referenceCell G) *
          l2NormOn referenceCell traceRho + l2NormOn referenceCell g := by
      have hρnonneg := l2NormOn_nonneg referenceCell traceRho
      have hc' : |c| ≤
          (l2NormOn referenceCell f + l2NormOn referenceCell G) *
            l2NormOn referenceCell traceRho :=
        hc.trans (mul_le_mul_of_nonneg_right hqnorm hρnonneg)
      exact add_le_add hc' (by simpa [G] using weakPrimitive_endpoint_bound hg)
    _ = _ := by rfl

lemma abs_weakPrimitive_le_l2NormOn {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict referenceCell)) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |weakPrimitive g x| ≤ l2NormOn referenceCell g := by
  let μ := volume.restrict (referenceCell : Set ℝ)
  letI : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_iff]
    simp [μ, referenceCell, cell]
  have hgInt : Integrable g (volume.restrict referenceCell) :=
    hg.integrable (by norm_num)
  have hgIoo : IntegrableOn g (Set.Ioo (0 : ℝ) 1) volume := by
    simpa [referenceCell, cell] using hgInt
  have hgInterval : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hgIoo
  have habsInterval : IntervalIntegrable (fun t ↦ |g t|) volume 0 1 := by
    simpa [Real.norm_eq_abs] using hgInterval.norm
  have habsLp : MemLp (fun t ↦ |g t|) 2 (volume.restrict referenceCell) := by
    simpa [Real.norm_eq_abs] using hg.norm
  have hl1raw := abs_integral_mul_le_l2NormOn habsLp memLp_const_one_reference
  have hl1nonneg : 0 ≤ ∫ t, |g t| ∂(volume.restrict referenceCell) :=
    integral_nonneg fun _ ↦ abs_nonneg _
  have hl1 : (∫ t in (0 : ℝ)..1, |g t|) ≤ l2NormOn referenceCell g := by
    rw [← integral_restrict_reference_eq_intervalIntegral]
    simpa [abs_of_nonneg hl1nonneg, l2NormOn_const_one_reference,
      l2NormOn_abs referenceCell hg.aestronglyMeasurable] using hl1raw
  rw [weakPrimitive]
  calc
    |∫ t in (0 : ℝ)..x, g t| ≤ ∫ t in (0 : ℝ)..x, |g t| :=
      intervalIntegral.abs_integral_le_integral_abs hx.1
    _ ≤ ∫ t in (0 : ℝ)..1, |g t| := by
      exact intervalIntegral.integral_mono_interval (le_refl 0) hx.1 hx.2
        (ae_of_all _ fun _ ↦ abs_nonneg _) habsInterval
    _ ≤ l2NormOn referenceCell g := hl1

lemma weakPrimitive_l2NormOn_le {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    l2NormOn referenceCell (weakPrimitive g) ≤ l2NormOn referenceCell g := by
  let μ := volume.restrict (referenceCell : Set ℝ)
  letI : IsFiniteMeasure μ := by
    rw [isFiniteMeasure_iff]
    simp [μ, referenceCell, cell]
  have hG := weakPrimitive_memLp hg
  rw [l2NormOn_eq_sqrt_integral_sq hG]
  let L := l2NormOn referenceCell g
  let S := ∫ x, ‖weakPrimitive g x‖ ^ 2 ∂μ
  have hGsq : Integrable (fun x ↦ ‖weakPrimitive g x‖ ^ 2) μ := by
    exact (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG
  have hconst : Integrable (fun _ : ℝ ↦ L ^ 2) μ := integrable_const (L ^ 2)
  have hLnonneg : 0 ≤ L := l2NormOn_nonneg referenceCell g
  have hpoint : ∀ᵐ x ∂μ, ‖weakPrimitive g x‖ ^ 2 ≤ L ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := by simpa [referenceCell, cell] using hx.1
    have hx1 : x < (1 : ℝ) := by simpa [referenceCell, cell] using hx.2
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx0, le_of_lt hx1⟩
    have h := abs_weakPrimitive_le_l2NormOn hg hx'
    have hn : ‖weakPrimitive g x‖ ≤ L := by
      simpa [Real.norm_eq_abs, L] using h
    nlinarith [norm_nonneg (weakPrimitive g x)]
  have hSint : S ≤ ∫ _x : ℝ, L ^ 2 ∂μ := by
    exact integral_mono_ae hGsq hconst hpoint
  have hμ : μ.real Set.univ = 1 := by
    simp [μ, referenceCell, cell, MeasureTheory.Measure.real]
  have hconstEval : (∫ _x : ℝ, L ^ 2 ∂μ) = L ^ 2 := by
    simp [hμ]
  have hSle : S ≤ L ^ 2 := by simpa [hconstEval] using hSint
  have hSnonneg : 0 ≤ S := integral_nonneg fun _ ↦ sq_nonneg _
  have hsqrt := Real.sq_sqrt hSnonneg
  change Real.sqrt S ≤ L
  nlinarith

lemma endpoint_trace_bound {f g : ℝ → ℝ}
    (hfcont : ContinuousOn f (Set.Icc 0 1))
    (hf : MemLp f 2 (volume.restrict referenceCell))
    (hg : MemLp g 2 (volume.restrict referenceCell))
    (hfg : WeakDerivativeOn referenceCell f g) :
    |f 1| ≤
      (l2NormOn referenceCell f + l2NormOn referenceCell g) *
          l2NormOn referenceCell traceRho +
        l2NormOn referenceCell g := by
  have h := endpoint_trace_bound_with_primitive hfcont hf hg hfg
  have hG := weakPrimitive_l2NormOn_le hg
  have hρ := l2NormOn_nonneg referenceCell traceRho
  have hsum : l2NormOn referenceCell f +
      l2NormOn referenceCell (weakPrimitive g) ≤
      l2NormOn referenceCell f + l2NormOn referenceCell g :=
    add_le_add (le_refl _) hG
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hsum hρ) (le_refl _))

lemma SobolevMapOn.abs_eval_one_le_sobolevNorm {n : ℕ}
    (w : SobolevMapOn (n + 1) referenceCell) :
    |w 1| ≤ (2 * l2NormOn referenceCell traceRho + 1) * sobolevNorm w := by
  have hfcont : ContinuousOn w.toFun (Set.Icc 0 1) := by
    simpa [referenceCell, cell] using w.continuousOn
  have hf := w.toFun_memLp
  have hg := w.memLp_derivative 1 (by omega)
  have hfg : WeakDerivativeOn referenceCell w.toFun (w.derivative 1) := by
    have h := w.weakDerivative_succ 0 (by omega)
    simpa [w.derivative_zero] using h
  have htrace := endpoint_trace_bound hfcont hf hg hfg
  have h0 : l2NormOn referenceCell w.toFun ≤ sobolevNorm w := by
    have h := l2NormOn_derivative_le_sobolevNorm w (j := 0) (Nat.zero_le _)
    simpa [w.derivative_zero] using h
  have h1 : l2NormOn referenceCell (w.derivative 1) ≤ sobolevNorm w :=
    l2NormOn_derivative_le_sobolevNorm w (by omega)
  have hρ := l2NormOn_nonneg referenceCell traceRho
  calc
    |w 1| ≤ (l2NormOn referenceCell w.toFun +
          l2NormOn referenceCell (w.derivative 1)) *
          l2NormOn referenceCell traceRho +
        l2NormOn referenceCell (w.derivative 1) := htrace
    _ ≤ (sobolevNorm w + sobolevNorm w) *
          l2NormOn referenceCell traceRho + sobolevNorm w := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (add_le_add h0 h1) hρ) h1
    _ = (2 * l2NormOn referenceCell traceRho + 1) * sobolevNorm w := by ring


end Exp2
