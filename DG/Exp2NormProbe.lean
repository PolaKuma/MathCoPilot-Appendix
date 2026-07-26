import Exp2Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter

noncomputable section
namespace Exp2

lemma l2NormOn_eq_sqrt_integral_sq {Ω : TopologicalSpace.Opens ℝ} {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set ℝ))) :
    l2NormOn Ω f =
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(volume.restrict (Ω : Set ℝ))) := by
  unfold l2NormOn
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  rw [h]
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  norm_num [Real.norm_eq_abs, sq_abs]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [Real.sqrt_eq_rpow]

lemma abs_integral_mul_le_l2NormOn {Ω : TopologicalSpace.Opens ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set ℝ)))
    (hg : MemLp g 2 (volume.restrict (Ω : Set ℝ))) :
    |∫ x, f x * g x ∂(volume.restrict (Ω : Set ℝ))| ≤
      l2NormOn Ω f * l2NormOn Ω g := by
  have hfg : Integrable (f * g) (volume.restrict (Ω : Set ℝ)) := hf.integrable_mul hg
  have hnorm := norm_integral_le_integral_norm (μ := volume.restrict (Ω : Set ℝ)) (f * g)
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ω : Set ℝ)) := by
    simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ω : Set ℝ)) := by
    simpa using hg
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Ω : Set ℝ)) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf' hg'
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ x, f x * g x ∂(volume.restrict (Ω : Set ℝ))| ≤
        ∫ x, ‖f x‖ * ‖g x‖ ∂(volume.restrict (Ω : Set ℝ)) := by
          exact hnorm.trans_eq (by
            apply integral_congr_ae
            filter_upwards with x
            simp [Pi.mul_apply, Real.norm_eq_abs])
    _ ≤ (∫ x, ‖f x‖ ^ 2 ∂(volume.restrict (Ω : Set ℝ))) ^ (1 / 2) *
        (∫ x, ‖g x‖ ^ 2 ∂(volume.restrict (Ω : Set ℝ))) ^ (1 / 2) := hholder
    _ = l2NormOn Ω f * l2NormOn Ω g := by
      rw [l2NormOn_eq_sqrt_integral_sq hf, l2NormOn_eq_sqrt_integral_sq hg]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      norm_num [Real.rpow_natCast]

lemma l2NormOn_nonneg (Ω : TopologicalSpace.Opens ℝ) (f : ℝ → ℝ) :
    0 ≤ l2NormOn Ω f := by
  exact ENNReal.toReal_nonneg

lemma l2NormOn_add_le {Ω : TopologicalSpace.Opens ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ω : Set ℝ)))
    (hg : MemLp g 2 (volume.restrict (Ω : Set ℝ))) :
    l2NormOn Ω (f + g) ≤ l2NormOn Ω f + l2NormOn Ω g := by
  have h := eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htop : eLpNorm f 2 (volume.restrict (Ω : Set ℝ)) +
      eLpNorm g 2 (volume.restrict (Ω : Set ℝ)) ≠ ∞ := by
    simp [hf.eLpNorm_ne_top, hg.eLpNorm_ne_top]
  have hr := ENNReal.toReal_mono htop h
  simpa [l2NormOn, ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using hr

lemma l2NormOn_neg (Ω : TopologicalSpace.Opens ℝ) (f : ℝ → ℝ) :
    l2NormOn Ω (-f) = l2NormOn Ω f := by
  simp [l2NormOn]

lemma l2NormOn_abs (Ω : TopologicalSpace.Opens ℝ) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ω : Set ℝ))) :
    l2NormOn Ω (fun x ↦ |f x|) = l2NormOn Ω f := by
  unfold l2NormOn
  rw [toReal_eLpNorm (by simpa [Real.norm_eq_abs] using hf.norm),
    toReal_eLpNorm hf]
  exact lpNorm_fun_abs hf 2

lemma l2NormOn_const_smul (Ω : TopologicalSpace.Opens ℝ) (c : ℝ)
    (f : ℝ → ℝ) :
    l2NormOn Ω (c • f) = |c| * l2NormOn Ω f := by
  unfold l2NormOn
  rw [eLpNorm_const_smul]
  simp [Real.norm_eq_abs]

lemma l2NormOn_finset_sum_le {ι : Type*} {Ω : TopologicalSpace.Opens ℝ}
    {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, MemLp (f i) 2 (volume.restrict (Ω : Set ℝ))) :
    l2NormOn Ω (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l2NormOn Ω (f i) := by
  have hsum : AEStronglyMeasurable (∑ i ∈ s, f i)
      (volume.restrict (Ω : Set ℝ)) := by
    exact Finset.aestronglyMeasurable_sum s fun i hi ↦ (hf i hi).1
  calc
    l2NormOn Ω (∑ i ∈ s, f i) =
        lpNorm (∑ i ∈ s, f i) 2 (volume.restrict (Ω : Set ℝ)) := by
      exact toReal_eLpNorm hsum
    _ ≤ ∑ i ∈ s, lpNorm (f i) 2 (volume.restrict (Ω : Set ℝ)) :=
      lpNorm_sum_le hf (by norm_num)
    _ = ∑ i ∈ s, l2NormOn Ω (f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (toReal_eLpNorm (hf i hi).1).symm

lemma l2NormOn_derivative_le_sobolevNorm {n : ℕ}
    (w : SobolevMapOn n referenceCell) {j : ℕ} (hj : j ≤ n) :
    l2NormOn referenceCell (w.derivative j) ≤ sobolevNorm w := by
  let S : ℝ := ∑ i ∈ Finset.range (n + 1),
    (l2NormOn referenceCell (w.derivative i)) ^ 2
  have hjmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hterm : (l2NormOn referenceCell (w.derivative j)) ^ 2 ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun i _ ↦ sq_nonneg (l2NormOn referenceCell (w.derivative i))) hjmem
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hsqrt : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS
  have hjnonneg := l2NormOn_nonneg referenceCell (w.derivative j)
  have hsqrtnonneg := Real.sqrt_nonneg S
  dsimp [sobolevNorm]
  change l2NormOn referenceCell (w.derivative j) ≤ Real.sqrt S
  nlinarith

lemma sobolevNorm_nonneg {n : ℕ} {Ω : TopologicalSpace.Opens ℝ}
    (w : SobolevMapOn n Ω) : 0 ≤ sobolevNorm w := by
  exact Real.sqrt_nonneg _

end Exp2
