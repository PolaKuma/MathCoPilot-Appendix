import Chapter00.Renewal.Renewal
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter00
namespace Renewal

/-- Cauchy convolution of two real sequences. -/
def natConvolution (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

local infixr:70 " ⋆ₙ " => natConvolution

lemma natConvolution_eq_powerSeries_coeff (f g : ℕ → ℝ) (n : ℕ) :
    (f ⋆ₙ g) n = PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.mk g) := by
  rw [natConvolution, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ f i * g j) n).symm

lemma powerSeries_mk_natConvolution (f g : ℕ → ℝ) :
    PowerSeries.mk (f ⋆ₙ g) = PowerSeries.mk f * PowerSeries.mk g := by
  ext n
  rw [PowerSeries.coeff_mk, ← natConvolution_eq_powerSeries_coeff]

lemma natConvolution_assoc (f g h : ℕ → ℝ) :
    (f ⋆ₙ g) ⋆ₙ h = f ⋆ₙ (g ⋆ₙ h) := by
  funext n
  rw [natConvolution_eq_powerSeries_coeff,
    natConvolution_eq_powerSeries_coeff]
  rw [powerSeries_mk_natConvolution, powerSeries_mk_natConvolution]
  exact
    congrArg (PowerSeries.coeff n)
      (mul_assoc (PowerSeries.mk f) (PowerSeries.mk g) (PowerSeries.mk h))

lemma natConvolution_comm (f g : ℕ → ℝ) : f ⋆ₙ g = g ⋆ₙ f := by
  funext n
  rw [natConvolution_eq_powerSeries_coeff,
    natConvolution_eq_powerSeries_coeff, mul_comm]

def convolutionUnit : ℕ → ℝ
  | 0 => 1
  | _ + 1 => 0

@[simp] lemma natConvolution_unit (f : ℕ → ℝ) :
    f ⋆ₙ convolutionUnit = f := by
  have hunit : PowerSeries.mk convolutionUnit = (1 : PowerSeries ℝ) := by
    ext n
    cases n <;> simp [convolutionUnit]
  funext n
  rw [natConvolution_eq_powerSeries_coeff, hunit, mul_one,
    PowerSeries.coeff_mk]

@[simp] lemma unit_natConvolution (f : ℕ → ℝ) :
    convolutionUnit ⋆ₙ f = f := by
  rw [natConvolution_comm, natConvolution_unit]

lemma natConvolution_add_right (f g h : ℕ → ℝ) :
    f ⋆ₙ (g + h) = f ⋆ₙ g + f ⋆ₙ h := by
  funext n
  simp only [natConvolution, Pi.add_apply, mul_add, Finset.sum_add_distrib]

def shiftedWeights (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => p n

lemma shiftedWeights_convolution_succ (p v : ℕ → ℝ) (n : ℕ) :
    (shiftedWeights p ⋆ₙ v) (n + 1) =
      ∑ j ∈ Finset.range (n + 1), p j * v (n - j) := by
  rw [natConvolution, Finset.sum_range_succ']
  simp [shiftedWeights]

lemma renewalMass_convolution_equation (p : ℕ → ℝ) :
    renewalMass p = convolutionUnit + shiftedWeights p ⋆ₙ renewalMass p := by
  funext n
  cases n with
  | zero => simp [convolutionUnit, shiftedWeights, natConvolution]
  | succ n =>
      rw [renewalMass_succ, Pi.add_apply,
        shiftedWeights_convolution_succ]
      simp [convolutionUnit]

lemma convolution_renewalMass_equation (p e : ℕ → ℝ) :
    e ⋆ₙ renewalMass p =
      e + shiftedWeights p ⋆ₙ (e ⋆ₙ renewalMass p) := by
  conv_lhs => rw [renewalMass_convolution_equation p]
  rw [natConvolution_add_right, natConvolution_unit]
  congr 1
  rw [← natConvolution_assoc, natConvolution_comm e (shiftedWeights p),
    natConvolution_assoc]

lemma renewalResponse_eq_convolution (p e : ℕ → ℝ) :
    renewalResponse p e = e ⋆ₙ renewalMass p := by
  symm
  apply eq_renewalResponse_of_recurrence
  · have h := congrFun (convolution_renewalMass_equation p e) 0
    simpa [shiftedWeights, natConvolution] using h
  · intro n
    have h := congrFun (convolution_renewalMass_equation p e) (n + 1)
    simpa [shiftedWeights_convolution_succ] using h

lemma tendsto_natConvolution_of_summable
    {e r : ℕ → ℝ} {L : ℝ}
    (he0 : ∀ k, 0 ≤ e k) (he : Summable e)
    (hrBound : ∀ n, |r n| ≤ 1)
    (hr : Tendsto r atTop (nhds L)) :
    Tendsto (e ⋆ₙ r) atTop (nhds ((∑' k, e k) * L)) := by
  let F : ℕ → ℕ → ℝ := fun n k ↦
    if k ≤ n then e k * r (n - k) else 0
  have hFsum (n : ℕ) : (∑' k, F n k) = (e ⋆ₙ r) n := by
    rw [tsum_eq_sum (s := Finset.range (n + 1))]
    · apply Finset.sum_congr rfl
      intro k hk
      simp [F, Nat.le_of_lt_succ (Finset.mem_range.1 hk), natConvolution]
    · intro k hk
      have hnk : ¬ k ≤ n := by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
      simp [F, hnk]
  have hFlim (k : ℕ) : Tendsto (fun n ↦ F n k) atTop (nhds (e k * L)) := by
    refine (tendsto_const_nhds.mul
      (hr.comp (tendsto_nat_sub_const_atTop k))).congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    simp [F, hn]
  have hFbound : ∀ᶠ n in atTop, ∀ k, ‖F n k‖ ≤ e k := by
    filter_upwards [] with n
    intro k
    by_cases hkn : k ≤ n
    · simp only [F, if_pos hkn, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (he0 k)]
      exact mul_le_of_le_one_right (he0 k) (hrBound (n - k))
    · simp [F, hkn, he0 k]
  have h := tendsto_tsum_of_dominated_convergence he hFlim hFbound
  rw [he.tsum_mul_right L] at h
  exact h.congr' (Eventually.of_forall fun n ↦ hFsum n)

end Renewal
end Chapter00
