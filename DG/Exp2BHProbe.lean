import Exp2ErrorBound
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section

open scoped BigOperators
open MeasureTheory

noncomputable def polynomialPrimitive (q : Polynomial ℝ) : Polynomial ℝ :=
  q.sum fun n a ↦ Polynomial.monomial (n + 1) (a / (n + 1 : ℝ))

lemma polynomialPrimitive_derivative (q : Polynomial ℝ) :
    (polynomialPrimitive q).derivative = q := by
  rw [polynomialPrimitive, Polynomial.sum_def, Polynomial.derivative_sum]
  calc
    ∑ n ∈ q.support,
        (Polynomial.monomial (n + 1) (q.coeff n / (n + 1 : ℝ))).derivative =
        ∑ n ∈ q.support, Polynomial.monomial n (q.coeff n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Polynomial.derivative_monomial]
      simp only [Nat.add_sub_cancel]
      congr 1
      have hn0 : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num
    _ = q := by
      simpa [Polynomial.sum_def] using Polynomial.sum_monomial_eq q

lemma polynomialPrimitive_mem {m : ℕ} {q : Polynomial ℝ}
    (hq : q ∈ Polynomial.degreeLT ℝ m) :
    polynomialPrimitive q ∈ Polynomial.degreeLT ℝ (m + 1) := by
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]
  apply (Polynomial.natDegree_le_iff_degree_le).1
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [polynomialPrimitive, Polynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hq0 : q ≠ 0 := by
    intro hzero
    subst q
    simp at hn
  have hnle : n ≤ q.natDegree := Polynomial.le_natDegree_of_mem_supp n hn
  have hqnat : q.natDegree < m :=
    (Polynomial.natDegree_lt_iff_degree_lt hq0).2 ((Polynomial.mem_degreeLT).1 hq)
  have hnlt : n < m := hnle.trans_lt hqnat
  have hne : n + 1 ≠ N := by omega
  simp [Polynomial.coeff_monomial, hne]

lemma weakPrimitive_polynomial_eval (q : Polynomial ℝ) (x : ℝ) :
    Exp2.weakPrimitive (fun y ↦ q.eval y) x =
      (polynomialPrimitive q).eval x - (polynomialPrimitive q).eval 0 := by
  have hdiff : ∀ y ∈ Set.uIcc (0 : ℝ) x,
      DifferentiableAt ℝ (fun t ↦ (polynomialPrimitive q).eval t) y := by
    intro y hy
    exact ((polynomialPrimitive q).hasDerivAt y).differentiableAt
  have heq : deriv (fun t ↦ (polynomialPrimitive q).eval t) =
      fun t ↦ q.eval t := by
    funext t
    rw [(polynomialPrimitive q).hasDerivAt t |>.deriv,
      polynomialPrimitive_derivative]
  have hint : IntervalIntegrable
      (deriv (fun t ↦ (polynomialPrimitive q).eval t)) volume 0 x := by
    have hcont : Continuous (fun t : ℝ ↦ q.eval t) := Exp2.polynomial_eval_continuous q
    rw [heq]
    exact hcont.intervalIntegrable 0 x
  have h := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [heq] at h
  exact h

namespace Exp2

lemma WeakDerivativeOn.congr_right_ae {f g h : ℝ → ℝ}
    (hfg : WeakDerivativeOn referenceCell f g)
    (hgh : g =ᵐ[volume.restrict referenceCell] h) :
    WeakDerivativeOn referenceCell f h := by
  intro φ
  rw [hfg φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hgh] with x hx
  rw [hx]

lemma WeakDerivativeOn.sub_of_memLp {f₁ g₁ f₂ g₂ : ℝ → ℝ}
    (h₁ : WeakDerivativeOn referenceCell f₁ g₁)
    (h₂ : WeakDerivativeOn referenceCell f₂ g₂)
    (hf₁ : MemLp f₁ 2 (volume.restrict referenceCell))
    (hg₁ : MemLp g₁ 2 (volume.restrict referenceCell))
    (hf₂ : MemLp f₂ 2 (volume.restrict referenceCell))
    (hg₂ : MemLp g₂ 2 (volume.restrict referenceCell)) :
    WeakDerivativeOn referenceCell (f₁ - f₂) (g₁ - g₂) := by
  have hneg := WeakDerivativeOn.const_smul (-1) h₂
  have hadd := WeakDerivativeOn.add_of_memLp h₁ hneg hf₁ hg₁
    (hf₂.const_smul (-1)) (hg₂.const_smul (-1))
  simpa [sub_eq_add_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hadd

theorem weakDerivative_chain_ae_polynomial :
    ∀ (m : ℕ) (f : ℕ → ℝ → ℝ),
      (∀ j ≤ m, MemLp (f j) 2 (volume.restrict referenceCell)) →
      (∀ j < m, WeakDerivativeOn referenceCell (f j) (f (j + 1))) →
      f m = 0 →
      ∃ p : Polynomial ℝ, p ∈ Polynomial.degreeLT ℝ m ∧
        f 0 =ᵐ[volume.restrict referenceCell] fun x ↦ p.eval x := by
  intro m
  induction m with
  | zero =>
      intro f hLp hweak htop
      refine ⟨0, by simp, ?_⟩
      have hzero : f 0 = 0 := by simpa using htop
      filter_upwards with x
      rw [hzero]
      simp
  | succ m ih =>
      intro f hLp hweak htop
      let tail : ℕ → ℝ → ℝ := fun j ↦ f (j + 1)
      have htailLp : ∀ j ≤ m,
          MemLp (tail j) 2 (volume.restrict referenceCell) := by
        intro j hj
        exact hLp (j + 1) (by omega)
      have htailWeak : ∀ j < m,
          WeakDerivativeOn referenceCell (tail j) (tail (j + 1)) := by
        intro j hj
        simpa [tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hweak (j + 1) (by omega)
      have htailTop : tail m = 0 := by
        simpa [tail] using htop
      obtain ⟨q, hqdeg, hqae⟩ := ih tail htailLp htailWeak htailTop
      have hqLp : MemLp (fun x : ℝ ↦ q.eval x) 2
          (volume.restrict referenceCell) := polynomial_eval_memLp_reference q
      have hf0Lp := hLp 0 (by omega)
      have hf1Lp := hLp 1 (by omega)
      have hf0weak : WeakDerivativeOn referenceCell (f 0) (f 1) :=
        hweak 0 (by omega)
      have htail0 : tail 0 = f 1 := by
        funext x
        simp [tail]
      have hf1ae : f 1 =ᵐ[volume.restrict referenceCell] fun x ↦ q.eval x := by
        simpa [htail0] using hqae
      have hf0weakq : WeakDerivativeOn referenceCell (f 0) (fun x ↦ q.eval x) :=
        hf0weak.congr_right_ae hf1ae
      have hprimWeak : WeakDerivativeOn referenceCell
          (weakPrimitive fun x ↦ q.eval x) (fun x ↦ q.eval x) :=
        weakPrimitive_weakDerivative hqLp
      have hprimLp : MemLp (weakPrimitive fun x ↦ q.eval x) 2
          (volume.restrict referenceCell) := weakPrimitive_memLp hqLp
      have hdiffWeak : WeakDerivativeOn referenceCell
          (f 0 - weakPrimitive fun x ↦ q.eval x) 0 := by
        simpa using hf0weakq.sub_of_memLp hprimWeak hf0Lp hqLp hprimLp hqLp
      have hdiffLp : MemLp (f 0 - weakPrimitive fun x ↦ q.eval x) 2
          (volume.restrict referenceCell) := hf0Lp.sub hprimLp
      obtain ⟨c, hcae⟩ := weakDerivative_zero_ae_constant hdiffWeak hdiffLp
      let p : Polynomial ℝ :=
        polynomialPrimitive q + Polynomial.C (c - (polynomialPrimitive q).eval 0)
      refine ⟨p, ?_, ?_⟩
      · have hpprim := polynomialPrimitive_mem hqdeg
        have hc : Polynomial.C (c - (polynomialPrimitive q).eval 0) ∈
            Polynomial.degreeLT ℝ (m + 1) := by
          change Polynomial.C (c - (polynomialPrimitive q).eval 0) ∈
            Polynomial.degreeLT ℝ (m + 1)
          rw [Polynomial.mem_degreeLT]
          exact lt_of_le_of_lt Polynomial.degree_C_le (by positivity)
        exact add_mem hpprim hc
      · filter_upwards [hcae] with x hx
        have hprimx := weakPrimitive_polynomial_eval q x
        dsimp only [Pi.sub_apply] at hx
        rw [hprimx] at hx
        dsimp [p]
        rw [Polynomial.eval_add, Polynomial.eval_C]
        linarith

theorem SobolevMapOn.exists_polynomial_of_top_derivative_eq_zero {m : ℕ}
    (w : SobolevMapOn m referenceCell) (htop : w.derivative m = 0) :
    ∃ p : Polynomial ℝ, p ∈ Polynomial.degreeLT ℝ m ∧
      ∀ x ∈ referenceCell, w x = p.eval x := by
  obtain ⟨p, hpdeg, hpae⟩ := weakDerivative_chain_ae_polynomial m w.derivative
    w.memLp_derivative w.weakDerivative_succ htop
  have hfunAe : w.toFun =ᵐ[volume.restrict referenceCell] fun x ↦ p.eval x := by
    rw [← w.derivative_zero]
    exact hpae
  have hfunIoo : w.toFun =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
      fun x ↦ p.eval x := by
    simpa [referenceCell, cell] using hfunAe
  have hfunIcc : w.toFun =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      fun x ↦ p.eval x := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc :
      Set.Ioo (0 : ℝ) 1 =ᵐ[volume] Set.Icc 0 1)]
    exact hfunIoo
  have hwcont : ContinuousOn w.toFun (Set.Icc (0 : ℝ) 1) := by
    simpa [referenceCell, cell] using w.continuousOn
  have hpcont : ContinuousOn (fun x : ℝ ↦ p.eval x) (Set.Icc 0 1) :=
    (polynomial_eval_continuous p).continuousOn
  have heq := volume.eqOn_Icc_of_ae_eq (by norm_num : (0 : ℝ) ≠ 1)
    hfunIcc hwcont hpcont
  refine ⟨p, hpdeg, ?_⟩
  intro x hx
  apply heq
  have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [referenceCell, cell] using hx
  exact ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩

def iteratedWeakPrimitive : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, g => g
  | r + 1, g => weakPrimitive (iteratedWeakPrimitive r g)

lemma iteratedWeakPrimitive_memLp (r : ℕ) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    MemLp (iteratedWeakPrimitive r g) 2 (volume.restrict referenceCell) := by
  induction r with
  | zero => simpa [iteratedWeakPrimitive] using hg
  | succ r ih =>
      simpa [iteratedWeakPrimitive] using weakPrimitive_memLp ih

lemma iteratedWeakPrimitive_weakDerivative (r : ℕ) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    WeakDerivativeOn referenceCell (iteratedWeakPrimitive (r + 1) g)
      (iteratedWeakPrimitive r g) := by
  simpa [iteratedWeakPrimitive] using
    weakPrimitive_weakDerivative (iteratedWeakPrimitive_memLp r hg)

lemma iteratedWeakPrimitive_l2NormOn_le (r : ℕ) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    l2NormOn referenceCell (iteratedWeakPrimitive r g) ≤
      l2NormOn referenceCell g := by
  induction r with
  | zero => simp [iteratedWeakPrimitive]
  | succ r ih =>
      exact (weakPrimitive_l2NormOn_le (iteratedWeakPrimitive_memLp r hg)).trans ih

def primitiveSobolev (k : ℕ) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    SobolevMapOn (k + 1) referenceCell where
  toFun := iteratedWeakPrimitive (k + 1) g
  derivative := fun j ↦ iteratedWeakPrimitive (k + 1 - j) g
  derivative_zero := by
    simp
  continuousOn := by
    have hac := weakPrimitive_absolutelyContinuous
      (iteratedWeakPrimitive_memLp k hg)
    have hcont : ContinuousOn (weakPrimitive (iteratedWeakPrimitive k g))
        (Set.Icc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hac.continuousOn
    have hclosure : closure (referenceCell : Set ℝ) = Set.Icc (0 : ℝ) 1 := by
      change closure (Set.Ioo 0 (0 + 1)) = Set.Icc 0 1
      norm_num only [zero_add]
      exact closure_Ioo (by norm_num)
    rw [hclosure]
    simpa [iteratedWeakPrimitive] using hcont
  memLp_derivative := by
    intro j hj
    exact iteratedWeakPrimitive_memLp _ hg
  weakDerivative_succ := by
    intro j hj
    have harith : k + 1 - j = (k + 1 - (j + 1)) + 1 := by omega
    rw [harith]
    exact iteratedWeakPrimitive_weakDerivative _ hg

@[simp] lemma primitiveSobolev_derivative (k : ℕ) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict referenceCell)) (j : ℕ) :
    (primitiveSobolev k g hg).derivative j =
      iteratedWeakPrimitive (k + 1 - j) g := rfl

@[simp] lemma primitiveSobolev_top_derivative (k : ℕ) (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    (primitiveSobolev k g hg).derivative (k + 1) = g := by
  simp [primitiveSobolev, iteratedWeakPrimitive]

set_option maxHeartbeats 800000 in
lemma primitiveSobolev_sobolevNorm_le (k : ℕ) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict referenceCell)) :
    sobolevNorm (primitiveSobolev k g hg) ≤
      (k + 2 : ℝ) * l2NormOn referenceCell g := by
  let L := l2NormOn referenceCell g
  let S := ∑ j ∈ Finset.range (k + 2),
    (l2NormOn referenceCell ((primitiveSobolev k g hg).derivative j)) ^ 2
  let A : ℝ := k + 2
  have hL : 0 ≤ L := l2NormOn_nonneg referenceCell g
  have hterm : ∀ j ∈ Finset.range (k + 2),
      (l2NormOn referenceCell ((primitiveSobolev k g hg).derivative j)) ^ 2 ≤
        L ^ 2 := by
    intro j hj
    have hle : l2NormOn referenceCell
        ((primitiveSobolev k g hg).derivative j) ≤ L := by
      rw [primitiveSobolev_derivative]
      exact iteratedWeakPrimitive_l2NormOn_le (k + 1 - j) hg
    have hnonneg := l2NormOn_nonneg referenceCell
      ((primitiveSobolev k g hg).derivative j)
    nlinarith
  have hS : S ≤ A * L ^ 2 := by
    calc
      S ≤ ∑ _j ∈ Finset.range (k + 2), L ^ 2 := by
        dsimp [S]
        exact Finset.sum_le_sum fun j hj ↦ hterm j hj
      _ = A * L ^ 2 := by
        simp [A]
  have hSnonneg : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _
  have hA : 1 ≤ A := by
    dsimp [A]
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hAnonneg : 0 ≤ A := le_trans (by norm_num) hA
  have hAquad : A ≤ A ^ 2 := by nlinarith
  have hboundSq : S ≤ (A * L) ^ 2 := by
    calc
      S ≤ A * L ^ 2 := hS
      _ ≤ A ^ 2 * L ^ 2 :=
        mul_le_mul_of_nonneg_right hAquad (sq_nonneg L)
      _ = (A * L) ^ 2 := by ring
  have hsqrtSq : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hSnonneg
  have hsqrtNonneg := Real.sqrt_nonneg S
  have hALnonneg : 0 ≤ A * L := mul_nonneg hAnonneg hL
  change Real.sqrt S ≤ A * L
  nlinarith

theorem gaussRadau_add (k : ℕ)
    (u v : SobolevMapOn (k + 1) referenceCell) :
    gaussRadau k (u + v) = gaussRadau k u + gaussRadau k v := by
  apply gaussRadauAt_unique k (u + v) (gaussRadau_spec k (u + v))
  constructor
  · intro q hq
    have hu := (gaussRadau_spec k u).1 q hq
    have hv := (gaussRadau_spec k v).1 q hq
    have hqLp := polynomial_eval_memLp_reference q
    have hpuLp := polynomial_eval_memLp_reference (gaussRadau k u).1
    have hpvLp := polynomial_eval_memLp_reference (gaussRadau k v).1
    have heuLp : MemLp
        (fun x ↦ (gaussRadau k u).1.eval x - u x) 2
        (volume.restrict referenceCell) := by
      simpa [sub_eq_add_neg] using hpuLp.add u.toFun_memLp.neg
    have hevLp : MemLp
        (fun x ↦ (gaussRadau k v).1.eval x - v x) 2
        (volume.restrict referenceCell) := by
      simpa [sub_eq_add_neg] using hpvLp.add v.toFun_memLp.neg
    have heuInt : Integrable
        (fun x ↦ ((gaussRadau k u).1.eval x - u x) * q.eval x)
        (volume.restrict referenceCell) := heuLp.integrable_mul hqLp
    have hevInt : Integrable
        (fun x ↦ ((gaussRadau k v).1.eval x - v x) * q.eval x)
        (volume.restrict referenceCell) := hevLp.integrable_mul hqLp
    calc
      (∫ x, (((gaussRadau k u + gaussRadau k v).1.eval x - (u + v) x) *
          q.eval x) ∂(volume.restrict referenceCell)) =
          ∫ x, (((gaussRadau k u).1.eval x - u x) * q.eval x +
            ((gaussRadau k v).1.eval x - v x) * q.eval x)
            ∂(volume.restrict referenceCell) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [Submodule.coe_add, Polynomial.eval_add]
        change ((((gaussRadau k u).1.eval x + (gaussRadau k v).1.eval x) -
          (u x + v x)) * q.eval x) = _
        ring
      _ = (∫ x, ((gaussRadau k u).1.eval x - u x) * q.eval x
            ∂(volume.restrict referenceCell)) +
          ∫ x, ((gaussRadau k v).1.eval x - v x) * q.eval x
            ∂(volume.restrict referenceCell) := by
        simpa only [Pi.add_apply] using integral_add heuInt hevInt
      _ = 0 := by rw [hu, hv]; ring
  · simp only [Submodule.coe_add, Polynomial.eval_add]
    change (gaussRadau k u).1.eval 1 + (gaussRadau k v).1.eval 1 = u 1 + v 1
    rw [(gaussRadau_spec k u).2, (gaussRadau_spec k v).2]

lemma referenceError_add (k : ℕ)
    (u v : SobolevMapOn (k + 1) referenceCell) :
    referenceError k (u + v) = referenceError k u + referenceError k v := by
  funext x
  rw [referenceError, gaussRadau_add]
  simp only [Submodule.coe_add, Polynomial.eval_add]
  change ((gaussRadau k u).1.eval x + (gaussRadau k v).1.eval x) -
    (u x + v x) =
      ((gaussRadau k u).1.eval x - u x) +
        ((gaussRadau k v).1.eval x - v x)
  ring

lemma referenceError_memLp (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    MemLp (referenceError k w) 2 (volume.restrict referenceCell) := by
  have hp := polynomial_eval_memLp_reference (gaussRadau k w).1
  simpa [referenceError, sub_eq_add_neg] using hp.add w.toFun_memLp.neg

lemma errorFunctional_add_of_memLp (k : ℕ)
    (u v : SobolevMapOn (k + 1) referenceCell) {z : ℝ → ℝ}
    (hz : MemLp z 2 (volume.restrict referenceCell)) :
    errorFunctional k (u + v) z =
      errorFunctional k u z + errorFunctional k v z := by
  have huInt : Integrable (referenceError k u * z)
      (volume.restrict referenceCell) := (referenceError_memLp k u).integrable_mul hz
  have hvInt : Integrable (referenceError k v * z)
      (volume.restrict referenceCell) := (referenceError_memLp k v).integrable_mul hz
  rw [errorFunctional, referenceError_add]
  change (∫ x, (referenceError k u x + referenceError k v x) * z x
      ∂(volume.restrict referenceCell)) = _
  simp_rw [add_mul]
  simpa only [Pi.add_apply, errorFunctional] using integral_add huInt hvInt

lemma l2NormOn_le_of_unit_pairings {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict referenceCell)) {B : ℝ}
    (hpair : ∀ z : ℝ → ℝ, MemLp z 2 (volume.restrict referenceCell) →
      l2NormOn referenceCell z ≤ 1 →
      |∫ x, f x * z x ∂(volume.restrict referenceCell)| ≤ B) :
    l2NormOn referenceCell f ≤ B := by
  let L := l2NormOn referenceCell f
  have hL : 0 ≤ L := l2NormOn_nonneg referenceCell f
  by_cases hLzero : L = 0
  · simpa [L, hLzero] using hpair (fun _ ↦ 0) MemLp.zero (by simp [l2NormOn])
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
    let z : ℝ → ℝ := L⁻¹ • f
    have hz : MemLp z 2 (volume.restrict referenceCell) := hf.const_smul L⁻¹
    have hzNorm : l2NormOn referenceCell z = 1 := by
      dsimp [z]
      rw [l2NormOn_const_smul]
      rw [abs_of_pos (inv_pos.mpr hLpos)]
      field_simp [hLzero]
      rfl
    have hsqInt : (∫ x, ‖f x‖ ^ 2 ∂(volume.restrict referenceCell)) = L ^ 2 := by
      have hnorm := l2NormOn_eq_sqrt_integral_sq hf
      have hIntNonneg : 0 ≤ ∫ x, ‖f x‖ ^ 2
          ∂(volume.restrict referenceCell) := integral_nonneg fun x ↦ sq_nonneg _
      have hsqrt := Real.sq_sqrt hIntNonneg
      calc
        (∫ x, ‖f x‖ ^ 2 ∂(volume.restrict referenceCell)) =
            (Real.sqrt (∫ x, ‖f x‖ ^ 2
              ∂(volume.restrict referenceCell))) ^ 2 := hsqrt.symm
        _ = L ^ 2 := by rw [← hnorm]
    have hff : (∫ x, f x * f x ∂(volume.restrict referenceCell)) = L ^ 2 := by
      rw [← hsqInt]
      apply integral_congr_ae
      filter_upwards with x
      simp [Real.norm_eq_abs, pow_two]
    have hpairValue : (∫ x, f x * z x ∂(volume.restrict referenceCell)) = L := by
      calc
        (∫ x, f x * z x ∂(volume.restrict referenceCell)) =
            ∫ x, L⁻¹ * (f x * f x) ∂(volume.restrict referenceCell) := by
          apply integral_congr_ae
          filter_upwards with x
          simp [z]
          ring
        _ = L⁻¹ * (∫ x, f x * f x ∂(volume.restrict referenceCell)) := by
          rw [integral_const_mul]
        _ = L := by rw [hff]; field_simp [hLzero]
    have h := hpair z hz (by rw [hzNorm])
    rw [hpairValue, abs_of_pos hLpos] at h
    exact h

theorem brambleHilbert_reference_complete (k : ℕ)
    (hbounded : ErrorFunctionalBounded k)
    (hannihilates : ErrorFunctionalAnnihilatesPolynomials k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SobolevMapOn (k + 1) referenceCell,
      l2NormOn referenceCell (referenceError k w) ≤
        C * sobolevSeminorm w := by
  obtain ⟨C₀, hC₀, hbound⟩ := hbounded
  let C : ℝ := C₀ * (k + 2)
  have hk : 0 ≤ (k + 2 : ℝ) := by positivity
  refine ⟨C, mul_nonneg hC₀ hk, ?_⟩
  intro w
  let g : ℝ → ℝ := w.derivative (k + 1)
  have hg : MemLp g 2 (volume.restrict referenceCell) :=
    w.memLp_derivative (k + 1) (by omega)
  let v : SobolevMapOn (k + 1) referenceCell := primitiveSobolev k g hg
  let q : SobolevMapOn (k + 1) referenceCell := w - v
  have hqtop : q.derivative (k + 1) = 0 := by
    change w.derivative (k + 1) - v.derivative (k + 1) = 0
    rw [show v.derivative (k + 1) = g by
      simpa [v] using primitiveSobolev_top_derivative k g hg]
    simp [g]
  obtain ⟨p, hpdeg, hpEq⟩ := q.exists_polynomial_of_top_derivative_eq_zero hqtop
  have hpNat : p.natDegree ≤ k := (mem_PolyLE_iff).1 hpdeg
  apply l2NormOn_le_of_unit_pairings (referenceError_memLp k w)
  intro z hz hzunit
  have hqzero : errorFunctional k q z = 0 :=
    hannihilates q z ⟨p, hpNat, hpEq⟩
  have hadd := errorFunctional_add_of_memLp k q v hz
  have hdecomp : q + v = w := by
    dsimp [q]
    exact sub_add_cancel w v
  rw [hdecomp] at hadd
  have heq : errorFunctional k w z = errorFunctional k v z := by
    rw [hqzero] at hadd
    simpa using hadd
  change |errorFunctional k w z| ≤ C * sobolevSeminorm w
  rw [heq]
  calc
    |errorFunctional k v z| ≤ C₀ * sobolevNorm v := hbound v z hz hzunit
    _ ≤ C₀ * ((k + 2 : ℝ) * l2NormOn referenceCell g) :=
      mul_le_mul_of_nonneg_left (by
        simpa [v] using primitiveSobolev_sobolevNorm_le k hg) hC₀
    _ = C * sobolevSeminorm w := by
      simp only [C, g, sobolevSeminorm]
      ring

end Exp2
