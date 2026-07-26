import Chapter00.Renewal.RenewalConvolution
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.FrobeniusNumber

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter00
namespace Renewal

local infixr:70 " ⋆ₙ " => natConvolution

def renewalEnergy (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1),
      p j * renewalMass p (n - j) ^ 2) - renewalMass p (n + 1) ^ 2

lemma partialSum_le_one {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, p n ≤ 1 := by
  simpa [ht] using hs.sum_le_tsum (Finset.range N) (fun n _ ↦ hp n)

lemma renewalEnergy_nonneg {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1) (n : ℕ) :
    0 ≤ renewalEnergy p n := by
  let r := renewalMass p
  let s := Finset.range (n + 1)
  have hcs : (∑ j ∈ s, p j * r (n - j)) ^ 2 ≤
      (∑ j ∈ s, p j) *
        ∑ j ∈ s, p j * r (n - j) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro j hj
      exact hp j
    · intro j hj
      exact mul_nonneg (hp j) (sq_nonneg _)
    · intro j hj
      ring
  have hsum : ∑ j ∈ s, p j ≤ 1 := partialSum_le_one hp hs ht (n + 1)
  have hA : 0 ≤ ∑ j ∈ s, p j * r (n - j) ^ 2 :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hp j) (sq_nonneg _)
  have hr : r (n + 1) = ∑ j ∈ s, p j * r (n - j) := by
    exact renewalMass_succ p n
  unfold renewalEnergy
  change 0 ≤ (∑ j ∈ s, p j * r (n - j) ^ 2) - r (n + 1) ^ 2
  rw [sub_nonneg, hr]
  exact hcs.trans (by simpa using mul_le_of_le_one_left hA hsum)

lemma sum_range_renewalEnergy_le_one {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, renewalEnergy p n ≤ 1 := by
  let r := renewalMass p
  let b : ℕ → ℝ := fun m ↦ if m < N then r m ^ 2 else 0
  have hb0 : ∀ m, 0 ≤ b m := by
    intro m
    simp only [b]
    split <;> positivity
  have hb : Summable b := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro m hm
    have hNm : ¬ m < N := by simpa [Finset.mem_range] using hm
    simp [b, hNm]
  have hpNorm : Summable (fun n ↦ ‖p n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hp _)] using hs
  have hbNorm : Summable (fun n ↦ ‖b n‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb0 _)] using hb
  have hprod := hasSum_sum_range_mul_of_summable_norm hpNorm hbNorm
  have hfirst :
      (∑ n ∈ Finset.range N,
        ∑ j ∈ Finset.range (n + 1), p j * r (n - j) ^ 2) ≤
        ∑ m ∈ Finset.range N, r m ^ 2 := by
    calc
      _ = ∑ n ∈ Finset.range N, (p ⋆ₙ b) n := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro j hj
        have hmn : n - j < N :=
          lt_of_le_of_lt (Nat.sub_le n j) (Finset.mem_range.1 hn)
        simp [natConvolution, b, hmn]
      _ ≤ ∑' n, (p ⋆ₙ b) n :=
        hprod.summable.sum_le_tsum _ (fun n _ ↦
          Finset.sum_nonneg fun j _ ↦ mul_nonneg (hp j) (hb0 _))
      _ = (∑' n, p n) * ∑' m, b m := by
        simpa [natConvolution] using hprod.tsum_eq
      _ = ∑ m ∈ Finset.range N, r m ^ 2 := by
        rw [ht, one_mul, tsum_eq_sum (s := Finset.range N)]
        · apply Finset.sum_congr rfl
          intro m hm
          simp [b, Finset.mem_range.1 hm]
        · intro m hm
          have hNm : ¬ m < N := by simpa [Finset.mem_range] using hm
          simp [b, hNm]
  have htel :
      (∑ m ∈ Finset.range N, r m ^ 2) -
          (∑ n ∈ Finset.range N, r (n + 1) ^ 2) =
        1 - r N ^ 2 := by
    have hshift := Finset.sum_range_succ' (fun m ↦ r m ^ 2) N
    have hfront := Finset.sum_range_succ (fun m ↦ r m ^ 2) N
    have hr0 : r 0 ^ 2 = 1 := by simp [r]
    linarith
  calc
    ∑ n ∈ Finset.range N, renewalEnergy p n =
        (∑ n ∈ Finset.range N,
          ∑ j ∈ Finset.range (n + 1), p j * r (n - j) ^ 2) -
          ∑ n ∈ Finset.range N, r (n + 1) ^ 2 := by
            simp [renewalEnergy, r, Finset.sum_sub_distrib]
    _ ≤ (∑ m ∈ Finset.range N, r m ^ 2) -
          ∑ n ∈ Finset.range N, r (n + 1) ^ 2 := sub_le_sub_right hfirst _
    _ = 1 - r N ^ 2 := htel
    _ ≤ 1 := sub_le_self _ (sq_nonneg _)

lemma renewal_shift_sq_le_energy {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1) {j n : ℕ} (hjn : j ≤ n) :
    p j * (renewalMass p (n - j) - renewalMass p (n + 1)) ^ 2 ≤
      renewalEnergy p n := by
  let r := renewalMass p
  let s := Finset.range (n + 1)
  have hj : j ∈ s := Finset.mem_range.2 (Nat.lt_succ_of_le hjn)
  have hterm : p j * (r (n - j) - r (n + 1)) ^ 2 ≤
      ∑ k ∈ s, p k * (r (n - k) - r (n + 1)) ^ 2 := by
    apply Finset.single_le_sum (s := s) (f := fun k ↦
      p k * (r (n - k) - r (n + 1)) ^ 2)
    · intro k hk
      exact mul_nonneg (hp k) (sq_nonneg _)
    · exact hj
  have hsum : ∑ k ∈ s, p k ≤ 1 := partialSum_le_one hp hs ht (n + 1)
  have hr : r (n + 1) = ∑ k ∈ s, p k * r (n - k) :=
    renewalMass_succ p n
  have hvar :
      (∑ k ∈ s, p k * (r (n - k) - r (n + 1)) ^ 2) =
        renewalEnergy p n - r (n + 1) ^ 2 * (1 - ∑ k ∈ s, p k) := by
    calc
      _ = ∑ k ∈ s, (p k * r (n - k) ^ 2 -
          2 * r (n + 1) * (p k * r (n - k)) +
          r (n + 1) ^ 2 * p k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (∑ k ∈ s, p k * r (n - k) ^ 2) -
          2 * r (n + 1) * (∑ k ∈ s, p k * r (n - k)) +
          r (n + 1) ^ 2 * (∑ k ∈ s, p k) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp_rw [Finset.mul_sum]
      _ = renewalEnergy p n - r (n + 1) ^ 2 *
          (1 - ∑ k ∈ s, p k) := by
            rw [← hr]
            unfold renewalEnergy
            change _ =
              ((∑ k ∈ s, p k * r (n - k) ^ 2) - r (n + 1) ^ 2) - _
            ring
  rw [hvar] at hterm
  exact hterm.trans (sub_le_self _
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsum)))

lemma summable_renewalEnergy {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1) : Summable (renewalEnergy p) := by
  apply summable_of_sum_range_le (fun n ↦ renewalEnergy_nonneg hp hs ht n)
  exact sum_range_renewalEnergy_le_one hp hs ht

lemma summable_renewal_shift_sq {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1) {j : ℕ} (hpj : 0 < p j) :
    Summable (fun n ↦
      (renewalMass p (n + j + 1) - renewalMass p n) ^ 2) := by
  have henergy : Summable (fun n ↦ renewalEnergy p (n + j)) :=
    (summable_nat_add_iff j).2 (summable_renewalEnergy hp hs ht)
  have hdiv : Summable (fun n ↦ renewalEnergy p (n + j) / p j) :=
    henergy.div_const (p j)
  apply hdiv.of_nonneg_of_le
  · intro n
    exact sq_nonneg _
  · intro n
    apply (le_div_iff₀ hpj).2
    have h := renewal_shift_sq_le_energy hp hs ht (j := j) (n := n + j)
      (Nat.le_add_left j n)
    have h' : p j * (renewalMass p n - renewalMass p (n + j + 1)) ^ 2 ≤
        renewalEnergy p (n + j) := by
      simpa [Nat.add_sub_cancel] using h
    nlinarith

lemma tendsto_renewal_shift_zero {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1) {j : ℕ} (hpj : 0 < p j) :
    Tendsto (fun n ↦ renewalMass p (n + j + 1) - renewalMass p n)
      atTop (nhds 0) := by
  let v : ℕ → ℝ := fun n ↦
    renewalMass p (n + j + 1) - renewalMass p n
  have hsquare : Tendsto (fun n ↦ v n ^ 2) atTop (nhds 0) :=
    (summable_renewal_shift_sq hp hs ht hpj).tendsto_atTop_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun n ↦ |v n|) atTop (nhds 0)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsquare
  have heq : ((fun x : ℝ ↦ Real.sqrt x) ∘ fun n ↦ v n ^ 2) =
      fun n ↦ |v n| := by
    funext n
    exact Real.sqrt_sq_eq_abs (v n)
  rw [heq, Real.sqrt_zero] at hsqrt
  exact hsqrt

lemma tendsto_forwardDiff_renewalMass {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1)
    (haper : ∀ q : ℕ,
      (∀ n, 0 < shiftedWeights p n → q ∣ n) → q = 1) :
    Tendsto (forwardDiff (renewalMass p)) atTop (nhds 0) := by
  let support : Set ℕ := {n | 0 < shiftedWeights p n}
  have hgcd : Nat.setGcd support = 1 := by
    apply haper (Nat.setGcd support)
    intro n hn
    exact Nat.setGcd_dvd_of_mem (s := support) hn
  let H : ℕ → Prop := fun k ↦
    Tendsto (fun n ↦ renewalMass p (n + k) - renewalMass p n)
      atTop (nhds 0)
  have hzero : H 0 := by
    simp [H]
  have hgen : ∀ k ∈ support, H k := by
    intro k hk
    have hkpos : 0 < shiftedWeights p k := hk
    cases k with
    | zero => simp [shiftedWeights] at hkpos
    | succ j =>
        simpa [H] using tendsto_renewal_shift_zero hp hs ht
          (by simpa [shiftedWeights] using hkpos)
  have hadd : ∀ a b, H a → H b → H (a + b) := by
    intro a b ha hb
    have hbshift := hb.comp (tendsto_nat_add_const_atTop a)
    have hsum := hbshift.add ha
    convert hsum using 1
    · funext n
      dsimp [H] at ha hb ⊢
      ring_nf
    · simp
  have hclosure : ∀ k ∈ AddSubmonoid.closure support, H k := by
    intro k hk
    exact AddSubmonoid.closure_induction hgen hzero
      (fun a b _ _ ha hb ↦ hadd a b ha hb) hk
  obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge support
  have hNc : N ∈ AddSubmonoid.closure support := hN N le_rfl (by simp [hgcd])
  have hN1c : N + 1 ∈ AddSubmonoid.closure support :=
    hN (N + 1) (Nat.le_succ N) (by simp [hgcd])
  have hbig := hclosure (N + 1) hN1c
  have hsmallShift := (hclosure N hNc).comp (tendsto_nat_add_const_atTop 1)
  have hdiff := hbig.sub hsmallShift
  dsimp [H] at hdiff
  unfold forwardDiff
  convert hdiff using 1
  · funext n
    ring_nf
  · simp

lemma tendsto_renewalMass {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n, p n = 1)
    (haper : ∀ q : ℕ,
      (∀ n, 0 < shiftedWeights p n → q ∣ n) → q = 1) :
    Tendsto (renewalMass p) atTop (nhds (1 / ∑' n, stepTail p n)) := by
  have hrange := renewalMass_nonneg_le_one hp hs ht
  have hdiff := tendsto_forwardDiff_renewalMass hp hs ht haper
  have htail0 : ∀ n, 0 ≤ stepTail p n := stepTail_nonneg hp
  have hid := renewalTailSum_eq_one hs ht
  by_cases hQs : Summable (stepTail p)
  · have hmu : 0 < ∑' n, stepTail p n := by
      have hle : stepTail p 0 ≤ ∑' n, stepTail p n :=
        by simpa using hQs.sum_le_tsum {0} (fun n hn ↦ htail0 n)
      rw [stepTail_zero ht] at hle
      linarith
    exact tendsto_inverse_tsum_of_forwardDiff_and_summable_tail_identity
      (fun n ↦ (hrange n).1) (fun n ↦ (hrange n).2)
      htail0 hQs hmu hid hdiff
  · have hdiv0 : Tendsto
        (fun M ↦ ∑ i ∈ Finset.range M, stepTail p i) atTop atTop :=
      (not_summable_iff_tendsto_nat_atTop_of_nonneg htail0).1 hQs
    have hdiv : Tendsto
        (fun M ↦ ∑ i ∈ Finset.range (M + 1), stepTail p i) atTop atTop :=
      hdiv0.comp (tendsto_nat_add_const_atTop 1)
    have hz := tendsto_zero_of_forwardDiff_and_divergent_tail_identity
      (fun n ↦ (hrange n).1) htail0 hid hdiff hdiv
    rw [tsum_eq_zero_of_not_summable hQs, div_zero]
    exact hz

end Renewal
end Chapter00
