import Chapter00.Common

noncomputable section

open Classical Filter
open scoped BigOperators ENNReal

namespace Chapter00

namespace Renewal

lemma exists_positive_support
    {c : ℕ → ℝ}
    (haper : ∀ q : ℕ, (∀ n, 0 < c n → q ∣ n) → q = 1) :
    ∃ n : ℕ, n ≠ 0 ∧ 0 < c n := by
  by_contra h
  push_neg at h
  have hdiv : ∀ n, 0 < c n → 0 ∣ n := by
    intro n hn
    have hnzero : n = 0 := by
      by_contra hn0
      exact (not_lt_of_ge (h n hn0)) hn
    simp [hnzero]
  have := haper 0 hdiv
  omega

lemma coefficient_zero_lt_one
    {c : ℕ → ℝ}
    (haper : ∀ q : ℕ, (∀ n, 0 < c n → q ∣ n) → q = 1)
    (hsum : (∑' n : ℕ, ENNReal.ofReal (c n)) = 1) :
    c 0 < 1 := by
  obtain ⟨n, hn0, hn⟩ := exists_positive_support haper
  have hpair :
      ∑ i ∈ ({0, n} : Finset ℕ), ENNReal.ofReal (c i) ≤
        ∑' i : ℕ, ENNReal.ofReal (c i) :=
    ENNReal.sum_le_tsum ({0, n} : Finset ℕ)
  rw [hsum] at hpair
  have hpair' : ENNReal.ofReal (c 0) + ENNReal.ofReal (c n) ≤ 1 := by
    rw [Finset.sum_insert (by simpa using hn0.symm), Finset.sum_singleton] at hpair
    exact hpair
  have hnpos : 0 < ENNReal.ofReal (c n) := ENNReal.ofReal_pos.2 hn
  apply ENNReal.ofReal_lt_one.1
  exact (ENNReal.lt_add_right ENNReal.ofReal_ne_top hnpos.ne').trans_le hpair'

lemma summable_of_ofReal_tsum_ne_top
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hsum : (∑' n : ℕ, ENNReal.ofReal (f n)) ≠ ⊤) :
    Summable f := by
  have h := ENNReal.summable_toReal hsum
  simpa only [ENNReal.toReal_ofReal (hf _)] using h

lemma tsum_eq_one_of_ofReal_tsum_eq_one
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hsum : (∑' n : ℕ, ENNReal.ofReal (f n)) = 1) :
    ∑' n : ℕ, f n = 1 := by
  have hfinite : (∑' n : ℕ, ENNReal.ofReal (f n)) ≠ ⊤ := by simp [hsum]
  have hs : Summable f := summable_of_ofReal_tsum_ne_top hf hfinite
  have h := ENNReal.ofReal_tsum_of_nonneg hf hs
  rw [hsum] at h
  have hnonneg : 0 ≤ ∑' n : ℕ, f n := tsum_nonneg hf
  apply_fun ENNReal.toReal at h
  simpa [ENNReal.toReal_ofReal hnonneg] using h

def normalizedStepWeights (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  c (n + 1) / (1 - c 0)

lemma normalizedStepWeights_nonneg
    {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 < 1) (n : ℕ) :
    0 ≤ normalizedStepWeights c n := by
  unfold normalizedStepWeights
  exact div_nonneg (hc _) (sub_nonneg.mpr hc0.le)

lemma summable_normalizedStepWeights
    {c : ℕ → ℝ} (hs : Summable c) :
    Summable (normalizedStepWeights c) := by
  unfold normalizedStepWeights
  exact ((summable_nat_add_iff 1).2 hs).div_const _

lemma tsum_normalizedStepWeights
    {c : ℕ → ℝ} (hc0 : c 0 < 1) (hs : Summable c)
    (ht : ∑' n : ℕ, c n = 1) :
    ∑' n : ℕ, normalizedStepWeights c n = 1 := by
  rw [show normalizedStepWeights c = fun n ↦ c (n + 1) / (1 - c 0) from rfl,
    tsum_div_const]
  have htail : ∑' n : ℕ, c (n + 1) = 1 - c 0 := by
    have hsplit := hs.tsum_eq_zero_add
    rw [ht] at hsplit
    linarith
  rw [htail]
  exact div_self (sub_ne_zero.mpr hc0.ne')

def renewalMass (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ∑ j ∈ Finset.range (n + 1), p j * renewalMass p (n - j)

@[simp] lemma renewalMass_zero (p : ℕ → ℝ) : renewalMass p 0 = 1 := by
  simp [renewalMass]

lemma renewalMass_succ (p : ℕ → ℝ) (n : ℕ) :
    renewalMass p (n + 1) =
      ∑ j ∈ Finset.range (n + 1), p j * renewalMass p (n - j) := by
  rw [renewalMass]

lemma renewalMass_nonneg_le_one
    {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (hs : Summable p)
    (ht : ∑' n : ℕ, p n = 1) (n : ℕ) :
    0 ≤ renewalMass p n ∧ renewalMass p n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [renewalMass_succ]
          constructor
          · exact Finset.sum_nonneg fun j hj ↦
              mul_nonneg (hp j) (ih (n - j) (by omega)).1
          · calc
              ∑ j ∈ Finset.range (n + 1), p j * renewalMass p (n - j) ≤
                  ∑ j ∈ Finset.range (n + 1), p j := by
                    apply Finset.sum_le_sum
                    intro j hj
                    exact mul_le_of_le_one_right (hp j) (ih (n - j) (by omega)).2
              _ ≤ ∑' j : ℕ, p j := hs.sum_le_tsum _ (fun j _ ↦ hp j)
              _ = 1 := ht

def stepTail (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, p (n + k)

lemma stepTail_zero {p : ℕ → ℝ} (ht : ∑' n : ℕ, p n = 1) :
    stepTail p 0 = 1 := by
  simpa [stepTail] using ht

lemma stepTail_nonneg {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) (k : ℕ) :
    0 ≤ stepTail p k := by
  exact tsum_nonneg fun n ↦ hp _

lemma stepTail_succ {p : ℕ → ℝ} (hs : Summable p) (k : ℕ) :
    stepTail p k = p k + stepTail p (k + 1) := by
  have hshift : Summable (fun n ↦ p (n + k)) := (summable_nat_add_iff k).2 hs
  have h := hshift.tsum_eq_zero_add
  simpa only [stepTail, zero_add, add_assoc, add_comm, add_left_comm] using h

def renewalTailSum (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), renewalMass p (n - k) * stepTail p k

lemma renewalTailSum_eq_one
    {p : ℕ → ℝ} (hs : Summable p) (ht : ∑' n : ℕ, p n = 1)
    (n : ℕ) : renewalTailSum p n = 1 := by
  induction n with
  | zero => simp [renewalTailSum, stepTail_zero ht]
  | succ n ih =>
      have hsplit :
          renewalTailSum p (n + 1) =
            (∑ k ∈ Finset.range (n + 1),
              renewalMass p (n - k) * stepTail p (k + 1)) + renewalMass p (n + 1) := by
        rw [renewalTailSum, Finset.sum_range_succ']
        simp only [renewalMass_zero, stepTail_zero ht, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        omega
      rw [hsplit]
      have htail : ∀ k, stepTail p (k + 1) = stepTail p k - p k := by
        intro k
        linarith [stepTail_succ hs k]
      simp_rw [htail]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      have hrec :
          renewalMass p (n + 1) =
            ∑ k ∈ Finset.range (n + 1), renewalMass p (n - k) * p k := by
        rw [renewalMass_succ]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hrec]
      ring_nf
      simpa [renewalTailSum, Nat.add_comm] using ih

lemma exists_finite_support_gcd_one
    {w : ℕ → ℝ}
    (haper : ∀ q : ℕ, (∀ n, 0 < w n → q ∣ n) → q = 1) :
    ∃ S : Finset ℕ, (∀ n ∈ S, 0 < w n) ∧ S.gcd id = 1 := by
  have aux : ∀ g : ℕ, 0 < g → ∀ S : Finset ℕ,
      S.gcd id = g → (∀ n ∈ S, 0 < w n) →
        ∃ T : Finset ℕ, (∀ n ∈ T, 0 < w n) ∧ T.gcd id = 1 := by
    intro g
    induction g using Nat.strong_induction_on with
    | h g ih =>
        intro hg S hSg hSw
        by_cases hg1 : g = 1
        · exact ⟨S, hSw, hSg.trans hg1⟩
        · have hnotall : ¬ ∀ n, 0 < w n → g ∣ n := by
            intro hall
            exact hg1 (haper g hall)
          push_neg at hnotall
          obtain ⟨n, hwn, hndiv⟩ := hnotall
          let g' := Nat.gcd n g
          have hg'pos : 0 < g' := Nat.gcd_pos_of_pos_right n hg
          have hg'le : g' ≤ g := Nat.le_of_dvd hg (Nat.gcd_dvd_right n g)
          have hg'ne : g' ≠ g := by
            intro heq
            exact hndiv (Nat.gcd_eq_right_iff_dvd.1 heq)
          have hg'lt : g' < g := lt_of_le_of_ne hg'le hg'ne
          apply ih g' hg'lt hg'pos (insert n S)
          · simp [g', hSg, gcd_eq_nat_gcd]
          · intro m hm
            rcases Finset.mem_insert.1 hm with rfl | hmS
            · exact hwn
            · exact hSw m hmS
  obtain ⟨n, hn0, hwn⟩ := exists_positive_support haper
  have hngcd : ({n} : Finset ℕ).gcd id = n := by simp
  exact aux n (Nat.pos_of_ne_zero hn0) {n} hngcd (by simpa)

def normalizedForcing (c d : ℕ → ℝ) (n : ℕ) : ℝ :=
  d n / (1 - c 0)

def renewalResponse (p e : ℕ → ℝ) : ℕ → ℝ
  | 0 => e 0
  | n + 1 => e (n + 1) +
      ∑ j ∈ Finset.range (n + 1), p j * renewalResponse p e (n - j)

@[simp] lemma renewalResponse_zero (p e : ℕ → ℝ) :
    renewalResponse p e 0 = e 0 := by simp [renewalResponse]

lemma renewalResponse_succ (p e : ℕ → ℝ) (n : ℕ) :
    renewalResponse p e (n + 1) = e (n + 1) +
      ∑ j ∈ Finset.range (n + 1), p j * renewalResponse p e (n - j) := by
  rw [renewalResponse]

lemma normalized_renewal_recurrence
    {c d u : ℕ → ℝ} (hc0 : c 0 < 1)
    (hrec : ∀ n, u n = d n +
      (Finset.range (n + 1)).sum fun j ↦ c j * u (n - j)) :
    u 0 = normalizedForcing c d 0 ∧
      ∀ n, u (n + 1) = normalizedForcing c d (n + 1) +
        ∑ j ∈ Finset.range (n + 1),
          normalizedStepWeights c j * u (n - j) := by
  have ha : 1 - c 0 ≠ 0 := sub_ne_zero.mpr hc0.ne'
  constructor
  · have h := hrec 0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.zero_sub, mul_eq_mul_left_iff] at h
    unfold normalizedForcing
    field_simp
    linarith
  · intro n
    have h := hrec (n + 1)
    rw [Finset.sum_range_succ'] at h
    simp only [Nat.add_sub_add_right, Nat.sub_zero] at h
    unfold normalizedForcing normalizedStepWeights
    field_simp
    rw [Finset.mul_sum]
    simp_rw [mul_div_cancel₀ _ ha]
    linarith

lemma eq_renewalResponse_of_recurrence
    {p e u : ℕ → ℝ}
    (h0 : u 0 = e 0)
    (hrec : ∀ n, u (n + 1) = e (n + 1) +
      ∑ j ∈ Finset.range (n + 1), p j * u (n - j)) :
    u = renewalResponse p e := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa using h0
      | succ n =>
          rw [hrec, renewalResponse_succ]
          apply congrArg (e (n + 1) + ·)
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih (n - j) (by omega)]

def forwardDiff (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1) - a n

lemma tendsto_nat_add_const_atTop (k : ℕ) :
    Tendsto (fun n : ℕ ↦ n + k) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

lemma tendsto_nat_sub_const_atTop (k : ℕ) :
    Tendsto (fun n : ℕ ↦ n - k) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b + k)] with n hn
  omega

lemma tendsto_add_shift_sub_self_of_forwardDiff
    {a : ℕ → ℝ}
    (hdiff : Tendsto (forwardDiff a) atTop (nhds 0)) (k : ℕ) :
    Tendsto (fun n ↦ a (n + k) - a n) atTop (nhds 0) := by
  induction k with
  | zero => simpa using tendsto_const_nhds
  | succ k ih =>
      have hfirst : Tendsto (fun n ↦ forwardDiff a (n + k)) atTop (nhds 0) :=
        hdiff.comp (tendsto_nat_add_const_atTop k)
      have hadd := hfirst.add ih
      convert hadd using 1
      · funext n
        simp only [forwardDiff]
        ring
      · ring

lemma tendsto_self_sub_sub_shift_of_forwardDiff
    {a : ℕ → ℝ}
    (hdiff : Tendsto (forwardDiff a) atTop (nhds 0)) (k : ℕ) :
    Tendsto (fun n ↦ a n - a (n - k)) atTop (nhds 0) := by
  have h := (tendsto_add_shift_sub_self_of_forwardDiff hdiff k).comp
    (tendsto_nat_sub_const_atTop k)
  apply h.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  simp [Function.comp_apply, Nat.sub_add_cancel hn]

lemma eventually_finset_forall
    {X Y : Type*} {l : Filter Y} (s : Finset X) (P : X → Y → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in l, P x y) :
    ∀ᶠ y in l, ∀ x ∈ s, P x y := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      filter_upwards [h x (by simp), ih (fun z hz ↦ h z (by simp [hz]))] with y hxy hsy
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hzs
      · exact hxy
      · exact hsy z hzs

lemma tendsto_zero_of_forwardDiff_and_divergent_tail_identity
    {a Q : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n)
    (hQ : ∀ n, 0 ≤ Q n)
    (hid : ∀ n, ∑ i ∈ Finset.range (n + 1), a (n - i) * Q i = 1)
    (hdiff : Tendsto (forwardDiff a) atTop (nhds 0))
    (hdiv : Tendsto (fun M ↦ ∑ i ∈ Finset.range (M + 1), Q i) atTop atTop) :
    Tendsto a atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevM := tendsto_atTop.1 hdiv (4 / ε)
  rw [eventually_atTop] at hevM
  obtain ⟨M, hM⟩ := hevM
  let S := ∑ i ∈ Finset.range (M + 1), Q i
  have hS : 4 / ε ≤ S := hM M le_rfl
  have hSpos : 0 < S := lt_of_lt_of_le (div_pos (by norm_num) hε) hS
  have hshift : ∀ i ∈ Finset.range (M + 1),
      ∀ᶠ n in atTop, |a n - a (n - i)| < ε / 2 := by
    intro i hi
    have ht := tendsto_self_sub_sub_shift_of_forwardDiff hdiff i
    rw [Metric.tendsto_atTop] at ht
    obtain ⟨N, hN⟩ := ht (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa [Real.dist_eq] using hN n hn
  have hall := eventually_finset_forall (Finset.range (M + 1))
    (fun i n ↦ |a n - a (n - i)| < ε / 2) hshift
  have hboth := hall.and (eventually_ge_atTop M)
  rw [eventually_atTop] at hboth
  obtain ⟨N, hN⟩ := hboth
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨hnshift, hnM⟩ := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha n)]
  have hterm : ∀ i ∈ Finset.range (M + 1),
      a n * Q i ≤ a (n - i) * Q i + (ε / 2) * Q i := by
    intro i hi
    have hiabs := hnshift i hi
    have hiineq : a n ≤ a (n - i) + ε / 2 := by
      linarith [le_abs_self (a n - a (n - i))]
    simpa [add_mul] using mul_le_mul_of_nonneg_right hiineq (hQ i)
  have hsum_le : a n * S ≤ 1 + (ε / 2) * S := by
    calc
      a n * S = ∑ i ∈ Finset.range (M + 1), a n * Q i := by
        simp [S, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (M + 1),
          (a (n - i) * Q i + (ε / 2) * Q i) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range (M + 1), a (n - i) * Q i) +
          (ε / 2) * S := by simp [S, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 1 + (ε / 2) * S := by
        gcongr
        calc
          ∑ i ∈ Finset.range (M + 1), a (n - i) * Q i ≤
              ∑ i ∈ Finset.range (n + 1), a (n - i) * Q i := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro i hi
                  simp only [Finset.mem_range] at hi ⊢
                  omega
                · intro i hi hinot
                  exact mul_nonneg (ha _) (hQ _)
          _ = 1 := hid n
  have hinv : 1 / S ≤ ε / 4 := by
    apply (div_le_iff₀ hSpos).2
    have hmul := mul_le_mul_of_nonneg_left hS (div_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 4))
    field_simp at hmul ⊢
    nlinarith
  have ha_le : a n ≤ 1 / S + ε / 2 := by
    calc
      a n ≤ (1 + (ε / 2) * S) / S := (le_div_iff₀ hSpos).2 hsum_le
      _ = 1 / S + ε / 2 := by field_simp
  linarith

lemma tendsto_inverse_tsum_of_forwardDiff_and_summable_tail_identity
    {a Q : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hQ : ∀ n, 0 ≤ Q n) (hQs : Summable Q)
    (hμ : 0 < ∑' n, Q n)
    (hid : ∀ n, ∑ i ∈ Finset.range (n + 1), a (n - i) * Q i = 1)
    (hdiff : Tendsto (forwardDiff a) atTop (nhds 0)) :
    Tendsto a atTop (nhds (1 / ∑' n, Q n)) := by
  let μ := ∑' n, Q n
  have hμpos : 0 < μ := hμ
  rw [Metric.tendsto_atTop]
  intro ε hε
  let η := ε * μ / 4
  have hη : 0 < η := by positivity
  have hsum_tendsto : Tendsto (fun M ↦ ∑ i ∈ Finset.range (M + 1), Q i)
      atTop (nhds μ) := by
    simpa [μ, Function.comp_def] using
      hQs.tendsto_sum_tsum_nat.comp (tendsto_nat_add_const_atTop 1)
  rw [Metric.tendsto_atTop] at hsum_tendsto
  obtain ⟨M, hM⟩ := hsum_tendsto η hη
  let S := ∑ i ∈ Finset.range (M + 1), Q i
  have hSle : S ≤ μ := by
    exact hQs.sum_le_tsum _ (fun i _ ↦ hQ i)
  have htail : μ - S < η := by
    have hd := hM M le_rfl
    rw [Real.dist_eq] at hd
    change |S - μ| < η at hd
    linarith [neg_le_abs (S - μ)]
  let δ := ε * μ / (4 * (μ + 1))
  have hδ : 0 < δ := by positivity
  have hshift : ∀ i ∈ Finset.range (M + 1),
      ∀ᶠ n in atTop, |a n - a (n - i)| < δ := by
    intro i hi
    have ht := tendsto_self_sub_sub_shift_of_forwardDiff hdiff i
    rw [Metric.tendsto_atTop] at ht
    obtain ⟨N, hN⟩ := ht δ hδ
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa [Real.dist_eq] using hN n hn
  have hall := eventually_finset_forall (Finset.range (M + 1))
    (fun i n ↦ |a n - a (n - i)| < δ) hshift
  have hboth := hall.and (eventually_ge_atTop M)
  rw [eventually_atTop] at hboth
  obtain ⟨N, hN⟩ := hboth
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨hnshift, hnM⟩ := hN n hn
  let P := ∑ i ∈ Finset.range (M + 1), a (n - i) * Q i
  have hPclose : |a n * S - P| ≤ δ * S := by
    have habs :
        |∑ i ∈ Finset.range (M + 1), (a n - a (n - i)) * Q i| ≤
          ∑ i ∈ Finset.range (M + 1), |a n - a (n - i)| * Q i := by
      calc
        |∑ i ∈ Finset.range (M + 1), (a n - a (n - i)) * Q i| ≤
            ∑ i ∈ Finset.range (M + 1), |(a n - a (n - i)) * Q i| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.range (M + 1), |a n - a (n - i)| * Q i := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [abs_mul, abs_of_nonneg (hQ i)]
    have hstrict :
        ∑ i ∈ Finset.range (M + 1), |a n - a (n - i)| * Q i ≤
          ∑ i ∈ Finset.range (M + 1), δ * Q i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (le_of_lt (hnshift i hi)) (hQ i)
    have heq : a n * S - P =
        ∑ i ∈ Finset.range (M + 1), (a n - a (n - i)) * Q i := by
      simp [S, P, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul]
    rw [heq]
    exact habs.trans (by simpa [S, Finset.mul_sum] using hstrict)
  have hP_le_one : P ≤ 1 := by
    calc
      P ≤ ∑ i ∈ Finset.range (n + 1), a (n - i) * Q i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_range] at hi ⊢
          omega
        · intro i hi hinot
          exact mul_nonneg (ha _) (hQ _)
      _ = 1 := hid n
  have hone_sub_P : 1 - P ≤ μ - S := by
    let R := Finset.range (n + 1) \ Finset.range (M + 1)
    have hsubset : Finset.range (M + 1) ⊆ Finset.range (n + 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    have hdecomp : P + ∑ i ∈ R, a (n - i) * Q i = 1 := by
      rw [← hid n]
      dsimp only [P]
      have hs := Finset.sum_sdiff hsubset (f := fun i ↦ a (n - i) * Q i)
      simpa [R, add_comm] using hs
    have hR : ∑ i ∈ R, a (n - i) * Q i ≤ μ - S := by
      have hterm : ∑ i ∈ R, a (n - i) * Q i ≤ ∑ i ∈ R, Q i := by
        apply Finset.sum_le_sum
        intro i hi
        simpa using mul_le_of_le_one_left (hQ i) (ha1 _)
      have hQrange : S + ∑ i ∈ R, Q i ≤ μ := by
        dsimp only [S]
        have hs := Finset.sum_sdiff hsubset (f := Q)
        calc
          ∑ i ∈ Finset.range (M + 1), Q i + ∑ i ∈ R, Q i =
              ∑ i ∈ Finset.range (n + 1), Q i := by simpa [R, add_comm] using hs
          _ ≤ μ := hQs.sum_le_tsum _ (fun i _ ↦ hQ i)
      linarith
    linarith
  have hscaled : |μ * a n - 1| < ε * μ := by
    have htail_nonneg : 0 ≤ μ - S := sub_nonneg.mpr hSle
    have hbound : |μ * a n - 1| ≤
        (μ - S) + |a n * S - P| + (1 - P) := by
      have haμ : 0 ≤ (μ - S) * a n := mul_nonneg htail_nonneg (ha n)
      have haμ_le : (μ - S) * a n ≤ μ - S :=
        mul_le_of_le_one_right htail_nonneg (ha1 n)
      calc
        |μ * a n - 1| = |(μ - S) * a n + (a n * S - P) - (1 - P)| := by ring_nf
        _ ≤ |(μ - S) * a n| + |a n * S - P| + |1 - P| := by
          calc
            _ ≤ |(μ - S) * a n + (a n * S - P)| + |1 - P| := abs_sub _ _
            _ ≤ (|(μ - S) * a n| + |a n * S - P|) + |1 - P| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ (μ - S) + |a n * S - P| + (1 - P) := by
          rw [abs_of_nonneg haμ, abs_of_nonneg (sub_nonneg.mpr hP_le_one)]
          gcongr
    have hδS : δ * S < η := by
      have hfrac : μ / (μ + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
      calc
        δ * S ≤ δ * μ := mul_le_mul_of_nonneg_left hSle hδ.le
        _ = η * (μ / (μ + 1)) := by
          dsimp [δ, η]
          field_simp
          <;> ring
        _ < η := by simpa using mul_lt_mul_of_pos_left hfrac hη
    calc
      |μ * a n - 1| ≤ (μ - S) + |a n * S - P| + (1 - P) := hbound
      _ < η + η + η := by linarith
      _ < ε * μ := by dsimp [η]; nlinarith [mul_pos hε hμpos]
  rw [Real.dist_eq]
  have heq : a n - 1 / μ = (μ * a n - 1) / μ := by field_simp
  rw [heq, abs_div, abs_of_pos hμpos]
  exact (div_lt_iff₀ hμpos).2 hscaled

lemma sum_forwardDiff_reverse
    (a : ℕ → ℝ) {M n : ℕ} (hMn : M ≤ n) :
    ∑ i ∈ Finset.range (M + 1), forwardDiff a (n - i) =
      a (n + 1) - a (n - M) := by
  induction M with
  | zero => simp [forwardDiff]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      simp only [forwardDiff]
      have hsub : n - (M + 1) + 1 = n - M := by omega
      rw [hsub]
      ring

lemma tendsto_forwardDiff_zero_of_secondDiff_zero
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hsecond : Tendsto (forwardDiff (forwardDiff a)) atTop (nhds 0)) :
    Tendsto (forwardDiff a) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M : ℕ, hM0 : 4 / ε < M⟩ := exists_nat_gt (4 / ε)
  have hM : 4 / ε < (M + 1 : ℕ) := by
    exact hM0.trans_le (by exact_mod_cast Nat.le_succ M)
  have hMpos : (0 : ℝ) < M + 1 := by positivity
  have hinvM : 1 / (M + 1 : ℝ) < ε / 4 := by
    rw [one_div_lt hMpos (by positivity : (0 : ℝ) < ε / 4)]
    simpa [Nat.cast_add, Nat.cast_one] using hM
  have hshift : ∀ i ∈ Finset.range (M + 1),
      ∀ᶠ n in atTop,
        |forwardDiff a n - forwardDiff a (n - i)| < ε / 2 := by
    intro i hi
    have ht := tendsto_self_sub_sub_shift_of_forwardDiff hsecond i
    rw [Metric.tendsto_atTop] at ht
    obtain ⟨N, hN⟩ := ht (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa [Real.dist_eq] using hN n hn
  have hall := eventually_finset_forall (Finset.range (M + 1))
    (fun i n ↦ |forwardDiff a n - forwardDiff a (n - i)| < ε / 2) hshift
  have hboth := hall.and (eventually_ge_atTop M)
  rw [eventually_atTop] at hboth
  obtain ⟨N, hN⟩ := hboth
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨hnshift, hnM⟩ := hN n hn
  let T := ∑ i ∈ Finset.range (M + 1), forwardDiff a (n - i)
  have hT : |T| ≤ 1 := by
    dsimp only [T]
    rw [sum_forwardDiff_reverse a hnM]
    rw [abs_le]
    constructor <;> linarith [ha (n + 1), ha1 (n + 1), ha (n - M), ha1 (n - M)]
  have hclose : |(M + 1 : ℝ) * forwardDiff a n - T| ≤
      (M + 1 : ℝ) * (ε / 2) := by
    have habs :
        |∑ i ∈ Finset.range (M + 1),
          (forwardDiff a n - forwardDiff a (n - i))| ≤
          ∑ i ∈ Finset.range (M + 1),
            |forwardDiff a n - forwardDiff a (n - i)| :=
      Finset.abs_sum_le_sum_abs _ _
    have hsum :
        ∑ i ∈ Finset.range (M + 1),
            |forwardDiff a n - forwardDiff a (n - i)| ≤
          ∑ i ∈ Finset.range (M + 1), ε / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (hnshift i hi)
    have heq : (M + 1 : ℝ) * forwardDiff a n - T =
        ∑ i ∈ Finset.range (M + 1),
          (forwardDiff a n - forwardDiff a (n - i)) := by
      simp [T, Finset.sum_sub_distrib]
    rw [heq]
    exact habs.trans (hsum.trans_eq (by simp))
  have hscaled : |(M + 1 : ℝ) * forwardDiff a n| ≤
      1 + (M + 1 : ℝ) * (ε / 2) := by
    calc
      _ = |((M + 1 : ℝ) * forwardDiff a n - T) + T| := by ring_nf
      _ ≤ |(M + 1 : ℝ) * forwardDiff a n - T| + |T| := abs_add_le _ _
      _ ≤ (M + 1 : ℝ) * (ε / 2) + 1 := add_le_add hclose hT
      _ = 1 + (M + 1 : ℝ) * (ε / 2) := by ring
  rw [abs_mul, abs_of_pos hMpos] at hscaled
  rw [Real.dist_eq, sub_zero]
  have hb : |forwardDiff a n| ≤ 1 / (M + 1 : ℝ) + ε / 2 := by
    calc
      |forwardDiff a n| ≤
          (1 + (M + 1 : ℝ) * (ε / 2)) / (M + 1 : ℝ) :=
        (le_div_iff₀ hMpos).2 (by simpa [mul_comm] using hscaled)
      _ = 1 / (M + 1 : ℝ) + ε / 2 := by field_simp
  linarith

end Renewal

end Chapter00
