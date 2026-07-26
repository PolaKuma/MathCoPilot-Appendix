import Chapter00.Ergodic.Density
import Chapter02.Common

noncomputable section

open Classical Filter

namespace Chapter02
namespace ZeroDensity

def increasingCutoff (Q : ℕ → ℕ) : ℕ → ℕ
  | 0 => Q 0
  | k + 1 => max (increasingCutoff Q k + 1) (Q (k + 1))

lemma le_increasingCutoff (Q : ℕ → ℕ) (k : ℕ) :
    Q k ≤ increasingCutoff Q k := by
  cases k with
  | zero => rfl
  | succ k => exact le_max_right _ _

lemma increasingCutoff_lt_succ (Q : ℕ → ℕ) (k : ℕ) :
    increasingCutoff Q k < increasingCutoff Q (k + 1) := by
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

lemma increasingCutoff_strictMono (Q : ℕ → ℕ) :
    StrictMono (increasingCutoff Q) :=
  strictMono_nat_of_lt_succ (increasingCutoff_lt_succ Q)

lemma index_le_increasingCutoff (Q : ℕ → ℕ) (k : ℕ) :
    k ≤ increasingCutoff Q k :=
  (increasingCutoff_strictMono Q).id_le k

def cutoffLevel (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  if N 0 ≤ n then Nat.findGreatest (fun k => N k ≤ n) n else 0

lemma cutoffLevel_le (N : ℕ → ℕ) (n : ℕ) : cutoffLevel N n ≤ n := by
  unfold cutoffLevel
  split_ifs
  · exact Nat.findGreatest_le n
  · exact Nat.zero_le n

lemma cutoffLevel_spec (N : ℕ → ℕ) {n : ℕ} (hn : N 0 ≤ n) :
    N (cutoffLevel N n) ≤ n := by
  simp only [cutoffLevel, if_pos hn]
  exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn

lemma le_cutoffLevel (N : ℕ → ℕ) (hmono : Monotone N) (hindex : ∀ k, k ≤ N k)
    {k n : ℕ} (hkn : N k ≤ n) : k ≤ cutoffLevel N n := by
  have hn0 : N 0 ≤ n := (hmono (Nat.zero_le k)).trans hkn
  simp only [cutoffLevel, if_pos hn0]
  exact Nat.le_findGreatest ((hindex k).trans hkn) hkn

lemma cutoffLevel_mono (N : ℕ → ℕ) (hmono : Monotone N)
    (hindex : ∀ k, k ≤ N k) :
    Monotone (cutoffLevel N) := by
  intro m n hmn
  by_cases hm : N 0 ≤ m
  · exact le_cutoffLevel N hmono hindex
      ((cutoffLevel_spec N hm).trans hmn)
  · simp [cutoffLevel, hm]

lemma cutoffLevel_tendsto_atTop (N : ℕ → ℕ) (hmono : Monotone N)
    (hindex : ∀ k, k ≤ N k) :
    Tendsto (cutoffLevel N) atTop atTop := by
  rw [tendsto_atTop]
  intro k
  filter_upwards [Filter.eventually_ge_atTop (N k)] with n hn
  exact le_cutoffLevel N hmono hindex hn

lemma exists_nonnegative_norm_bound (a : ℕ → ℂ)
    (ha : BddAbove (Set.range fun n => ‖a n‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C := by
  rcases bddAbove_def.mp ha with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro n
  exact (hC _ ⟨n, rfl⟩).trans (le_max_left _ _)

lemma cesaro_norm_sq_of_cesaro_norm (a : ℕ → ℂ)
    (ha : BddAbove (Set.range fun n => ‖a n‖))
    (h : cesaroTendsTo (fun n => ‖a n‖) 0) :
    cesaroTendsTo (fun n => ‖a n‖ ^ 2) 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_nonnegative_norm_bound a ha
  unfold cesaroTendsTo seqTendsTo cesaroAverage at h ⊢
  have hnonneg (N : ℕ) :
      0 ≤ (((N + 1 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) := by positivity
  have hle (N : ℕ) :
      (((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2) ≤
        C * (((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N + 1), ‖a n‖) := by
    calc
      _ ≤ (((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N + 1), C * ‖a n‖) := by
        gcongr with n hn
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)
      _ = _ := by
        rw [← Finset.mul_sum]
        ring
  apply squeeze_zero hnonneg hle
  simpa only [mul_zero] using tendsto_const_nhds.mul h

lemma cesaro_norm_of_cesaro_norm_sq (a : ℕ → ℂ)
    (h : cesaroTendsTo (fun n => ‖a n‖ ^ 2) 0) :
    cesaroTendsTo (fun n => ‖a n‖) 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at h ⊢
  let q : ℕ → ℝ := fun N =>
    (((N + 1 : ℕ) : ℝ)⁻¹ *
      ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2)
  have hq0 : Tendsto q atTop (nhds 0) := h
  have hsqrt : Tendsto (fun N => Real.sqrt (q N)) atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hq0
  have hnonneg (N : ℕ) :
      0 ≤ (((N + 1 : ℕ) : ℝ)⁻¹ *
        ∑ n ∈ Finset.range (N + 1), ‖a n‖) := by positivity
  have hle (N : ℕ) :
      (((N + 1 : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (N + 1), ‖a n‖) ≤
        Real.sqrt (q N) := by
    let m : ℕ := N + 1
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range m)
      (fun n => ‖a n‖) (fun _ => 1)
    have hsum1 : ∑ _n ∈ Finset.range m, (1 : ℝ) ^ 2 = m := by simp
    have hsum_nonneg : 0 ≤ ∑ n ∈ Finset.range m, ‖a n‖ ^ 2 := by positivity
    have hsqrt_m : Real.sqrt (m : ℝ) = (Real.sqrt (m : ℝ)) := rfl
    have hmpos : 0 < (m : ℝ) := by positivity
    have hsqrtpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
    have hraw : (∑ n ∈ Finset.range m, ‖a n‖) ≤
        Real.sqrt (∑ n ∈ Finset.range m, ‖a n‖ ^ 2) *
          Real.sqrt (m : ℝ) := by
      simpa [hsum1] using hcs
    rw [show (((N + 1 : ℕ) : ℝ)⁻¹) = (m : ℝ)⁻¹ by rfl]
    have hdiv := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hmpos.le)
    calc
      (m : ℝ)⁻¹ * ∑ n ∈ Finset.range m, ‖a n‖ ≤
          (m : ℝ)⁻¹ *
            (Real.sqrt (∑ n ∈ Finset.range m, ‖a n‖ ^ 2) *
              Real.sqrt (m : ℝ)) := hdiv
      _ = Real.sqrt ((m : ℝ)⁻¹ *
          ∑ n ∈ Finset.range m, ‖a n‖ ^ 2) := by
        rw [Real.sqrt_mul (inv_nonneg.mpr hmpos.le)]
        rw [Real.sqrt_inv (m : ℝ)]
        field_simp [Real.sq_sqrt hmpos.le, hsqrtpos.ne', hm0]
        rw [Real.sq_sqrt hmpos.le]
        ac_rfl
      _ = Real.sqrt (q N) := rfl
  exact squeeze_zero hnonneg hle hsqrt

lemma cesaro_norm_iff_cesaro_norm_sq (a : ℕ → ℂ)
    (ha : BddAbove (Set.range fun n => ‖a n‖)) :
    cesaroTendsTo (fun n => ‖a n‖) 0 ↔
      cesaroTendsTo (fun n => ‖a n‖ ^ 2) 0 :=
  ⟨cesaro_norm_sq_of_cesaro_norm a ha, cesaro_norm_of_cesaro_norm_sq a⟩

lemma tendsto_natInitialDensity_of_lower_upper_eq_zero (J : Set ℕ)
    (hlow : Chapter00.lowerAsymptoticDensity J = 0)
    (hupp : Chapter00.upperAsymptoticDensity J = 0) :
    Tendsto (Chapter00.natInitialDensity J) atTop (nhds 0) := by
  apply tendsto_of_liminf_eq_limsup
  · rwa [← Chapter00.lowerAsymptoticDensity_eq_liminf]
  · rwa [← Chapter00.upperAsymptoticDensity_eq_limsup]
  · exact Chapter00.boundedAbove_of_zero_one atTop
      (fun n => Chapter00.natIntervalDensity_le_one J 0 n)
  · exact Chapter00.boundedBelow_of_zero_one atTop
      (fun n => Chapter00.natIntervalDensity_nonneg J 0 n)

lemma natInitialDensity_threshold_mul_le_cesaroAverage
    (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (ε : ℝ) (N : ℕ) :
    Chapter00.natInitialDensity {n | ε ≤ x n} (N + 1) * ε ≤
      cesaroAverage x N := by
  let s := Finset.range (N + 1)
  let t := s.filter fun n => ε ≤ x n
  have ht_sum : (t.card : ℝ) * ε ≤ ∑ n ∈ t, x n := by
    have hpoint : ∀ n ∈ t, ε ≤ x n := fun n hn => (Finset.mem_filter.mp hn).2
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat,
      Nat.cast_id] using (Finset.sum_le_sum hpoint)
  have hfilter_sum : (∑ n ∈ t, x n) ≤ ∑ n ∈ s, x n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => hx n)
  have hsum : (t.card : ℝ) * ε ≤ ∑ n ∈ s, x n := ht_sum.trans hfilter_sum
  have hdenom : 0 ≤ (((N + 1 : ℕ) : ℝ))⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hdenom
  simpa [Chapter00.natInitialDensity, Chapter00.natIntervalDensity,
    Chapter00.natInterval, cesaroAverage, s, t, div_eq_inv_mul,
    mul_assoc] using hscaled

lemma threshold_density_tendsto_zero
    (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n)
    (h : cesaroTendsTo x 0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (Chapter00.natInitialDensity {n | ε ≤ x n}) atTop (nhds 0) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have hnonneg (N : ℕ) :
      0 ≤ Chapter00.natInitialDensity {n | ε ≤ x n} (N + 1) :=
    Chapter00.natIntervalDensity_nonneg _ _ _
  have hle (N : ℕ) :
      Chapter00.natInitialDensity {n | ε ≤ x n} (N + 1) ≤
        cesaroAverage x N / ε := by
    exact (le_div_iff₀ hε).2
      (natInitialDensity_threshold_mul_le_cesaroAverage x hx ε N)
  apply squeeze_zero hnonneg hle
  unfold cesaroTendsTo seqTendsTo at h
  simpa only [zero_div] using h.div_const ε

lemma exists_zero_density_exceptional_set
    (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (h : cesaroTendsTo x 0) :
    ∃ J : Set ℕ,
      Tendsto (Chapter00.natInitialDensity J) atTop (nhds 0) ∧
      Tendsto x (Filter.principal Jᶜ ⊓ atTop) (nhds 0) := by
  have hthreshold (k : ℕ) :
      Tendsto (Chapter00.natInitialDensity
        {n | (1 : ℝ) / (k + 1 : ℝ) ≤ x n}) atTop (nhds 0) := by
    exact threshold_density_tendsto_zero x hx h (by positivity)
  have hcut : ∀ k : ℕ, ∃ q : ℕ, ∀ n : ℕ, q ≤ n →
      Chapter00.natInitialDensity
          {i | (1 : ℝ) / (k + 1 : ℝ) ≤ x i} n <
        (1 : ℝ) / (k + 1 : ℝ) := by
    intro k
    have hevent := (tendsto_order.mp (hthreshold k)).2
      ((1 : ℝ) / (k + 1 : ℝ)) (by positivity)
    exact Filter.eventually_atTop.mp hevent
  choose Q hQ using hcut
  let N : ℕ → ℕ := increasingCutoff Q
  let L : ℕ → ℕ := cutoffLevel N
  let J : Set ℕ := {n | (1 : ℝ) / (L n + 1 : ℝ) ≤ x n}
  have hNmono : Monotone N := (increasingCutoff_strictMono Q).monotone
  have hNindex : ∀ k, k ≤ N k := index_le_increasingCutoff Q
  have hLmono : Monotone L := cutoffLevel_mono N hNmono hNindex
  have hLtop : Tendsto L atTop atTop := cutoffLevel_tendsto_atTop N hNmono hNindex
  have hrecip : Tendsto (fun n => (1 : ℝ) / (L n + 1 : ℝ))
      atTop (nhds 0) := by
    exact (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1 : ℝ)) atTop (nhds 0)) |>.comp hLtop
  have hdens_le : ∀ᶠ n in atTop,
      Chapter00.natInitialDensity J n ≤ (1 : ℝ) / (L n + 1 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (N 0)] with n hn
    have hNL : N (L n) ≤ n := cutoffLevel_spec N hn
    have hQL : Q (L n) ≤ n := (le_increasingCutoff Q (L n)).trans hNL
    have hthresh := (hQ (L n) n hQL).le
    have hsubset :
        (Chapter00.natInterval 0 n).filter (fun i => i ∈ J) ⊆
          (Chapter00.natInterval 0 n).filter
            (fun i => (1 : ℝ) / (L n + 1 : ℝ) ≤ x i) := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiInterval, hiJ⟩
      apply Finset.mem_filter.mpr
      refine ⟨hiInterval, ?_⟩
      have hin : i ≤ n := by
        have := (Finset.mem_Ico.mp hiInterval).2
        omega
      have hlevel : L i ≤ L n := hLmono hin
      have hrecip_mono : (1 : ℝ) / (L n + 1 : ℝ) ≤
          (1 : ℝ) / (L i + 1 : ℝ) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.succ_le_succ hlevel
      exact hrecip_mono.trans hiJ
    have hdensity_mono : Chapter00.natInitialDensity J n ≤
        Chapter00.natInitialDensity
          {i | (1 : ℝ) / (L n + 1 : ℝ) ≤ x i} n := by
      have hcard := Finset.card_le_card hsubset
      unfold Chapter00.natInitialDensity Chapter00.natIntervalDensity
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg n)
    exact hdensity_mono.trans hthresh
  have hJdensity : Tendsto (Chapter00.natInitialDensity J) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n => Chapter00.natIntervalDensity_nonneg J 0 n
    · exact hdens_le
    · exact hrecip
  refine ⟨J, hJdensity, ?_⟩
  have hrecip_off : Tendsto (fun n => (1 : ℝ) / (L n + 1 : ℝ))
      (Filter.principal Jᶜ ⊓ atTop) (nhds 0) :=
    hrecip.mono_left inf_le_right
  apply squeeze_zero'
  · exact Eventually.of_forall hx
  · rw [inf_comm, Filter.eventually_inf_principal]
    filter_upwards [] with n hnJ
    exact le_of_not_ge hnJ
  · exact hrecip_off

lemma cesaroAverage_le_density_add_tail
    (x : ℕ → ℝ) (J : Set ℕ) (C η : ℝ) (K N : ℕ)
    (hC0 : 0 ≤ C) (hη0 : 0 ≤ η)
    (hxC : ∀ n, x n ≤ C)
    (hsmall : ∀ n, K ≤ n → n ∉ J → x n ≤ η) :
    cesaroAverage x N ≤
      C * Chapter00.natInitialDensity J (N + 1) + η +
        C * (K : ℝ) / (N + 1 : ℝ) := by
  let s := Finset.range (N + 1)
  have hpoint (n : ℕ) : x n ≤
      C * (if n ∈ J then 1 else 0) + η +
        C * (if n < K then 1 else 0) := by
    by_cases hnJ : n ∈ J
    · simp [hnJ]
      split_ifs <;> linarith [hxC n]
    · by_cases hnK : n < K
      · simp [hnJ, hnK]
        linarith [hxC n]
      · simp [hnJ, hnK]
        exact hsmall n (Nat.le_of_not_gt hnK) hnJ
  have hsum := Finset.sum_le_sum (s := s) (fun n _ => hpoint n)
  have hprefix :
      ((s.filter fun n => n < K).card : ℝ) ≤ K := by
    have hsub : (s.filter fun n => n < K) ⊆ Finset.range K := by
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range K)
  have hsum' :
      (∑ n ∈ s, x n) ≤
        C * ((s.filter fun n => n ∈ J).card : ℝ) +
          (N + 1 : ℝ) * η + C * K := by
    have hJsum :
        (∑ n ∈ s, C * (if n ∈ J then (1 : ℝ) else 0)) =
          C * ((s.filter fun n => n ∈ J).card : ℝ) := by
      have hfun : (fun n : ℕ => C * (if n ∈ J then (1 : ℝ) else 0)) =
          fun n => if n ∈ J then C else 0 := by
        funext n
        split_ifs <;> simp_all
      rw [hfun, ← Finset.sum_filter]
      simp
      ring
    have hKsum :
        (∑ n ∈ s, C * (if n < K then (1 : ℝ) else 0)) =
          C * ((s.filter fun n => n < K).card : ℝ) := by
      have hfun : (fun n : ℕ => C * (if n < K then (1 : ℝ) else 0)) =
          fun n => if n < K then C else 0 := by
        funext n
        split_ifs <;> simp_all
      rw [hfun, ← Finset.sum_filter]
      simp
      ring
    calc
      _ ≤ ∑ n ∈ s, (C * (if n ∈ J then 1 else 0) + η +
          C * (if n < K then 1 else 0)) := hsum
      _ = C * ((s.filter fun n => n ∈ J).card : ℝ) +
          (N + 1 : ℝ) * η +
            C * ((s.filter fun n => n < K).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hJsum, hKsum]
        simp [s]
      _ ≤ _ := by gcongr
  have hdenom : 0 ≤ (((N + 1 : ℕ) : ℝ))⁻¹ := by positivity
  have hdenom_ne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum' hdenom
  have hdensity : Chapter00.natInitialDensity J (N + 1) =
      (((N + 1 : ℕ) : ℝ))⁻¹ *
        ((s.filter fun n => n ∈ J).card : ℝ) := by
    simp [Chapter00.natInitialDensity, Chapter00.natIntervalDensity,
      Chapter00.natInterval, s, div_eq_inv_mul]
  rw [hdensity]
  unfold cesaroAverage
  rw [div_eq_inv_mul]
  simp only [Nat.cast_add, Nat.cast_one] at hscaled hdenom_ne ⊢
  convert hscaled using 1 <;> field_simp [hdenom_ne] <;> ring

lemma cesaroTendsTo_zero_of_tendsto_off_zero_density
    (x : ℕ → ℝ) (J : Set ℕ) (C : ℝ)
    (hx0 : ∀ n, 0 ≤ x n) (hC0 : 0 ≤ C) (hxC : ∀ n, x n ≤ C)
    (hJ : Tendsto (Chapter00.natInitialDensity J) atTop (nhds 0))
    (hoff : Tendsto x (Filter.principal Jᶜ ⊓ atTop) (nhds 0)) :
    cesaroTendsTo x 0 := by
  unfold cesaroTendsTo seqTendsTo
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [] with N
    have havg0 : 0 ≤ cesaroAverage x N := by
      unfold cesaroAverage
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hx0 n)
    linarith
  · intro δ hδ
    let η : ℝ := δ / 3
    have hη : 0 < η := by dsimp [η]; linarith
    have hoff_event : ∀ᶠ n in Filter.principal Jᶜ ⊓ atTop, x n < η :=
      (tendsto_order.mp hoff).2 η hη
    rw [inf_comm, Filter.eventually_inf_principal] at hoff_event
    rcases (Filter.eventually_atTop.mp hoff_event) with ⟨K, hK⟩
    have hdens_bound : ∀ᶠ N in atTop,
        Chapter00.natInitialDensity J (N + 1) < δ / (3 * (C + 1)) := by
      have hpos : 0 < δ / (3 * (C + 1)) := by positivity
      exact (Filter.tendsto_add_atTop_iff_nat 1).mpr hJ |>.eventually
        (eventually_lt_nhds hpos)
    have hfinite_tendsto : Tendsto (fun N : ℕ => C * (K : ℝ) / (N + 1 : ℝ))
        atTop (nhds 0) := by
      have hone : Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1 : ℝ))
          atTop (nhds 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun N : ℕ => (1 : ℝ) / (N + 1)) atTop (nhds 0))
      have hc : Tendsto (fun _ : ℕ => C * (K : ℝ)) atTop
          (nhds (C * (K : ℝ))) := tendsto_const_nhds
      simpa [div_eq_mul_inv, one_div, mul_assoc] using hc.mul hone
    have hfinite_bound : ∀ᶠ (N : ℕ) in atTop,
        C * (K : ℝ) / (N + 1 : ℝ) < δ / 3 :=
      (tendsto_order.mp hfinite_tendsto).2 (δ / 3) (by linarith)
    filter_upwards [hdens_bound, hfinite_bound] with N hdens hfinite
    have htail : ∀ n, K ≤ n → n ∉ J → x n ≤ η := by
      intro n hn hnJ
      exact (hK n hn (by simpa using hnJ)).le
    have hbound := cesaroAverage_le_density_add_tail x J C η K N
      hC0 hη.le hxC htail
    have hCdens : C * Chapter00.natInitialDensity J (N + 1) < δ / 3 := by
      rcases hC0.eq_or_lt with hCeq | hCpos
      · simp [← hCeq, hδ]
      · have hmul := mul_lt_mul_of_pos_left hdens hCpos
        have hratio : C * (δ / (3 * (C + 1))) < δ / 3 := by
          field_simp
          nlinarith
        exact hmul.trans hratio
    dsimp [η] at hbound
    linarith

theorem koopmanVonNeumannZeroDensityLemma :
    KoopmanVonNeumannZeroDensityLemma := by
  intro a ha
  constructor
  · intro hmean
    have hsquare := cesaro_norm_sq_of_cesaro_norm a ha hmean
    obtain ⟨J, hJdensity, hnorm⟩ :=
      exists_zero_density_exceptional_set (fun n => ‖a n‖)
        (fun n => norm_nonneg (a n)) hmean
    have hlow : Chapter00.lowerAsymptoticDensity J = 0 := by
      rw [Chapter00.lowerAsymptoticDensity_eq_liminf]
      exact hJdensity.liminf_eq
    have hupp : Chapter00.upperAsymptoticDensity J = 0 := by
      rw [Chapter00.upperAsymptoticDensity_eq_limsup]
      exact hJdensity.limsup_eq
    have haoff : Tendsto a (Filter.principal Jᶜ ⊓ atTop) (nhds 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa using hnorm
    exact ⟨⟨J, hlow, hupp, haoff⟩, hsquare⟩
  · rintro ⟨_, hsquare⟩
    exact cesaro_norm_of_cesaro_norm_sq a hsquare

end ZeroDensity
end Chapter02
