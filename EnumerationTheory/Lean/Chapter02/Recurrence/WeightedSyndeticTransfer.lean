import Chapter02.Recurrence.ForwardKroneckerBohr

open Classical Filter Set
open scoped BigOperators

noncomputable section

namespace Chapter02.WeightedSyndeticTransfer

open BohrWeightedUniform

/-- A nonnegative weight which is exponentially small below a structured
threshold, exponentially large on one point in every bounded block, and
which kills the bounded error in translated Cesàro mean transfers a strict
superlevel set from the structured sequence to the original one. -/
theorem isSyndetic_superlevel_of_weighted_error
    (a b : ℕ → ℝ) (w : ℕ → ℂ)
    (c T γ C ρ σ : ℝ) (k L : ℕ)
    (hγ : 0 < γ) (hC : 0 ≤ C)
    (hρ : 0 ≤ ρ) (hσ : 0 < σ)
    (hL : 0 < L)
    (hthreshold : c + γ ≤ T)
    (hw_nonneg : ∀ n, 0 ≤ (w n).re)
    (herror : ∀ n, |a n - b n| ≤ C)
    (hsmall : ∀ n, b n ≤ T → (w n).re ≤ ρ ^ k)
    (hreturn : ∀ i : ℕ, ∃ n : ℕ,
      T < b n ∧ σ ^ k ≤ (w n).re ∧ i ≤ n ∧ n < i + L)
    (hratio : (L : ℝ) * C * ρ ^ k < γ * σ ^ k / 2)
    (hzero : HasUniformComplexCesaroZero
      (fun n ↦ w n * ((a n - b n : ℝ) : ℂ))) :
    IsSyndetic {n : ℕ | a n > c} := by
  let ζ : ℝ := γ * σ ^ k / (4 * (L : ℝ))
  have hζ : 0 < ζ := by
    dsimp [ζ]
    positivity
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.1 (hzero ζ hζ)
  let K : ℕ := N₀ + 1
  let Q : ℕ := K * L
  have hK : 0 < K := by
    dsimp [K]
    omega
  have hQ : 0 < Q := Nat.mul_pos hK hL
  refine ⟨Q, hQ, ?_⟩
  intro i
  by_contra hnone
  push_neg at hnone
  let p : ℕ → ℕ := fun j ↦ Classical.choose (hreturn (i + j * L))
  have hp_high (j : ℕ) : T < b (p j) :=
    (Classical.choose_spec (hreturn (i + j * L))).1
  have hp_floor (j : ℕ) : σ ^ k ≤ (w (p j)).re :=
    (Classical.choose_spec (hreturn (i + j * L))).2.1
  have hp_lower (j : ℕ) : i + j * L ≤ p j :=
    (Classical.choose_spec (hreturn (i + j * L))).2.2.1
  have hp_upper (j : ℕ) : p j < i + j * L + L :=
    (Classical.choose_spec (hreturn (i + j * L))).2.2.2
  let r : ℕ → ℕ := fun j ↦ p j - i
  have hp_from_i (j : ℕ) : i ≤ p j :=
    (Nat.le_add_right i (j * L)).trans (hp_lower j)
  have hr_eq (j : ℕ) : i + r j = p j :=
    Nat.add_sub_of_le (hp_from_i j)
  have hr_lt (j : ℕ) (hj : j ∈ Finset.range K) : r j < Q := by
    have hjK : j < K := Finset.mem_range.mp hj
    have hmul : (j + 1) * L ≤ K * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt hjK)
    have hpQ : p j < i + Q := by
      calc
        p j < i + j * L + L := hp_upper j
        _ = i + (j + 1) * L := by
          simp [Nat.add_mul, Nat.add_assoc]
        _ ≤ i + K * L := Nat.add_le_add_left hmul i
        _ = i + Q := by rfl
    have : i + r j < i + Q := by
      rw [hr_eq j]
      exact hpQ
    omega
  have hr_inj : Set.InjOn r (Finset.range K) := by
    intro j hj l hl hjl
    by_contra hne
    have horder : j < l ∨ l < j := by omega
    rcases horder with hjl' | hlj'
    · have hsep : p j < p l := by
        have hmul : (j + 1) * L ≤ l * L :=
          Nat.mul_le_mul_right L (Nat.succ_le_of_lt hjl')
        calc
          p j < i + j * L + L := hp_upper j
          _ = i + (j + 1) * L := by
            simp [Nat.add_mul, Nat.add_assoc]
          _ ≤ i + l * L := Nat.add_le_add_left hmul i
          _ ≤ p l := hp_lower l
      have hp_eq : p j = p l := by
        rw [← hr_eq j, ← hr_eq l, hjl]
      exact (ne_of_lt hsep) hp_eq
    · have hsep : p l < p j := by
        have hmul : (l + 1) * L ≤ j * L :=
          Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlj')
        calc
          p l < i + l * L + L := hp_upper l
          _ = i + (l + 1) * L := by
            simp [Nat.add_mul, Nat.add_assoc]
          _ ≤ i + j * L := Nat.add_le_add_left hmul i
          _ ≤ p j := hp_lower j
      have hp_eq : p l = p j := by
        rw [← hr_eq l, ← hr_eq j, hjl]
      exact (ne_of_lt hsep) hp_eq
  let R : Finset ℕ := (Finset.range K).image r
  have hRsubset : R ⊆ Finset.range Q := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (hr_lt j hj)
  have hRcard : R.card = K := by
    dsimp [R]
    simpa using (Finset.card_image_iff.mpr hr_inj)
  have ha_block (n : ℕ) (hn : n ∈ Finset.range Q) :
      a (i + n) ≤ c := by
    apply le_of_not_gt
    intro ha
    have hnot := hnone (i + n) ha (Nat.le_add_right i n)
    have hnQ : n < Q := Finset.mem_range.mp hn
    exact (not_lt_of_ge hnot) (by omega)
  have hpoint (n : ℕ) (hn : n ∈ Finset.range Q) :
      (w (i + n)).re * (a (i + n) - b (i + n)) ≤
        C * ρ ^ k -
          if n ∈ R then γ * σ ^ k else 0 := by
    have hw0 := hw_nonneg (i + n)
    have ha := ha_block n hn
    by_cases hnR : n ∈ R
    · obtain ⟨j, hj, hr⟩ := Finset.mem_image.mp hnR
      have hn_eq : i + n = p j := by
        rw [← hr, hr_eq j]
      have hbhigh : T < b (i + n) := by
        rw [hn_eq]
        exact hp_high j
      have hwfloor : σ ^ k ≤ (w (i + n)).re := by
        rw [hn_eq]
        exact hp_floor j
      have he : a (i + n) - b (i + n) ≤ -γ := by
        linarith
      have hmul1 :
          (w (i + n)).re * (a (i + n) - b (i + n)) ≤
            (w (i + n)).re * (-γ) :=
        mul_le_mul_of_nonneg_left he hw0
      have hmul2 :
          (w (i + n)).re * (-γ) ≤ -γ * σ ^ k := by
        have :=
          mul_le_mul_of_nonneg_left hwfloor hγ.le
        nlinarith
      rw [if_pos hnR]
      have hCrho : 0 ≤ C * ρ ^ k :=
        mul_nonneg hC (pow_nonneg hρ k)
      linarith
    · rw [if_neg hnR, sub_zero]
      by_cases hbad : b (i + n) ≤ T
      · have hwsmall := hsmall (i + n) hbad
        calc
          (w (i + n)).re * (a (i + n) - b (i + n)) ≤
              (w (i + n)).re * |a (i + n) - b (i + n)| :=
            mul_le_mul_of_nonneg_left
              (le_abs_self (a (i + n) - b (i + n))) hw0
          _ ≤ ρ ^ k * C := by
            exact mul_le_mul hwsmall (herror (i + n))
              (abs_nonneg _) (pow_nonneg hρ k)
          _ = C * ρ ^ k := by ring
      · have hbhigh : T < b (i + n) := lt_of_not_ge hbad
        have he : a (i + n) - b (i + n) ≤ -γ := by
          linarith
        have hnonpos :
            (w (i + n)).re * (a (i + n) - b (i + n)) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hw0 (by linarith)
        exact hnonpos.trans
          (mul_nonneg hC (pow_nonneg hρ k))
  have hsum :
      (Finset.range Q).sum
          (fun n ↦ (w (i + n)).re *
            (a (i + n) - b (i + n))) ≤
        (Q : ℝ) * (C * ρ ^ k) -
          (K : ℝ) * (γ * σ ^ k) := by
    calc
      (Finset.range Q).sum
          (fun n ↦ (w (i + n)).re *
            (a (i + n) - b (i + n))) ≤
          (Finset.range Q).sum
            (fun n ↦ C * ρ ^ k -
              if n ∈ R then γ * σ ^ k else 0) :=
        Finset.sum_le_sum hpoint
      _ = (Q : ℝ) * (C * ρ ^ k) -
          (K : ℝ) * (γ * σ ^ k) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, Finset.sum_ite_mem]
        rw [Finset.inter_eq_right.mpr hRsubset]
        rw [hRcard]
  have hratioK :
      (K : ℝ) * ((L : ℝ) * C * ρ ^ k) <
        (K : ℝ) * (γ * σ ^ k / 2) :=
    mul_lt_mul_of_pos_left hratio (by exact_mod_cast hK)
  have hsum_neg :
      (Finset.range Q).sum
          (fun n ↦ (w (i + n)).re *
            (a (i + n) - b (i + n))) <
        -(K : ℝ) * (γ * σ ^ k / 2) := by
    calc
      _ ≤ (Q : ℝ) * (C * ρ ^ k) -
          (K : ℝ) * (γ * σ ^ k) := hsum
      _ < -(K : ℝ) * (γ * σ ^ k / 2) := by
        dsimp [Q]
        push_cast
        nlinarith
  have hKQ : K ≤ Q := by
    dsimp [Q]
    exact Nat.le_mul_of_pos_right K hL
  have hQN : N₀ ≤ Q - 1 := by
    dsimp [K] at hKQ
    omega
  have hud := hN₀ (Q - 1) hQN i
  have hQsucc : Q - 1 + 1 = Q := by omega
  let z : ℂ :=
    complexCesaroAverage
      (fun n ↦
        w (i + n) *
          ((a (i + n) - b (i + n) : ℝ) : ℂ))
      (Q - 1)
  have hzre :
      z.re =
        ((Q : ℝ)⁻¹) *
          (Finset.range Q).sum
            (fun n ↦ (w (i + n)).re *
              (a (i + n) - b (i + n))) := by
    have hinvQ :
        (((Q : ℕ) : ℂ)⁻¹) = (((Q : ℝ)⁻¹ : ℝ) : ℂ) := by
      change (((Q : ℝ) : ℂ)⁻¹) = (((Q : ℝ)⁻¹ : ℝ) : ℂ)
      norm_cast
    dsimp [z]
    unfold complexCesaroAverage
    rw [hQsucc, hinvQ]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    congr 2
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hzneg : z.re < -ζ := by
    rw [hzre]
    have hscale :=
      mul_lt_mul_of_pos_left hsum_neg (inv_pos.mpr hQreal)
    have hright :
        ((Q : ℝ)⁻¹) *
            (-(K : ℝ) * (γ * σ ^ k / 2)) =
          -(γ * σ ^ k / (2 * (L : ℝ))) := by
      dsimp [Q]
      push_cast
      field_simp
    calc
      ((Q : ℝ)⁻¹) *
          (Finset.range Q).sum
            (fun n ↦ (w (i + n)).re *
              (a (i + n) - b (i + n))) <
          ((Q : ℝ)⁻¹) *
            (-(K : ℝ) * (γ * σ ^ k / 2)) := hscale
      _ = -(γ * σ ^ k / (2 * (L : ℝ))) := hright
      _ < -ζ := by
        dsimp [ζ]
        have hpos : 0 < γ * σ ^ k := by positivity
        have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
        apply neg_lt_neg
        rw [div_lt_div_iff₀
          (mul_pos (by norm_num) hLpos)
          (mul_pos (by norm_num) hLpos)]
        nlinarith
  have hzabs : ζ < |z.re| := by
    have hzre0 : z.re < 0 := lt_of_lt_of_le hzneg (neg_nonpos.mpr hζ.le)
    rw [abs_of_neg hzre0]
    linarith
  have hznorm : ζ < ‖z‖ :=
    hzabs.trans_le (Complex.abs_re_le_norm z)
  change ‖z‖ < ζ at hud
  exact (not_lt_of_ge hznorm.le) hud

end Chapter02.WeightedSyndeticTransfer
