import Chapter02.Common

open Classical Set

noncomputable section

namespace Chapter02.MultipleKhintchineSyndetic

universe u

/-- The three-fold progression correlation appearing in BHK Theorem 1.2. -/
def tripleCorrelation (M : System.{u}) (A : Set M.X) (n : ℕ) : ℝ :=
  realMeasure M
    (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A)

/-- The four-fold progression correlation appearing in BHK Theorem 1.2. -/
def quadrupleCorrelation (M : System.{u}) (A : Set M.X) (n : ℕ) : ℝ :=
  realMeasure M
    (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
      preimageIter M (3 * n) A)

/-- Every translated block of one fixed positive length has average strictly
larger than `c`.  The division-free formulation is convenient over `ℝ`. -/
def HasUniformBlockLowerBound (a : ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ i : ℕ,
    (Finset.range N).sum (fun j => a (i + j)) > (N : ℝ) * c

/-- BHK's `UD-Lim`: the absolute values have Cesàro mean tending to zero
uniformly over the starting point of the averaging interval. -/
def TendsToZeroInUniformDensity (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
    cesaroAverage (fun n ↦ |a (i + n)|) N < ε

/-- Translated-uniform mean-square convergence, the Cartesian-square
criterion used to prove `UD-Lim`. -/
def TendsToZeroInUniformMeanSquare (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
    cesaroAverage (fun n ↦ (a (i + n)) ^ 2) N < ε

/-- Uniform mean-square convergence implies BHK uniform-density convergence
by the finite Cauchy--Schwarz inequality. -/
theorem tendsToZeroInUniformDensity_of_meanSquare
    {a : ℕ → ℝ} (ha : TendsToZeroInUniformMeanSquare a) :
    TendsToZeroInUniformDensity a := by
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  filter_upwards [ha (ε ^ 2) hεsq] with N hN
  intro i
  let q : ℕ := N + 1
  let S : ℝ := (Finset.range q).sum (fun n ↦ |a (i + n)|)
  let V : ℝ := (Finset.range q).sum (fun n ↦ (a (i + n)) ^ 2)
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hcs : S ^ 2 ≤ (q : ℝ) * V := by
    dsimp [S, V]
    have h :=
      sq_sum_le_card_mul_sum_sq
        (s := Finset.range q) (f := fun n ↦ |a (i + n)|)
    simpa only [Finset.card_range, sq_abs] using h
  have hVstrict : V < (q : ℝ) * ε ^ 2 := by
    have hNi := hN i
    unfold cesaroAverage at hNi
    change ((q : ℝ)⁻¹) * V < ε ^ 2 at hNi
    rw [inv_mul_lt_iff₀ hqR] at hNi
    exact hNi
  have hSstrict : S < (q : ℝ) * ε := by
    have hright : 0 < (q : ℝ) * ε := mul_pos hqR hε
    nlinarith [mul_pos hqR (sub_pos.mpr hVstrict)]
  unfold cesaroAverage
  change ((q : ℝ)⁻¹) * S < ε
  rw [inv_mul_lt_iff₀ hqR]
  exact hSstrict

lemma tendsToZeroInUniformDensity_zero :
    TendsToZeroInUniformDensity (fun _ : ℕ ↦ (0 : ℝ)) := by
  intro ε hε
  filter_upwards
  intro N i
  simpa [cesaroAverage] using hε

lemma TendsToZeroInUniformDensity.neg
    {a : ℕ → ℝ} (ha : TendsToZeroInUniformDensity a) :
    TendsToZeroInUniformDensity (fun n ↦ -a n) := by
  intro ε hε
  simpa only [abs_neg] using ha ε hε

lemma TendsToZeroInUniformDensity.add
    {a b : ℕ → ℝ}
    (ha : TendsToZeroInUniformDensity a)
    (hb : TendsToZeroInUniformDensity b) :
    TendsToZeroInUniformDensity (fun n ↦ a n + b n) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [ha (ε / 2) hε2, hb (ε / 2) hε2] with N haN hbN
  intro i
  have hsum :
      cesaroAverage (fun n ↦ |a (i + n) + b (i + n)|) N ≤
        cesaroAverage (fun n ↦ |a (i + n)| + |b (i + n)|) N := by
    unfold cesaroAverage
    gcongr with n hn
    exact abs_add_le _ _
  have hsplit :
      cesaroAverage (fun n ↦ |a (i + n)| + |b (i + n)|) N =
        cesaroAverage (fun n ↦ |a (i + n)|) N +
          cesaroAverage (fun n ↦ |b (i + n)|) N := by
    unfold cesaroAverage
    rw [Finset.sum_add_distrib, mul_add]
  rw [hsplit] at hsum
  calc
    cesaroAverage (fun n ↦ |a (i + n) + b (i + n)|) N ≤
        cesaroAverage (fun n ↦ |a (i + n)|) N +
          cesaroAverage (fun n ↦ |b (i + n)|) N := hsum
    _ < ε / 2 + ε / 2 := add_lt_add (haN i) (hbN i)
    _ = ε := by ring

lemma TendsToZeroInUniformDensity.const_mul
    {a : ℕ → ℝ} (ha : TendsToZeroInUniformDensity a) (c : ℝ) :
    TendsToZeroInUniformDensity (fun n ↦ c * a n) := by
  by_cases hc : c = 0
  · subst c
    simpa using tendsToZeroInUniformDensity_zero
  intro ε hε
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hδ : 0 < ε / |c| := div_pos hε hcabs
  filter_upwards [ha (ε / |c|) hδ] with N hN
  intro i
  have heq :
      cesaroAverage (fun n ↦ |c * a (i + n)|) N =
        |c| * cesaroAverage (fun n ↦ |a (i + n)|) N := by
    unfold cesaroAverage
    simp_rw [abs_mul, ← Finset.mul_sum]
    ring
  rw [heq]
  calc
    |c| * cesaroAverage (fun n ↦ |a (i + n)|) N <
        |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hN i) hcabs
    _ = ε := by field_simp

/-- A uniform-density-zero perturbation preserves a syndetic strict
superlevel set, with any fixed positive loss in the threshold.  This is the
finite counting form of BHK Lemma 1.11 needed below. -/
theorem isSyndetic_superlevel_of_uniformDensity_close
    (a b : ℕ → ℝ) (c η : ℝ) (hη : 0 < η)
    (hb : IsSyndetic {n : ℕ | b n > c + η})
    (hab : TendsToZeroInUniformDensity (fun n ↦ a n - b n)) :
    IsSyndetic {n : ℕ | a n > c} := by
  obtain ⟨L, hL, hbL⟩ := hb
  let δ : ℝ := η / (2 * (L : ℝ))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N₀, hN₀⟩ :=
    (Filter.eventually_atTop.1 (hab δ hδ))
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
  let p : ℕ → ℕ := fun k ↦
    Classical.choose (hbL (i + k * L))
  have hp_mem (k : ℕ) :
      p k ∈ {n : ℕ | b n > c + η} :=
    (Classical.choose_spec (hbL (i + k * L))).1
  have hp_lower (k : ℕ) : i + k * L ≤ p k :=
    (Classical.choose_spec (hbL (i + k * L))).2.1
  have hp_upper (k : ℕ) : p k < i + k * L + L :=
    (Classical.choose_spec (hbL (i + k * L))).2.2
  let r : ℕ → ℕ := fun k ↦ p k - i
  have hp_from_i (k : ℕ) : i ≤ p k :=
    (Nat.le_add_right i (k * L)).trans (hp_lower k)
  have hr_eq (k : ℕ) : i + r k = p k := by
    exact Nat.add_sub_of_le (hp_from_i k)
  have hr_lt (k : ℕ) (hk : k ∈ Finset.range K) : r k < Q := by
    have hkK : k < K := Finset.mem_range.mp hk
    have hmul : (k + 1) * L ≤ K * L :=
      Nat.mul_le_mul_right L (Nat.succ_le_of_lt hkK)
    have hpQ : p k < i + Q := by
      calc
        p k < i + k * L + L := hp_upper k
        _ = i + (k + 1) * L := by
          simp [Nat.add_mul, Nat.add_assoc]
        _ ≤ i + K * L := Nat.add_le_add_left hmul i
        _ = i + Q := by rfl
    have hiadd : i + r k < i + Q := by
      rw [hr_eq k]
      exact hpQ
    omega
  have hr_inj : Set.InjOn r (Finset.range K) := by
    intro k hk l hl hkl
    by_contra hne
    have horder : k < l ∨ l < k := by omega
    rcases horder with hkl' | hlk'
    · have hsep : p k < p l := by
        have hmul : (k + 1) * L ≤ l * L :=
          Nat.mul_le_mul_right L (Nat.succ_le_of_lt hkl')
        calc
          p k < i + k * L + L := hp_upper k
          _ = i + (k + 1) * L := by
            simp [Nat.add_mul, Nat.add_assoc]
          _ ≤ i + l * L := Nat.add_le_add_left hmul i
          _ ≤ p l := hp_lower l
      have hp_eq : p k = p l := by
        rw [← hr_eq k, ← hr_eq l, hkl]
      exact (ne_of_lt hsep) hp_eq
    · have hsep : p l < p k := by
        have hmul : (l + 1) * L ≤ k * L :=
          Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlk')
        calc
          p l < i + l * L + L := hp_upper l
          _ = i + (l + 1) * L := by
            simp [Nat.add_mul, Nat.add_assoc]
          _ ≤ i + k * L := Nat.add_le_add_left hmul i
          _ ≤ p k := hp_lower k
      have hp_eq : p l = p k := by
        rw [← hr_eq l, ← hr_eq k, hkl]
      exact (ne_of_lt hsep) hp_eq
  have himage :
      (Finset.range K).image r ⊆ Finset.range Q := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hr_lt k hk)
  have hpoint (k : ℕ) (hk : k ∈ Finset.range K) :
      η < |a (i + r k) - b (i + r k)| := by
    have hbpk : c + η < b (p k) := hp_mem k
    have hpkQ : p k < i + Q := by
      rw [← hr_eq k]
      exact Nat.add_lt_add_left (hr_lt k hk) i
    have hapk : a (p k) ≤ c := by
      apply le_of_not_gt
      intro ha
      exact (not_lt_of_ge (hnone (p k) ha (hp_from_i k))) hpkQ
    rw [hr_eq k]
    have hneg : a (p k) - b (p k) < -η := by linarith
    have hneg0 : a (p k) - b (p k) < 0 := by linarith
    rw [abs_of_neg hneg0]
    linarith
  have himage_sum :
      (K : ℝ) * η <
        ((Finset.range K).image r).sum
          (fun n ↦ |a (i + n) - b (i + n)|) := by
    rw [Finset.sum_image hr_inj]
    have hstrict :
        (Finset.range K).sum (fun _ ↦ η) <
          (Finset.range K).sum
            (fun k ↦ |a (i + r k) - b (i + r k)|) := by
      exact Finset.sum_lt_sum (fun k hk ↦ (hpoint k hk).le)
        ⟨0, Finset.mem_range.mpr hK, hpoint 0 (Finset.mem_range.mpr hK)⟩
    simpa using hstrict
  have hfull :
      ((Finset.range K).image r).sum
          (fun n ↦ |a (i + n) - b (i + n)|) ≤
        (Finset.range Q).sum
          (fun n ↦ |a (i + n) - b (i + n)|) :=
    Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun n hn hnot ↦ abs_nonneg _)
  have hQN : N₀ ≤ Q - 1 := by
    have hKQ : K ≤ Q := by
      dsimp [Q]
      exact Nat.le_mul_of_pos_right K hL
    dsimp [K] at hKQ
    omega
  have hud := hN₀ (Q - 1) hQN i
  have hQsucc : Q - 1 + 1 = Q := by omega
  unfold cesaroAverage at hud
  rw [hQsucc] at hud
  have hsum_upper :
      (Finset.range Q).sum
          (fun n ↦ |a (i + n) - b (i + n)|) <
        (Q : ℝ) * δ := by
    have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
    rw [inv_mul_lt_iff₀ hQreal] at hud
    simpa [mul_comm] using hud
  have hcalc : (Q : ℝ) * δ = (K : ℝ) * η / 2 := by
    dsimp [Q, δ]
    have hLreal : (L : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hcalc] at hsum_upper
  have hKη : 0 < (K : ℝ) * η := mul_pos (by exact_mod_cast hK) hη
  linarith

/-- A uniform strict lower bound for every block sum forces the strict
superlevel set to have bounded gaps. -/
theorem isSyndetic_superlevel_of_block_sum_gt
    (a : ℕ → ℝ) (c : ℝ) (N : ℕ) (hN : 0 < N)
    (hblock : ∀ i : ℕ,
      (Finset.range N).sum (fun j => a (i + j)) > (N : ℝ) * c) :
    IsSyndetic {n : ℕ | a n > c} := by
  refine ⟨N, hN, ?_⟩
  intro i
  by_contra h
  push_neg at h
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) : a (i + j) ≤ c := by
    apply le_of_not_gt
    intro hij
    have hnot := h (i + j) hij (Nat.le_add_right i j)
    have hjlt : j < N := Finset.mem_range.mp hj
    omega
  have hsum :
      (Finset.range N).sum (fun j => a (i + j)) ≤
        (Finset.range N).sum (fun _ => c) := by
    exact Finset.sum_le_sum fun j hj => hterm j hj
  have hconst :
      (Finset.range N).sum (fun _ => c) = (N : ℝ) * c := by
    simp
  rw [hconst] at hsum
  exact (not_lt_of_ge hsum) (hblock i)

theorem isSyndetic_superlevel_of_uniformBlockLowerBound
    (a : ℕ → ℝ) (c : ℝ) (h : HasUniformBlockLowerBound a c) :
    IsSyndetic {n : ℕ | a n > c} := by
  obtain ⟨N, hN, hblock⟩ := h
  exact isSyndetic_superlevel_of_block_sum_gt a c N hN hblock

/-- Exact analytic obligation remaining after removing the combinatorial
syndeticity step from the three- and four-fold clauses of BHK Theorem 1.2. -/
def MultipleKhintchineUniformBlockBounds (M : System.{u}) : Prop :=
  IsErgodic M →
    ∀ A : Set M.X, MeasurableSet A → 0 < M.μ A →
    ∀ ε : ℝ, 0 < ε →
      HasUniformBlockLowerBound (tripleCorrelation M A)
        ((realMeasure M A) ^ 3 - ε) ∧
      HasUniformBlockLowerBound (quadrupleCorrelation M A)
        ((realMeasure M A) ^ 4 - ε)

/-- Uniform block lower bounds imply exactly the two syndetic conclusions in
BHK Theorem 1.2, without any additional dynamical assumption. -/
theorem multipleKhintchine_of_uniformBlockBounds
    (M : System.{u}) (h : MultipleKhintchineUniformBlockBounds M) :
    IsErgodic M →
      ∀ A : Set M.X, MeasurableSet A → 0 < M.μ A →
      ∀ ε : ℝ, 0 < ε →
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A) >
            (realMeasure M A) ^ 3 - ε} ∧
        IsSyndetic {n : ℕ |
          realMeasure M
              (A ∩ preimageIter M n A ∩ preimageIter M (2 * n) A ∩
                preimageIter M (3 * n) A) >
            (realMeasure M A) ^ 4 - ε} := by
  intro hM A hA hApos ε hε
  obtain ⟨hthree, hfour⟩ := h hM A hA hApos ε hε
  constructor
  · simpa [tripleCorrelation] using
      isSyndetic_superlevel_of_uniformBlockLowerBound
        (tripleCorrelation M A) ((realMeasure M A) ^ 3 - ε) hthree
  · simpa [quadrupleCorrelation] using
      isSyndetic_superlevel_of_uniformBlockLowerBound
        (quadrupleCorrelation M A) ((realMeasure M A) ^ 4 - ε) hfour

end Chapter02.MultipleKhintchineSyndetic
