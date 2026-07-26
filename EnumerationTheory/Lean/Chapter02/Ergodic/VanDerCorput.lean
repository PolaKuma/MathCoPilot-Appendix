import Chapter02.Common

open Classical
open Filter
open scoped BigOperators

noncomputable section

namespace Chapter02.VanDerCorput

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Cauchy--Schwarz for a finite sum of vectors, in a form used by the
finite van der Corput estimate. -/
lemma norm_finset_sum_sq_le
    {ι : Type*} (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hnorm :
      ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
    exact norm_sum_le _ _
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, ‖f i‖ := by positivity
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i ∈ s, f i)]
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq

/-- Shifting a finite sum by `h` changes only its two boundary pieces. -/
lemma norm_sum_range_shift_sub_le
    (u : ℕ → E) (M : ℝ) (h N : ℕ)
    (hu : ∀ n, ‖u n‖ ≤ M) :
    ‖(∑ n ∈ Finset.range N, u (n + h)) -
        ∑ n ∈ Finset.range N, u n‖ ≤
      2 * (h : ℝ) * M := by
  have hshift :
      (∑ n ∈ Finset.range N, u (n + h)) +
          ∑ n ∈ Finset.range h, u n =
        ∑ n ∈ Finset.range (N + h), u n := by
    rw [add_comm N h, Finset.sum_range_add]
    simp only [add_comm]
  have htail :
      (∑ n ∈ Finset.range N, u n) +
          ∑ n ∈ Finset.range h, u (N + n) =
        ∑ n ∈ Finset.range (N + h), u n := by
    rw [Finset.sum_range_add]
  have hrearrange :
      (∑ n ∈ Finset.range N, u (n + h)) -
          ∑ n ∈ Finset.range N, u n =
        (∑ n ∈ Finset.range h, u (N + n)) -
          ∑ n ∈ Finset.range h, u n := by
    let A : E := ∑ n ∈ Finset.range N, u (n + h)
    let B : E := ∑ n ∈ Finset.range h, u n
    let C : E := ∑ n ∈ Finset.range N, u n
    let D : E := ∑ n ∈ Finset.range h, u (N + n)
    have heq : A + B = C + D := by
      exact hshift.trans htail.symm
    have hAC : A - C = D - B := by
      calc
        A - C = (C + D - B) - C := by rw [← heq]; abel
        _ = D - B := by abel
    exact hAC
  rw [hrearrange]
  calc
    ‖(∑ n ∈ Finset.range h, u (N + n)) -
        ∑ n ∈ Finset.range h, u n‖ ≤
      ‖∑ n ∈ Finset.range h, u (N + n)‖ +
        ‖∑ n ∈ Finset.range h, u n‖ := norm_sub_le _ _
    _ ≤ (∑ n ∈ Finset.range h, ‖u (N + n)‖) +
        ∑ n ∈ Finset.range h, ‖u n‖ := by
      gcongr
      · exact norm_sum_le _ _
      · exact norm_sum_le _ _
    _ ≤ (∑ _n ∈ Finset.range h, M) +
        ∑ _n ∈ Finset.range h, M := by
      gcongr with n hn
      · exact hu _
      · exact hu _
    _ = 2 * (h : ℝ) * M := by
      simp
      ring

/-- Averaging the first `N` vectors is asymptotically unchanged if each
vector is first replaced by a forward block of `H` shifts.  This is the
boundary estimate in the finite Hilbert-space van der Corput argument. -/
lemma norm_smul_sum_sub_sum_forwardBlocks_le
    (u : ℕ → E) (M : ℝ) (H N : ℕ)
    (hu : ∀ n, ‖u n‖ ≤ M) :
    ‖(H : ℂ) • (∑ n ∈ Finset.range N, u n) -
        ∑ n ∈ Finset.range N,
          ∑ h ∈ Finset.range H, u (n + h)‖ ≤
      2 * (H : ℝ) ^ 2 * M := by
  let S : E := ∑ n ∈ Finset.range N, u n
  have hdouble :
      (∑ n ∈ Finset.range N,
          ∑ h ∈ Finset.range H, u (n + h)) =
        ∑ h ∈ Finset.range H,
          ∑ n ∈ Finset.range N, u (n + h) := by
    rw [Finset.sum_comm]
  have hconst :
      (H : ℂ) • S = ∑ _h ∈ Finset.range H, S := by
    rw [Finset.sum_const, Finset.card_range]
    exact Nat.cast_smul_eq_nsmul ℂ H S
  rw [hdouble, hconst, ← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ Finset.range H,
        (S - ∑ n ∈ Finset.range N, u (n + h))‖ ≤
      ∑ h ∈ Finset.range H,
        ‖S - ∑ n ∈ Finset.range N, u (n + h)‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.range H, 2 * (h : ℝ) * M := by
      gcongr with h hh
      simpa [S, norm_sub_rev] using
        norm_sum_range_shift_sub_le u M h N hu
    _ ≤ ∑ _h ∈ Finset.range H, 2 * (H : ℝ) * M := by
      apply Finset.sum_le_sum
      intro h hh
      have hh' : (h : ℝ) ≤ H := by
        exact_mod_cast (Finset.mem_range.mp hh).le
      have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
      nlinarith [mul_nonneg (sub_nonneg.mpr hh') hM]
    _ = 2 * (H : ℝ) ^ 2 * M := by
      simp
      ring

/-- Unsquared finite van der Corput comparison: `H` times the norm of the
original sum is controlled by the norm of the forward-block sum plus the
explicit boundary error. -/
lemma mul_norm_sum_le_norm_sum_forwardBlocks_add
    (u : ℕ → E) (M : ℝ) (H N : ℕ)
    (hu : ∀ n, ‖u n‖ ≤ M) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ ≤
      ‖∑ n ∈ Finset.range N,
          ∑ h ∈ Finset.range H, u (n + h)‖ +
        2 * (H : ℝ) ^ 2 * M := by
  let A : E := (H : ℂ) • (∑ n ∈ Finset.range N, u n)
  let B : E := ∑ n ∈ Finset.range N,
    ∑ h ∈ Finset.range H, u (n + h)
  have hboundary : ‖A - B‖ ≤ 2 * (H : ℝ) ^ 2 * M :=
    norm_smul_sum_sub_sum_forwardBlocks_le u M H N hu
  have htriangle : ‖A‖ ≤ ‖B‖ + ‖A - B‖ := by
    calc
      ‖A‖ = ‖(A - B) + B‖ := by congr 1; abel
      _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
      _ = ‖B‖ + ‖A - B‖ := add_comm _ _
  calc
    (H : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ = ‖A‖ := by
      simp [A, norm_smul]
    _ ≤ ‖B‖ + ‖A - B‖ := htriangle
    _ ≤ ‖B‖ + 2 * (H : ℝ) ^ 2 * M :=
      add_le_add (le_refl _) hboundary
    _ = ‖∑ n ∈ Finset.range N,
          ∑ h ∈ Finset.range H, u (n + h)‖ +
        2 * (H : ℝ) ^ 2 * M := by rfl

section InnerProduct

variable [InnerProductSpace ℂ E]

/-- Expanding the squared norm of a finite vector sum gives the real part of
the full pair-correlation sum. -/
lemma norm_finset_sum_sq_eq_sum_re_inner
    {ι : Type*} (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (@inner ℂ E _ (f j) (f i)).re := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [inner_sum, sum_inner, map_sum]
  rfl

/-- The quadratic estimate after replacing each vector by a forward block:
the right-hand side is now expressed entirely through pair correlations. -/
lemma norm_sum_forwardBlocks_sq_le
    (u : ℕ → E) (H N : ℕ) :
    ‖∑ n ∈ Finset.range N,
        ∑ h ∈ Finset.range H, u (n + h)‖ ^ 2 ≤
      (N : ℝ) *
        ∑ n ∈ Finset.range N,
          ∑ h ∈ Finset.range H,
            ∑ k ∈ Finset.range H,
              (@inner ℂ E _ (u (n + k)) (u (n + h))).re := by
  calc
    ‖∑ n ∈ Finset.range N,
        ∑ h ∈ Finset.range H, u (n + h)‖ ^ 2 ≤
      ((Finset.range N).card : ℝ) *
        ∑ n ∈ Finset.range N,
          ‖∑ h ∈ Finset.range H, u (n + h)‖ ^ 2 :=
      norm_finset_sum_sq_le (Finset.range N)
        (fun n => ∑ h ∈ Finset.range H, u (n + h))
    _ = (N : ℝ) *
        ∑ n ∈ Finset.range N,
          ∑ h ∈ Finset.range H,
            ∑ k ∈ Finset.range H,
              (@inner ℂ E _ (u (n + k)) (u (n + h))).re := by
      simp only [Finset.card_range]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      exact norm_finset_sum_sq_eq_sum_re_inner
        (Finset.range H) (fun h => u (n + h))

/-- Finite Hilbert-space van der Corput inequality.  `C` is the complete
pair-correlation sum inside all forward blocks. -/
lemma finite_vanDerCorput
    (u : ℕ → E) (M : ℝ) (H N : ℕ)
    (hu : ∀ n, ‖u n‖ ≤ M) :
    let C : ℝ :=
      ∑ n ∈ Finset.range N,
        ∑ h ∈ Finset.range H,
          ∑ k ∈ Finset.range H,
            (@inner ℂ E _ (u (n + k)) (u (n + h))).re
    (H : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ ≤
      Real.sqrt ((N : ℝ) * C) + 2 * (H : ℝ) ^ 2 * M := by
  dsimp only
  let B : E := ∑ n ∈ Finset.range N,
    ∑ h ∈ Finset.range H, u (n + h)
  let C : ℝ :=
    ∑ n ∈ Finset.range N,
      ∑ h ∈ Finset.range H,
        ∑ k ∈ Finset.range H,
          (@inner ℂ E _ (u (n + k)) (u (n + h))).re
  have hblock : ‖B‖ ^ 2 ≤ (N : ℝ) * C :=
    norm_sum_forwardBlocks_sq_le u H N
  have hNC : 0 ≤ (N : ℝ) * C := by
    exact (sq_nonneg ‖B‖).trans hblock
  have hsqrt_sq : (Real.sqrt ((N : ℝ) * C)) ^ 2 = (N : ℝ) * C :=
    Real.sq_sqrt hNC
  have hB : ‖B‖ ≤ Real.sqrt ((N : ℝ) * C) := by
    nlinarith [norm_nonneg B, Real.sqrt_nonneg ((N : ℝ) * C)]
  have hboundary :=
    mul_norm_sum_le_norm_sum_forwardBlocks_add u M H N hu
  change (H : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ ≤
    ‖B‖ + 2 * (H : ℝ) ^ 2 * M at hboundary
  calc
    (H : ℝ) * ‖∑ n ∈ Finset.range N, u n‖ ≤
        ‖B‖ + 2 * (H : ℝ) ^ 2 * M := hboundary
    _ ≤ Real.sqrt ((N : ℝ) * C) + 2 * (H : ℝ) ^ 2 * M :=
      add_le_add hB (le_refl _)
    _ = Real.sqrt ((N : ℝ) *
          ∑ n ∈ Finset.range N,
            ∑ h ∈ Finset.range H,
              ∑ k ∈ Finset.range H,
                (@inner ℂ E _ (u (n + k)) (u (n + h))).re) +
        2 * (H : ℝ) ^ 2 * M := by rfl

/-- The absolute off-diagonal correlations in a forward block.  Separating
these from the diagonal is the form needed when continuous spectrum gives
absolute Cesàro decay. -/
def offDiagonalBlockCorrelation
    (u : ℕ → E) (H n : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
    if h = k then 0 else ‖@inner ℂ E _ (u (n + k)) (u (n + h))‖

/-- A block correlation is bounded by its diagonal contribution plus the
absolute off-diagonal correlations. -/
lemma blockCorrelation_le_diagonal_add_offDiagonal
    (u : ℕ → E) (M : ℝ) (H n : ℕ)
    (hu : ∀ m, ‖u m‖ ≤ M) :
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        (@inner ℂ E _ (u (n + k)) (u (n + h))).re) ≤
      (H : ℝ) * M ^ 2 + offDiagonalBlockCorrelation u H n := by
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  calc
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        (@inner ℂ E _ (u (n + k)) (u (n + h))).re) ≤
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        (if h = k then M ^ 2
          else ‖@inner ℂ E _ (u (n + k)) (u (n + h))‖) := by
      gcongr with h hh k hk
      by_cases heq : h = k
      · subst k
        simp only [if_pos]
        calc
          (@inner ℂ E _ (u (n + h)) (u (n + h))).re ≤
              ‖@inner ℂ E _ (u (n + h)) (u (n + h))‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ ‖u (n + h)‖ * ‖u (n + h)‖ :=
            norm_inner_le_norm _ _
          _ ≤ M ^ 2 := by
            nlinarith [norm_nonneg (u (n + h)), hu (n + h)]
      · rw [if_neg heq]
        exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ = (H : ℝ) * M ^ 2 + offDiagonalBlockCorrelation u H n := by
      unfold offDiagonalBlockCorrelation
      have hdiag :
          (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
            if h = k then M ^ 2 else 0) = (H : ℝ) * M ^ 2 := by
        calc
          (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
              if h = k then M ^ 2 else 0) =
              ∑ _h ∈ Finset.range H, M ^ 2 := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [Finset.sum_eq_single h]
            · simp
            · intro k hk hkh
              simp [hkh.symm]
            · intro hnot
              exact (hnot hh).elim
          _ = (H : ℝ) * M ^ 2 := by simp
      simp_rw [show ∀ h k : ℕ,
          (if h = k then M ^ 2
            else ‖@inner ℂ E _ (u (n + k)) (u (n + h))‖) =
          (if h = k then M ^ 2 else 0) +
            (if h = k then 0
              else ‖@inner ℂ E _ (u (n + k)) (u (n + h))‖) by
          intro h k
          by_cases heq : h = k <;> simp [heq]]
      simp_rw [Finset.sum_add_distrib]
      rw [hdiag]

/-- Finite sums preserve zero Cesàro limits. -/
lemma cesaroTendsTo_finset_sum_zero
    {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ)
    (ha : ∀ i ∈ s, cesaroTendsTo (a i) 0) :
    cesaroTendsTo (fun n => ∑ i ∈ s, a i n) 0 := by
  unfold cesaroTendsTo seqTendsTo cesaroAverage at ha ⊢
  have hsum := tendsto_finset_sum s (fun i hi => ha i hi)
  convert hsum using 1
  · funext N
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp

/-- Absolute Cesàro decay of every off-diagonal pair in a fixed forward
block implies decay of the total off-diagonal block correlation. -/
lemma offDiagonalBlockCorrelation_cesaro_zero
    (u : ℕ → E) (H : ℕ)
    (hcorr : ∀ h ∈ Finset.range H, ∀ k ∈ Finset.range H, h ≠ k →
      cesaroTendsTo
        (fun n => ‖@inner ℂ E _ (u (n + k)) (u (n + h))‖) 0) :
    cesaroTendsTo (offDiagonalBlockCorrelation u H) 0 := by
  unfold offDiagonalBlockCorrelation
  apply cesaroTendsTo_finset_sum_zero
  intro h hh
  apply cesaroTendsTo_finset_sum_zero
  intro k hk
  by_cases heq : h = k
  · simp [heq, cesaroTendsTo, seqTendsTo, cesaroAverage]
  · simpa [heq] using hcorr h hh k hk heq

/-- Eventual fixed-block estimate used in the infinite van der Corput
argument.  It isolates exactly the diagonal cost `H * M²`; all
off-diagonal terms disappear by absolute Cesàro decay. -/
lemma eventually_blockCorrelationAverage_le
    (u : ℕ → E) (M : ℝ) (H : ℕ)
    (hu : ∀ n, ‖u n‖ ≤ M)
    (hcorr : ∀ h ∈ Finset.range H, ∀ k ∈ Finset.range H, h ≠ k →
      cesaroTendsTo
        (fun n => ‖@inner ℂ E _ (u (n + k)) (u (n + h))‖) 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      cesaroAverage
        (fun n => ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
          (@inner ℂ E _ (u (n + k)) (u (n + h))).re) N
        < (H : ℝ) * M ^ 2 + δ := by
  have hoff := offDiagonalBlockCorrelation_cesaro_zero u H hcorr
  unfold cesaroTendsTo seqTendsTo at hoff
  have heventually : ∀ᶠ N : ℕ in atTop,
      cesaroAverage (offDiagonalBlockCorrelation u H) N < δ := by
    filter_upwards [hoff.eventually (Iio_mem_nhds hδ)] with N hN
    exact hN
  filter_upwards [heventually] with N hN
  unfold cesaroAverage
  have hpointwise (n : ℕ) :=
    blockCorrelation_le_diagonal_add_offDiagonal u M H n hu
  calc
    (((N + 1 : ℕ) : ℝ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1),
          ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
            (@inner ℂ E _ (u (n + k)) (u (n + h))).re ≤
      (((N + 1 : ℕ) : ℝ)⁻¹) *
        ∑ n ∈ Finset.range (N + 1),
          ((H : ℝ) * M ^ 2 + offDiagonalBlockCorrelation u H n) := by
      gcongr with n hn
      exact hpointwise n
    _ = (H : ℝ) * M ^ 2 +
        cesaroAverage (offDiagonalBlockCorrelation u H) N := by
      unfold cesaroAverage
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
    _ < (H : ℝ) * M ^ 2 + δ := by
      exact (add_lt_add_iff_left ((H : ℝ) * M ^ 2)).mpr hN

/-- Hilbert-space van der Corput criterion in the absolute-correlation form
used by the continuous-spectrum part of the multiple ergodic theorem. -/
theorem vectorCesaro_tendsto_zero_of_offDiagonal
    (u : ℕ → E) (M : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ M)
    (hcorr : ∀ h k : ℕ, h ≠ k →
      cesaroTendsTo
        (fun n => ‖@inner ℂ E _ (u (n + k)) (u (n + h))‖) 0) :
    Tendsto
      (fun N : ℕ => (((N + 1 : ℕ) : ℂ)⁻¹) •
        ∑ n ∈ Finset.range (N + 1), u n)
      atTop (nhds 0) := by
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K : ℕ, hK⟩ :=
    exists_nat_gt (max 1 (2 * (M + 1) / ε))
  have hKpos : 0 < K := by
    have hKone : (1 : ℝ) < K :=
      lt_of_le_of_lt (le_max_left _ _) hK
    exact_mod_cast (show (0 : ℝ) < K by linarith)
  let H : ℕ := K ^ 2
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  have hsmall : (M + 1) / (K : ℝ) < ε / 2 := by
    have hKreal : 2 * (M + 1) / ε < (K : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hK
    have hKrealpos : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hMone : 0 < M + 1 := by linarith
    have hcleared : 2 * (M + 1) < (K : ℝ) * ε :=
      (div_lt_iff₀ hε).1 hKreal
    apply (div_lt_iff₀ hKrealpos).2
    nlinarith
  have hblock := eventually_blockCorrelationAverage_le
    u M H hu
    (fun h hh k hk hne => hcorr h k hne)
    (δ := (H : ℝ)) (by exact_mod_cast hHpos)
  rw [Filter.eventually_atTop] at hblock
  obtain ⟨Nb, hNb⟩ := hblock
  obtain ⟨N₀ : ℕ, hN₀⟩ :=
    exists_nat_gt (4 * (H : ℝ) * M / ε)
  refine ⟨max Nb N₀, ?_⟩
  intro N hN
  have hNbN : Nb ≤ N := le_trans (le_max_left _ _) hN
  have hN₀N : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hCavg := hNb N hNbN
  let C : ℝ :=
    ∑ n ∈ Finset.range (N + 1),
      ∑ h ∈ Finset.range H,
        ∑ k ∈ Finset.range H,
          (@inner ℂ E _ (u (n + k)) (u (n + h))).re
  have hNpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hCraw :
      C < ((N + 1 : ℕ) : ℝ) * ((H : ℝ) * M ^ 2 + H) := by
    unfold cesaroAverage at hCavg
    change (((N + 1 : ℕ) : ℝ)⁻¹) * C <
      (H : ℝ) * M ^ 2 + H at hCavg
    calc
      C = ((N + 1 : ℕ) : ℝ) *
          ((((N + 1 : ℕ) : ℝ)⁻¹) * C) := by
        field_simp
      _ < ((N + 1 : ℕ) : ℝ) * ((H : ℝ) * M ^ 2 + H) :=
        mul_lt_mul_of_pos_left hCavg hNpos
  let B : E := ∑ n ∈ Finset.range (N + 1),
    ∑ h ∈ Finset.range H, u (n + h)
  have hblockSq : ‖B‖ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) * C := by
    exact norm_sum_forwardBlocks_sq_le u H (N + 1)
  have hNC : 0 ≤ ((N + 1 : ℕ) : ℝ) * C :=
    (sq_nonneg ‖B‖).trans hblockSq
  have hsqrtSq :
      (Real.sqrt (((N + 1 : ℕ) : ℝ) * C)) ^ 2 =
        ((N + 1 : ℕ) : ℝ) * C :=
    Real.sq_sqrt hNC
  have hKrealpos : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hHrealpos : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hMone : 0 < M + 1 := by linarith
  have hroot :
      Real.sqrt (((N + 1 : ℕ) : ℝ) * C) <
        (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hHcast : (H : ℝ) = (K : ℝ) ^ 2 := by
      simp [H, Nat.cast_pow]
    have hupper :
        ((N + 1 : ℕ) : ℝ) * C <
          ((K : ℝ) * (M + 1) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [hHcast] at hCraw
      have hfirst :
          ((N + 1 : ℕ) : ℝ) * C <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) *
                ((K : ℝ) ^ 2 * M ^ 2 + (K : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hCraw hNpos
      have hMbound : M ^ 2 + 1 ≤ (M + 1) ^ 2 := by nlinarith
      calc
        ((N + 1 : ℕ) : ℝ) * C <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) *
                ((K : ℝ) ^ 2 * M ^ 2 + (K : ℝ) ^ 2)) := hfirst
        _ = (((K : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2) *
            (M ^ 2 + 1) := by ring
        _ ≤ (((K : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2) *
            (M + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hMbound (sq_nonneg _)
        _ = ((K : ℝ) * (M + 1) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by ring
    have hsqrtNonneg :=
      Real.sqrt_nonneg (((N + 1 : ℕ) : ℝ) * C)
    have hbasepos :
        0 < (K : ℝ) * (M + 1) * ((N + 1 : ℕ) : ℝ) := by positivity
    have hsqrtlt :
        Real.sqrt (((N + 1 : ℕ) : ℝ) * C) <
          (K : ℝ) * (M + 1) * ((N + 1 : ℕ) : ℝ) := by
      nlinarith
    rw [hHcast]
    have hsmall' : M + 1 < (ε / 2) * (K : ℝ) :=
      (div_lt_iff₀ hKrealpos).1 hsmall
    nlinarith
  have hboundary :
      2 * (H : ℝ) ^ 2 * M <
        (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hN₀real : (4 * (H : ℝ) * M / ε) < (N₀ : ℝ) := hN₀
    have hNreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
    have hlarge :
        4 * (H : ℝ) * M < ε * ((N + 1 : ℕ) : ℝ) := by
      have hratio : (4 * (H : ℝ) * M / ε) <
          ((N + 1 : ℕ) : ℝ) := by
        calc
          4 * (H : ℝ) * M / ε < (N₀ : ℝ) := hN₀real
          _ ≤ (N : ℝ) := hNreal
          _ < ((N + 1 : ℕ) : ℝ) := by norm_num
      simpa [mul_comm] using (div_lt_iff₀ hε).1 hratio
    nlinarith
  have hvdc := finite_vanDerCorput u M H (N + 1) hu
  change (H : ℝ) *
      ‖∑ n ∈ Finset.range (N + 1), u n‖ ≤
    Real.sqrt (((N + 1 : ℕ) : ℝ) * C) +
      2 * (H : ℝ) ^ 2 * M at hvdc
  rw [dist_zero_right, norm_smul, norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ n ∈ Finset.range (N + 1), u n‖ <
        ε * ((N + 1 : ℕ) : ℝ) := by
    nlinarith
  rw [inv_mul_lt_iff₀ hNpos]
  simpa [mul_comm] using hsum

/-- The averaged-correlation hypothesis in the general van der Corput
criterion.  Unlike pointwise off-diagonal decay, this is weak enough for
characteristic-factor arguments in an arbitrary ergodic system. -/
def HasVanDerCorputBlockDecay (u : ℕ → E) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ H : ℕ, 0 < H ∧
      ∀ᶠ N : ℕ in atTop,
        cesaroAverage
          (fun n => ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
            (@inner ℂ E _ (u (n + k)) (u (n + h))).re) N
          < δ * (H : ℝ) ^ 2

/-- General Hilbert-space van der Corput criterion, stated through decay of
the complete forward-block correlation average. -/
theorem vectorCesaro_tendsto_zero_of_blockDecay
    (u : ℕ → E) (M : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ M)
    (hdecay : HasVanDerCorputBlockDecay u) :
    Tendsto
      (fun N : ℕ => (((N + 1 : ℕ) : ℂ)⁻¹) •
        ∑ n ∈ Finset.range (N + 1), u n)
      atTop (nhds 0) := by
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := (ε / 2) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H, hHpos, hcorr⟩ := hdecay δ hδ
  rw [Filter.eventually_atTop] at hcorr
  obtain ⟨Nb, hNb⟩ := hcorr
  obtain ⟨N₀ : ℕ, hN₀⟩ :=
    exists_nat_gt (4 * (H : ℝ) * M / ε)
  refine ⟨max Nb N₀, ?_⟩
  intro N hN
  have hNbN : Nb ≤ N := le_trans (le_max_left _ _) hN
  have hN₀N : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hCavg := hNb N hNbN
  let C : ℝ :=
    ∑ n ∈ Finset.range (N + 1),
      ∑ h ∈ Finset.range H,
        ∑ k ∈ Finset.range H,
          (@inner ℂ E _ (u (n + k)) (u (n + h))).re
  have hNpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hHrealpos : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hCraw :
      C < ((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2) := by
    unfold cesaroAverage at hCavg
    change (((N + 1 : ℕ) : ℝ)⁻¹) * C <
      δ * (H : ℝ) ^ 2 at hCavg
    calc
      C = ((N + 1 : ℕ) : ℝ) *
          ((((N + 1 : ℕ) : ℝ)⁻¹) * C) := by field_simp
      _ < ((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hCavg hNpos
  let B : E := ∑ n ∈ Finset.range (N + 1),
    ∑ h ∈ Finset.range H, u (n + h)
  have hblockSq : ‖B‖ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) * C :=
    norm_sum_forwardBlocks_sq_le u H (N + 1)
  have hNC : 0 ≤ ((N + 1 : ℕ) : ℝ) * C :=
    (sq_nonneg ‖B‖).trans hblockSq
  have hsqrtSq :
      (Real.sqrt (((N + 1 : ℕ) : ℝ) * C)) ^ 2 =
        ((N + 1 : ℕ) : ℝ) * C :=
    Real.sq_sqrt hNC
  have hroot :
      Real.sqrt (((N + 1 : ℕ) : ℝ) * C) <
        (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hupper :
        ((N + 1 : ℕ) : ℝ) * C <
          ((ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
      have hfirst :
          ((N + 1 : ℕ) : ℝ) * C <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hCraw hNpos
      calc
        ((N + 1 : ℕ) : ℝ) * C <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2)) := hfirst
        _ = ((ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
          simp [δ]
          ring
    have hsqrtNonneg :=
      Real.sqrt_nonneg (((N + 1 : ℕ) : ℝ) * C)
    have hrhspos :
        0 < (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hboundary :
      2 * (H : ℝ) ^ 2 * M <
        (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hN₀real : (4 * (H : ℝ) * M / ε) < (N₀ : ℝ) := hN₀
    have hNreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
    have hratio : (4 * (H : ℝ) * M / ε) <
        ((N + 1 : ℕ) : ℝ) := by
      calc
        4 * (H : ℝ) * M / ε < (N₀ : ℝ) := hN₀real
        _ ≤ (N : ℝ) := hNreal
        _ < ((N + 1 : ℕ) : ℝ) := by norm_num
    have hlarge : 4 * (H : ℝ) * M <
        ε * ((N + 1 : ℕ) : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).1 hratio
    nlinarith
  have hvdc := finite_vanDerCorput u M H (N + 1) hu
  change (H : ℝ) *
      ‖∑ n ∈ Finset.range (N + 1), u n‖ ≤
    Real.sqrt (((N + 1 : ℕ) : ℝ) * C) +
      2 * (H : ℝ) ^ 2 * M at hvdc
  rw [dist_zero_right, norm_smul, norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ n ∈ Finset.range (N + 1), u n‖ <
        ε * ((N + 1 : ℕ) : ℝ) := by
    nlinarith
  rw [inv_mul_lt_iff₀ hNpos]
  simpa [mul_comm] using hsum

/-- Uniform-in-translation version of the complete block-correlation
hypothesis.  This is the form needed for syndetic recurrence. -/
def HasUniformVanDerCorputBlockDecay (u : ℕ → E) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ H : ℕ, 0 < H ∧
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        cesaroAverage
          (fun n => ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
            (@inner ℂ E _
              (u (i + (n + k))) (u (i + (n + h)))).re) N
          < δ * (H : ℝ) ^ 2

/-- Uniform Hilbert-space van der Corput criterion.  The same block length
works for every translated averaging interval. -/
theorem vectorCesaro_uniform_tendsto_zero_of_blockDecay
    (u : ℕ → E) (M : ℝ)
    (hu : ∀ n, ‖u n‖ ≤ M)
    (hdecay : HasUniformVanDerCorputBlockDecay u) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), u (i + n)‖ < ε := by
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  intro ε hε
  let δ : ℝ := (ε / 2) ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H, hHpos, hcorr⟩ := hdecay δ hδ
  rw [Filter.eventually_atTop] at hcorr
  obtain ⟨Nb, hNb⟩ := hcorr
  obtain ⟨N₀ : ℕ, hN₀⟩ :=
    exists_nat_gt (4 * (H : ℝ) * M / ε)
  refine Filter.eventually_atTop.2 ⟨max Nb N₀, ?_⟩
  intro N hN i
  have hNbN : Nb ≤ N := le_trans (le_max_left _ _) hN
  have hN₀N : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hCavg := hNb N hNbN i
  let v : ℕ → E := fun n ↦ u (i + n)
  let C : ℝ :=
    ∑ n ∈ Finset.range (N + 1),
      ∑ h ∈ Finset.range H,
        ∑ k ∈ Finset.range H,
          (@inner ℂ E _ (v (n + k)) (v (n + h))).re
  have hNpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hHrealpos : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hCavg' :
      (((N + 1 : ℕ) : ℝ)⁻¹) * C <
        δ * (H : ℝ) ^ 2 := by
    simpa only [cesaroAverage, C, v, Nat.add_assoc] using hCavg
  have hCraw :
      C < ((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2) := by
    calc
      C = ((N + 1 : ℕ) : ℝ) *
          ((((N + 1 : ℕ) : ℝ)⁻¹) * C) := by field_simp
      _ < ((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hCavg' hNpos
  let B : E := ∑ n ∈ Finset.range (N + 1),
    ∑ h ∈ Finset.range H, v (n + h)
  have hblockSq : ‖B‖ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) * C :=
    norm_sum_forwardBlocks_sq_le v H (N + 1)
  have hNC : 0 ≤ ((N + 1 : ℕ) : ℝ) * C :=
    (sq_nonneg ‖B‖).trans hblockSq
  have hsqrtSq :
      (Real.sqrt (((N + 1 : ℕ) : ℝ) * C)) ^ 2 =
        ((N + 1 : ℕ) : ℝ) * C :=
    Real.sq_sqrt hNC
  have hroot :
      Real.sqrt (((N + 1 : ℕ) : ℝ) * C) <
        (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hupper :
        ((N + 1 : ℕ) : ℝ) * C <
          ((ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
      have hfirst :
          ((N + 1 : ℕ) : ℝ) * C <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hCraw hNpos
      calc
        ((N + 1 : ℕ) : ℝ) * C <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (δ * (H : ℝ) ^ 2)) := hfirst
        _ = ((ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
          simp [δ]
          ring
    have hsqrtNonneg :=
      Real.sqrt_nonneg (((N + 1 : ℕ) : ℝ) * C)
    have hrhspos :
        0 < (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hboundary :
      2 * (H : ℝ) ^ 2 * M <
        (ε / 2) * (H : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hN₀real : (4 * (H : ℝ) * M / ε) < (N₀ : ℝ) := hN₀
    have hNreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
    have hratio : (4 * (H : ℝ) * M / ε) <
        ((N + 1 : ℕ) : ℝ) := by
      calc
        4 * (H : ℝ) * M / ε < (N₀ : ℝ) := hN₀real
        _ ≤ (N : ℝ) := hNreal
        _ < ((N + 1 : ℕ) : ℝ) := by norm_num
    have hlarge : 4 * (H : ℝ) * M <
        ε * ((N + 1 : ℕ) : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).1 hratio
    nlinarith
  have hvdc := finite_vanDerCorput v M H (N + 1)
    (fun n ↦ hu (i + n))
  change (H : ℝ) *
      ‖∑ n ∈ Finset.range (N + 1), v n‖ ≤
    Real.sqrt (((N + 1 : ℕ) : ℝ) * C) +
      2 * (H : ℝ) ^ 2 * M at hvdc
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ n ∈ Finset.range (N + 1), v n‖ <
        ε * ((N + 1 : ℕ) : ℝ) := by
    nlinarith
  rw [inv_mul_lt_iff₀ hNpos]
  simpa only [v, mul_comm] using hsum

end InnerProduct

end Chapter02.VanDerCorput
