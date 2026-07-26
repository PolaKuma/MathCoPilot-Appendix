import Chapter02.Ergodic.VanDerCorput

open Classical Filter
open scoped BigOperators

noncomputable section

namespace Chapter02.VanDerCorput

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A real array `L h k` gives all fixed forward-pair limits of `u`,
uniformly over translated Cesàro windows. -/
def HasUniformPairLimits (u : ℕ → E) (L : ℕ → ℕ → ℝ) : Prop :=
  ∀ h k : ℕ, ∀ ρ : ℝ, 0 < ρ →
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      |cesaroAverage
          (fun n ↦
            (@inner ℂ E _ (u (i + (n + k))) (u (i + (n + h)))).re) N -
        L h k| < ρ

/-- The fixed pair-limit array has arbitrarily small normalized complete
forward blocks. -/
def HasSmallPairLimitBlocks (L : ℕ → ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ H : ℕ, 0 < H ∧
      (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, L h k) <
        δ * (H : ℝ) ^ 2

/-- Uniform fixed pair limits reduce uniform van der Corput block decay to
the finite-dimensional task of finding small blocks in the limit array.

This isolates the analytic bookkeeping from the Host--Kra/Gowers estimate:
the latter only has to establish `HasSmallPairLimitBlocks`. -/
theorem hasUniformVanDerCorputBlockDecay_of_pairLimits
    (u : ℕ → E) (L : ℕ → ℕ → ℝ)
    (hlimits : HasUniformPairLimits u L)
    (hsmall : HasSmallPairLimitBlocks L) :
    HasUniformVanDerCorputBlockDecay u := by
  intro δ hδ
  obtain ⟨H, hH, hstrict⟩ := hsmall δ hδ
  refine ⟨H, hH, ?_⟩
  let S : ℝ :=
    ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, L h k
  have hstrictS : S < δ * (H : ℝ) ^ 2 := by
    simpa only [S] using hstrict
  let ρ : ℝ :=
    (δ * (H : ℝ) ^ 2 - S) /
      (2 * ((H : ℝ) ^ 2 + 1))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply div_pos
    · linarith
    · positivity
  have hall :
      ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ Finset.range H, ∀ k ∈ Finset.range H, ∀ i : ℕ,
          |cesaroAverage
              (fun n ↦
                (@inner ℂ E _
                  (u (i + (n + k))) (u (i + (n + h)))).re) N -
            L h k| < ρ := by
    rw [Filter.eventually_all_finset]
    intro h hh
    rw [Filter.eventually_all_finset]
    intro k hk
    exact hlimits h k ρ hρ
  filter_upwards [hall] with N hN
  intro i
  let A : ℕ → ℕ → ℝ := fun h k ↦
    cesaroAverage
      (fun n ↦
        (@inner ℂ E _
          (u (i + (n + k))) (u (i + (n + h)))).re) N
  have hdecomp :
      cesaroAverage
        (fun n ↦ ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
          (@inner ℂ E _
            (u (i + (n + k))) (u (i + (n + h)))).re) N =
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k := by
    unfold A cesaroAverage
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_comm]
  have hdiff :
      |(∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k) - S| ≤
        (H : ℝ) ^ 2 * ρ := by
    have hSL :
        S = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, L h k := by
      rfl
    rw [hSL, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      |∑ h ∈ Finset.range H,
          ∑ k ∈ Finset.range H, (A h k - L h k)| ≤
          ∑ h ∈ Finset.range H,
            |∑ k ∈ Finset.range H, (A h k - L h k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range H,
          ∑ k ∈ Finset.range H, |A h k - L h k| := by
        gcongr with h hh
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range H,
          ∑ _k ∈ Finset.range H, ρ := by
        gcongr with h hh k hk
        exact (hN h hh k hk i).le
      _ = (H : ℝ) ^ 2 * ρ := by
        simp
        ring
  rw [hdecomp]
  have hρsmall :
      (H : ℝ) ^ 2 * ρ < δ * (H : ℝ) ^ 2 - S := by
    dsimp [ρ]
    have hgap : 0 < δ * (H : ℝ) ^ 2 - S := sub_pos.mpr hstrictS
    have hden : 0 < 2 * ((H : ℝ) ^ 2 + 1) := by positivity
    rw [div_eq_mul_inv]
    calc
      (H : ℝ) ^ 2 *
          ((δ * (H : ℝ) ^ 2 - S) *
            (2 * ((H : ℝ) ^ 2 + 1))⁻¹) =
          (δ * (H : ℝ) ^ 2 - S) *
            ((H : ℝ) ^ 2 / (2 * ((H : ℝ) ^ 2 + 1))) := by ring
      _ < (δ * (H : ℝ) ^ 2 - S) * 1 := by
        apply mul_lt_mul_of_pos_left _ hgap
        rw [div_lt_one hden]
        nlinarith [sq_nonneg (H : ℝ)]
      _ = δ * (H : ℝ) ^ 2 - S := mul_one _
  have hlower :=
    (le_abs_self
      ((∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, A h k) - S))
  linarith

end Chapter02.VanDerCorput
