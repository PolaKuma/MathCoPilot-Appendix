import Chapter03.Section02

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter03
namespace Section03

/--
Source: Definition 3.3.1, Chapter 3, Section 3.
A number `u = [a₁, a₂, …] ∈ [0,1]` is badly approximable if the partial
quotients are bounded.
-/
def badlyApproximable (u : ℝ) : Prop :=
  IsUnitIntervalBadlyApproximable u

/--
Source: Proposition 3.3.2, Chapter 3, Section 3.
A number `u ∈ [0,1]` is badly approximable iff there is `ε > 0` such that every
rational `p/q` satisfies `|u - p/q| ≥ ε/q²`.
-/
theorem badlyApproximableIffDiophantineLowerBound (u : ℝ)
    (hu : u ∈ Set.Icc 0 1) :
    badlyApproximable u ↔ HasDiophantineBadApproximationBound u := by
  exact Section01.unitIntervalBadlyApproximable_iff_diophantine u hu

/--
Source: Definition 3.3.3, Chapter 3, Section 3.
A real number is a quadratic irrational if it is irrational and satisfies a
nontrivial quadratic equation with integer coefficients.
-/
def quadraticIrrational (u : ℝ) : Prop :=
  IsQuadraticIrrational u

/--
Source: Definition 3.3.4, Chapter 3, Section 3.
A continued fraction `[a₀; a₁, a₂, …]` is eventually periodic if there are
`N ≥ 0` and `k ≥ 1` such that `aₙ₊ₖ = aₙ` for all `n ≥ N`.
-/
def eventuallyPeriodicContinuedFraction (a : PartialQuotients) : Prop :=
  IsEventuallyPeriodic a

/--
Source: Theorem 3.3.5, Chapter 3, Section 3.
Lagrange theorem: for irrational `u`, `u` is a quadratic irrational iff its
continued fraction expansion is eventually periodic.
-/
theorem lagrangeQuadraticIrrationalIffEventuallyPeriodic (u : ℝ)
    (hirr : Irrational u) :
    IsQuadraticIrrational u ↔ HasEventuallyPeriodicContinuedFraction u := by
  constructor
  · exact Section01.quadraticIrrational_hasEventuallyPeriodicExpansion u
  · exact Section01.eventuallyPeriodicExpansion_isQuadratic u hirr

private theorem eventuallyPeriodicTailBounded (a : PartialQuotients)
    (hperiodic : IsEventuallyPeriodic a) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, a.tail n ≤ M := by
  rcases hperiodic with ⟨N, k, hk, hperiodic⟩
  let B := (Finset.range (N + k)).sup a.tail
  refine ⟨B + 1, Nat.zero_lt_succ B, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < N + k
      · have hle : a.tail n ≤ B := by
          exact Finset.le_sup (f := a.tail) (Finset.mem_range.mpr hn)
        omega
      · let m := n + 1 - k
        have hnk : N + k < n + 1 := by omega
        have hmNstrict : N < m := by simp only [m]; omega
        have hmN : N ≤ m := hmNstrict.le
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le N) hmNstrict
        have hmk : m + k = n + 1 := by simp only [m]; omega
        have heq := hperiodic m hmN
        rw [hmk] at heq
        cases hm : m with
        | zero => omega
        | succ r =>
            simp only [partialQuotient, hm] at heq
            have hnat : a.tail n = a.tail r := by exact_mod_cast heq
            rw [hnat]
            exact ih r (by simp only [m] at hm hmk; omega)

/--
Source: Corollary 3.3.6, Chapter 3, Section 3.
Every quadratic irrational is badly approximable.
-/
theorem quadraticIrrationalIsBadlyApproximable (u : ℝ)
    (hquad : IsQuadraticIrrational u) :
    IsBadlyApproximable u := by
  obtain ⟨a, hexp, hperiodic⟩ :=
    (lagrangeQuadraticIrrationalIffEventuallyPeriodic u hquad.1).mp hquad
  obtain ⟨M, hM, hbound⟩ := eventuallyPeriodicTailBounded a hperiodic
  exact ⟨a, M, hexp, hM, hbound⟩

end Section03
end Chapter03
