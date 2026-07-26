import Chapter00.PerronFrobenius.PerronFrobenius
import MCMC.Finite.Convergence

noncomputable section

open Classical Filter Topology
open scoped BigOperators

namespace Chapter00

private def stochasticScale {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (lam : ℝ) (v : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j ↦ A i j * v j / (lam * v i)

private theorem stochasticScale_pow {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    {lam : ℝ} {v : Fin k → ℝ} (hlam : 0 < lam) (hv : ∀ i, 0 < v i) :
    ∀ n i j, (stochasticScale A lam v ^ n) i j =
      (A ^ n) i j * v j / (lam ^ n * v i) := by
  intro n
  induction n with
  | zero =>
      intro i j
      by_cases hij : i = j
      · subst j
        simp [stochasticScale, Matrix.one_apply, (hv i).ne']
      · simp [stochasticScale, Matrix.one_apply, hij]
  | succ n ih =>
      intro i j
      rw [pow_succ, pow_succ, Matrix.mul_apply]
      simp_rw [ih]
      have hlamn : lam ^ n ≠ 0 := pow_ne_zero _ hlam.ne'
      have hlam0 : lam ≠ 0 := hlam.ne'
      calc
        ∑ q, ((A ^ n) i q * v q / (lam ^ n * v i)) *
            stochasticScale A lam v q j
            = ∑ q, ((A ^ n) i q * A q j) * v j /
                (lam ^ (n + 1) * v i) := by
              apply Finset.sum_congr rfl
              intro q _
              dsimp [stochasticScale]
              field_simp [hlamn, hlam0, (hv i).ne', (hv q).ne']
              ring
        _ = (∑ q, (A ^ n) i q * A q j) * v j /
              (lam ^ (n + 1) * v i) := by
              rw [Finset.sum_mul, Finset.sum_div]
        _ = (A ^ (n + 1)) i j * v j / (lam ^ (n + 1) * v i) := rfl

theorem primitivePerronFrobeniusEntrywiseLimit
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) (lam : ℝ)
    (u v : Fin k → ℝ)
    (hk : 0 < k) (hlam : 0 < lam)
    (hIrr : IsIrreducibleNonnegativeMatrix k A)
    (hPrim : IsAperiodicNonnegativeMatrix k A)
    (huvpos : ∀ i, 0 < u i ∧ 0 < v i)
    (hu : ∀ j, (∑ i, u i * A i j) = lam * u j)
    (hv : ∀ i, (∑ j, A i j * v j) = lam * v i)
    (hnorm : (∑ i, u i * v i) = 1) :
    ∀ i j : Fin k,
      Tendsto (fun n : ℕ ↦ (A ^ n) i j / lam ^ n) atTop
        (nhds (v i * u j)) := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let P := stochasticScale A lam v
  let pi : stdSimplex ℝ (Fin k) :=
    ⟨fun i ↦ u i * v i, by
      constructor
      · intro i
        exact mul_nonneg (le_of_lt (huvpos i).1) (le_of_lt (huvpos i).2)
      · exact hnorm⟩
  have hPstoch : MCMC.Finite.IsStochastic P := by
    constructor
    · intro i j
      exact div_nonneg (mul_nonneg (hIrr.1 i j) (le_of_lt (huvpos j).2))
        (mul_nonneg (le_of_lt hlam) (le_of_lt (huvpos i).2))
    · intro i
      calc
        ∑ j, P i j = (∑ j, A i j * v j) / (lam * v i) := by
          simp [P, stochasticScale, Finset.sum_div]
        _ = (lam * v i) / (lam * v i) := by rw [hv i]
        _ = 1 := div_self (mul_ne_zero hlam.ne' (huvpos i).2.ne')
  have hPstationary : MCMC.Finite.IsStationary P pi := by
    ext j
    change ∑ i, P i j * (u i * v i) = u j * v j
    calc
      ∑ i, P i j * (u i * v i) = ∑ i, (u i * A i j) * v j / lam := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [P, stochasticScale]
        field_simp [hlam.ne', (huvpos i).2.ne']
      _ = (∑ i, u i * A i j) * v j / lam := by
        rw [Finset.sum_mul, Finset.sum_div]
      _ = (lam * u j) * v j / lam := by rw [hu j]
      _ = u j * v j := by field_simp [hlam.ne']
  have hPprim : P.IsPrimitive := by
    rcases hPrim.2 with ⟨m, hm, hmpos⟩
    refine ⟨hPstoch.1, ⟨m, hm, ?_⟩⟩
    intro i j
    rw [stochasticScale_pow A hlam (fun q ↦ (huvpos q).2) m i j]
    exact div_pos (mul_pos (hmpos i j) (huvpos j).2)
      (mul_pos (pow_pos hlam _) (huvpos i).2)
  have hPirred : P.IsIrreducible := Matrix.IsPrimitive.isIrreducible hPprim
  let hMCMC : MCMC.Finite.IsMCMC P pi :=
    { stochastic := hPstoch
      stationary := hPstationary
      irreducible := hPirred
      primitive := hPprim }
  have hconv : Tendsto (fun n : ℕ ↦ P ^ n) atTop
      (nhds (MCMC.Finite.LimitMatrix pi)) :=
    MCMC.Finite.convergence_to_stationarity P pi hMCMC
  intro i j
  have hentry : Tendsto (fun n : ℕ ↦ (P ^ n) i j) atTop
      (nhds (u j * v j)) := by
    have hev : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ ↦ M i j) :=
      (continuous_apply j).comp (continuous_apply i)
    simpa [MCMC.Finite.LimitMatrix, pi] using (hev.tendsto _).comp hconv
  have hscaled := hentry.mul_const (v i / v j)
  convert hscaled using 1
  · ext n
    rw [stochasticScale_pow A hlam (fun q ↦ (huvpos q).2) n i j]
    field_simp [hlam.ne', (huvpos i).2.ne', (huvpos j).2.ne']
  · field_simp [(huvpos j).2.ne']

end Chapter00
