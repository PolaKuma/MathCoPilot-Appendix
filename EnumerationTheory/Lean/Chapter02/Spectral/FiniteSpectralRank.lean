import Chapter02.Spectral.CyclicOrthogonalSingularity

open Classical Filter MeasureTheory
open scoped BigOperators

noncomputable section

namespace Chapter02.FiniteSpectralRank

/-- The finite-coordinate Hermitian pairing, kept at the plain function type
so it can be evaluated pointwise inside a direct-integral model. -/
def finiteDot {n : ℕ} (v w : Fin n → ℂ) : ℂ :=
  ∑ k, star (v k) * w k

theorem finiteDot_self_ne_zero {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) :
    finiteDot v v ≠ 0 := by
  intro h
  have heq : finiteDot v v = ((∑ k, ‖v k‖ ^ 2 : ℝ) : ℂ) := by
    simp [finiteDot, Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]
  rw [heq] at h
  have hreal : ∑ k, ‖v k‖ ^ 2 = 0 := by exact_mod_cast h
  have hall : ∀ k, ‖v k‖ ^ 2 = 0 := by
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp hreal k
      (Finset.mem_univ k)
  apply hv
  funext k
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hall k))

/-- In `n` complex coordinates, `n+1` pairwise orthogonal vectors cannot all
be nonzero. This is the pointwise finite spectral-rank obstruction. -/
theorem exists_zero_of_pairwise_finiteDot_zero (n : ℕ)
    (v : Fin (n + 1) → Fin n → ℂ)
    (horth : ∀ i j, i ≠ j → finiteDot (v i) (v j) = 0) :
    ∃ i, v i = 0 := by
  by_contra hz
  push_neg at hz
  have hlin : LinearIndependent ℂ v := Fintype.linearIndependent_iff.mpr (by
    intro g hg i
    have hcoord (k : Fin n) : ∑ j, g j * v j k = 0 := by
      have := congrFun hg k
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have hdot : ∑ k, star (v i k) * (∑ j, g j * v j k) = 0 := by
      simp [hcoord]
    have hdot' : ∑ j, g j * finiteDot (v i) (v j) = 0 := by
      calc
        ∑ j, g j * finiteDot (v i) (v j) =
            ∑ j, ∑ k, star (v i k) * (g j * v j k) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [finiteDot, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = ∑ k, ∑ j, star (v i k) * (g j * v j k) := Finset.sum_comm
        _ = ∑ k, star (v i k) * (∑ j, g j * v j k) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
        _ = 0 := hdot
    have hcollapse : ∑ j, g j * finiteDot (v i) (v j) =
        g i * finiteDot (v i) (v i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [horth i j hji.symm]
        simp
      · simp
    rw [hcollapse] at hdot'
    exact (mul_eq_zero.mp hdot').resolve_right (finiteDot_self_ne_zero (hz i)))
  have hcard := hlin.fintype_card_le_finrank
  rw [Module.finrank_pi, Fintype.card_fin, Fintype.card_fin] at hcard
  omega

/-- Almost-everywhere version of the pointwise rank obstruction. -/
theorem ae_exists_zero_of_pairwise_finiteDot_zero {X : Type*}
    [MeasurableSpace X] (μ : Measure X) (n : ℕ)
    (v : Fin (n + 1) → X → Fin n → ℂ)
    (horth : ∀ i j, i ≠ j →
      ∀ᵐ z ∂μ, finiteDot (v i z) (v j z) = 0) :
    ∀ᵐ z ∂μ, ∃ i, v i z = 0 := by
  have hall : ∀ᵐ z ∂μ, ∀ i j, i ≠ j →
      finiteDot (v i z) (v j z) = 0 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hij).elim
    · exact (horth i j hij).mono fun _ hz _ ↦ hz
  filter_upwards [hall] with z hz
  exact exists_zero_of_pairwise_finiteDot_zero n (fun i ↦ v i z) hz

end Chapter02.FiniteSpectralRank
