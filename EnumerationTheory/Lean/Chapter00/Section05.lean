import Chapter00.Section04
import Chapter00.PerronFrobenius.PerronFrobeniusGeneral
import Chapter00.PerronFrobenius.PrimitiveAsymptotics
import Chapter00.Renewal.RenewalMain

noncomputable section

open Classical Filter
open scoped BigOperators

namespace Chapter00
namespace Section05

/--
Source: Theorem 0.5.2, Chapter 0, Section 5.
Perron-Frobenius theorem for a nonnegative real matrix, including the
distinguished nonnegative eigenvalue, bounds by row sums, nonnegative left and
right eigenvectors, and the irreducible case.
-/
theorem perronFrobeniusTheorem (k : ℕ) (A : Fin k -> Fin k -> ℝ) :
    IsPerronFrobeniusMatrixStatement k A := by
  intro hk hA
  obtain ⟨D, -⟩ := nonnegativePerronFrobeniusBaseData hk A hA
  exact D.toStatement hk hA

/--
Source: Theorem 0.5.3, Chapter 0, Section 5.
For an irreducible aperiodic nonnegative matrix, normalized powers converge to
the rank-one Perron-Frobenius limit.
-/
theorem primitiveMatrixPerronFrobeniusAsymptotics
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) (lam : ℝ)
    (u v : Fin k -> ℝ) :
    0 < k -> 0 < lam -> IsIrreducibleNonnegativeMatrix k A ->
      IsAperiodicNonnegativeMatrix k A ->
      (∀ i, 0 < u i ∧ 0 < v i) ->
      (∀ j, (Finset.univ.sum fun i : Fin k => u i * A i j) = lam * u j) ->
      (∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i) ->
      (Finset.univ.sum fun i : Fin k => u i * v i) = 1 ->
      ∀ i j : Fin k,
        Tendsto (fun n : ℕ => (A ^ n) i j / lam ^ n) atTop (nhds (v i * u j)) := by
  intro hk hlam hIrr hPrim huv hu hv hnorm
  exact primitivePerronFrobeniusEntrywiseLimit
    k A lam u v hk hlam hIrr hPrim huv hu hv hnorm

/--
Source: Theorem 0.5.4, Chapter 0, Section 5.
Renewal theorem for bounded nonnegative renewal data satisfying the renewal
equation and an aperiodicity condition.
-/
theorem renewalTheorem (c d u : ℕ -> ℝ) :
    RenewalEquationStatement c d u := by
  intro _ _ hdata haper hrec hctsum hdtsum
  exact Renewal.renewalTheorem_core c d u hdata haper hrec hctsum hdtsum

/--
Source: Definition 0.5.1, Chapter 0, Section 5.
Nonnegative matrices, irreducibility, aperiodicity, left and right
eigenvectors, and stochastic matrices.
-/
def nonnegativeMatrixIrreducibleAperiodicDefinition
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsNonnegativeMatrix k A

/-- Source: Definition 0.5.1(2). Irreducibility uses entries of matrix powers. -/
def irreducibleMatrixDefinition
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ i j : Fin k, ∃ n : ℕ, 0 < n ∧ 0 < (A ^ n) i j

/-- Source: Definition 0.5.1(3). Aperiodicity (primitivity). -/
def aperiodicMatrixDefinition
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ i j : Fin k, 0 < (A ^ n) i j

/-- Source: Definition 0.5.1. Left and right eigenvectors. -/
def leftRightEigenvectorDefinition (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℝ) (lam : ℝ) (u v : Fin k -> ℝ) : Prop × Prop :=
  (∀ j, (Finset.univ.sum fun i : Fin k => u i * A i j) = lam * u j,
    ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i)

/-- Source: Definition 0.5.1. A row-stochastic matrix. -/
def stochasticMatrixDefinition (k : ℕ)
    (P : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) ∧
    ∀ i, (Finset.univ.sum fun j : Fin k => P i j) = 1

end Section05
end Chapter00
