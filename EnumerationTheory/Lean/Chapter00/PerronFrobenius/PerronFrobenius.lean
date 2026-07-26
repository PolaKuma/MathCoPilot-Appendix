import Chapter00.Common
import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Multiplicity

noncomputable section

open Classical
open scoped BigOperators Matrix

namespace Chapter00

open Matrix

theorem IsIrreducibleNonnegativeMatrix.toMatrixIsIrreducible {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsIrreducibleNonnegativeMatrix k A) :
    A.IsIrreducible :=
  (Matrix.isIrreducible_iff_exists_pow_pos hA.1).2 hA.2

theorem IsAperiodicNonnegativeMatrix.toMatrixIsPrimitive {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsAperiodicNonnegativeMatrix k A) :
    A.IsPrimitive := by
  rcases hA.2 with ⟨n, hn, hpos⟩
  exact ⟨hA.1, ⟨n, hn, hpos⟩⟩

theorem nonnegativeMatrix_zero (k : ℕ) :
    IsNonnegativeMatrix k (0 : Matrix (Fin k) (Fin k) ℝ) := by
  intro i j
  simp

theorem nonnegativeMatrix_one (k : ℕ) :
    IsNonnegativeMatrix k (1 : Matrix (Fin k) (Fin k) ℝ) := by
  intro i j
  simp only [Matrix.one_apply]
  split <;> positivity

theorem IsNonnegativeMatrix.add {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : IsNonnegativeMatrix k A) (hB : IsNonnegativeMatrix k B) :
    IsNonnegativeMatrix k (A + B) := by
  intro i j
  exact add_nonneg (hA i j) (hB i j)

theorem IsNonnegativeMatrix.mul {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : IsNonnegativeMatrix k A) (hB : IsNonnegativeMatrix k B) :
    IsNonnegativeMatrix k (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hA i x) (hB x j)

theorem IsNonnegativeMatrix.pow {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : IsNonnegativeMatrix k A) : ∀ n : ℕ, IsNonnegativeMatrix k (A ^ n)
  | 0 => by simpa using nonnegativeMatrix_one k
  | n + 1 => by
      rw [pow_succ]
      exact (hA.pow n).mul hA

theorem IsAperiodicNonnegativeMatrix.irreducible {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsAperiodicNonnegativeMatrix k A) :
    IsIrreducibleNonnegativeMatrix k A := by
  refine ⟨hA.1, ?_⟩
  rcases hA.2 with ⟨n, hn, hpos⟩
  intro i j
  exact ⟨n, hn, hpos i j⟩

theorem IsIrreducibleNonnegativeMatrix.transpose {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsIrreducibleNonnegativeMatrix k A) :
    IsIrreducibleNonnegativeMatrix k A.transpose := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact hA.1 j i
  · intro i j
    rcases hA.2 j i with ⟨n, hn, hpos⟩
    refine ⟨n, hn, ?_⟩
    simpa only [← Matrix.transpose_pow, Matrix.transpose_apply] using hpos

theorem nonnegative_mulVec {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    {v : Fin k → ℝ} (hA : IsNonnegativeMatrix k A) (hv : ∀ i, 0 ≤ v i) (i : Fin k) :
    0 ≤ Finset.univ.sum fun j : Fin k => A i j * v j := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hv j)

theorem nonnegative_vecMul {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    {u : Fin k → ℝ} (hA : IsNonnegativeMatrix k A) (hu : ∀ i, 0 ≤ u i) (j : Fin k) :
    0 ≤ Finset.univ.sum fun i : Fin k => u i * A i j := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (hA i j)

theorem matrixPower_mulVec_eigenvector {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    {lam : ℝ} {v : Fin k → ℝ}
    (hv : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i) :
    ∀ n i, (Finset.univ.sum fun j : Fin k => (A ^ n) i j * v j) = lam ^ n * v i := by
  have hv' : A *ᵥ v = lam • v := by
    ext i
    simpa [Matrix.mulVec, Pi.smul_apply] using hv i
  have hp : ∀ n : ℕ, (A ^ n) *ᵥ v = (lam ^ n) • v := by
    intro n
    induction n with
    | zero => simp [Matrix.one_mulVec]
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_smul, ih]
        simp [pow_succ, smul_smul, mul_comm]
  intro n i
  simpa [Matrix.mulVec, Pi.smul_apply] using congrFun (hp n) i

theorem irreducible_rightEigenvector_strictlyPositive {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {lam : ℝ} {v : Fin k → ℝ}
    (hA : IsIrreducibleNonnegativeMatrix k A)
    (hv0 : ∀ i, 0 ≤ v i) (hvne : v ≠ 0)
    (heig : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i) :
    0 < lam ∧ ∀ i, 0 < v i := by
  have hex : ∃ t, v t ≠ 0 := by
    by_contra h
    push_neg at h
    apply hvne
    funext t
    simpa using h t
  rcases hex with ⟨t, hvtne⟩
  have hvt : 0 < v t := lt_of_le_of_ne (hv0 t) (Ne.symm hvtne)
  have hvpos : ∀ i, 0 < v i := by
    intro i
    rcases hA.2 i t with ⟨n, hn, hpower⟩
    have hterm : 0 < (A ^ n) i t * v t := mul_pos hpower hvt
    have hle : (A ^ n) i t * v t ≤
        Finset.univ.sum fun j : Fin k => (A ^ n) i j * v j := by
      simpa using (Finset.single_le_sum (s := Finset.univ)
        (fun j _ => mul_nonneg (hA.1.pow n i j) (hv0 j)) (Finset.mem_univ t))
    have hprod : 0 < lam ^ n * v i := by
      rw [← matrixPower_mulVec_eigenvector heig n i]
      exact hterm.trans_le hle
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · exact False.elim (not_lt_of_ge (hv0 i) h.2)
  have hlam_nonneg : 0 ≤ lam := by
    have hsum := nonnegative_mulVec hA.1 hv0 t
    rw [heig t] at hsum
    exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hsum) (hvpos t)
  have hlam_ne : lam ≠ 0 := by
    rcases hA.2 t t with ⟨n, hn, hpower⟩
    have hterm : 0 < (A ^ n) t t * v t := mul_pos hpower hvt
    have hle : (A ^ n) t t * v t ≤
        Finset.univ.sum fun j : Fin k => (A ^ n) t j * v j := by
      simpa using (Finset.single_le_sum (s := Finset.univ)
        (fun j _ => mul_nonneg (hA.1.pow n t j) (hv0 j)) (Finset.mem_univ t))
    intro hlam
    have := hterm.trans_le hle
    rw [matrixPower_mulVec_eigenvector heig n t, hlam] at this
    rw [zero_pow (Nat.ne_of_gt hn), zero_mul] at this
    exact (lt_irrefl 0) this
  exact ⟨lt_of_le_of_ne hlam_nonneg (Ne.symm hlam_ne), hvpos⟩

theorem irreducible_leftEigenvector_strictlyPositive {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {lam : ℝ} {u : Fin k → ℝ}
    (hA : IsIrreducibleNonnegativeMatrix k A)
    (hu0 : ∀ i, 0 ≤ u i) (hune : u ≠ 0)
    (heig : ∀ j, (Finset.univ.sum fun i : Fin k => u i * A i j) = lam * u j) :
    0 < lam ∧ ∀ i, 0 < u i := by
  apply irreducible_rightEigenvector_strictlyPositive hA.transpose hu0 hune
  intro j
  simpa [Matrix.transpose_apply, mul_comm] using heig j

theorem complexEigenvalue_norm_le_of_positive_rightEigenvector {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {lam : ℝ} {v : Fin k → ℝ}
    (hk : 0 < k) (hA0 : IsNonnegativeMatrix k A)
    (hvpos : ∀ i, 0 < v i)
    (hv : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i)
    {z : ℂ} {w : Fin k → ℂ} (hwne : w ≠ 0)
    (hw : ∀ i, (Finset.univ.sum fun j : Fin k => (A i j : ℂ) * w j) = z * w i) :
    ‖z‖ ≤ lam := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let ratio : Fin k → ℝ := fun i => ‖w i‖ / v i
  rcases Finite.exists_max ratio with ⟨i, hi⟩
  have hex : ∃ t, w t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hwne (funext h)
  rcases hex with ⟨t, hwt⟩
  have hratio_t : 0 < ratio t := div_pos (norm_pos_iff.mpr hwt) (hvpos t)
  have hratio_i : 0 < ratio i := hratio_t.trans_le (hi t)
  have hwi : 0 < ‖w i‖ := by
    by_contra h
    have hz : ‖w i‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    have : ratio i = 0 := by simp [ratio, hz]
    linarith
  have hcoord (j : Fin k) : ‖w j‖ ≤ ratio i * v j := by
    apply (div_le_iff₀ (hvpos j)).mp
    exact hi j
  have hnormsum :
      ‖Finset.univ.sum fun j : Fin k => (A i j : ℂ) * w j‖ ≤
        Finset.univ.sum fun j : Fin k => A i j * ‖w j‖ := by
    calc
      ‖Finset.univ.sum fun j : Fin k => (A i j : ℂ) * w j‖ ≤
          Finset.univ.sum fun j : Fin k => ‖(A i j : ℂ) * w j‖ :=
        norm_sum_le _ _
      _ = Finset.univ.sum fun j : Fin k => A i j * ‖w j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA0 i j)]
  have hsum :
      (Finset.univ.sum fun j : Fin k => A i j * ‖w j‖) ≤
        ratio i * (Finset.univ.sum fun j : Fin k => A i j * v j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      A i j * ‖w j‖ ≤ A i j * (ratio i * v j) :=
        mul_le_mul_of_nonneg_left (hcoord j) (hA0 i j)
      _ = ratio i * (A i j * v j) := by ring
  have hratio_coord : ratio i * v i = ‖w i‖ := by
    dsimp [ratio]
    field_simp [ne_of_gt (hvpos i)]
  have hmain : ‖z‖ * ‖w i‖ ≤ lam * ‖w i‖ := by
    calc
      ‖z‖ * ‖w i‖ = ‖z * w i‖ := by rw [norm_mul]
      _ = ‖Finset.univ.sum fun j : Fin k => (A i j : ℂ) * w j‖ := by rw [hw i]
      _ ≤ Finset.univ.sum fun j : Fin k => A i j * ‖w j‖ := hnormsum
      _ ≤ ratio i * (Finset.univ.sum fun j : Fin k => A i j * v j) := hsum
      _ = ratio i * (lam * v i) := by rw [hv i]
      _ = lam * ‖w i‖ := by
        calc
          ratio i * (lam * v i) = lam * (ratio i * v i) := by ring
          _ = lam * ‖w i‖ := by rw [hratio_coord]
  nlinarith

theorem irreducible_rightEigenvector_unique {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {lam : ℝ} {v w : Fin k → ℝ}
    (hk : 0 < k) (hA : IsIrreducibleNonnegativeMatrix k A)
    (hvpos : ∀ i, 0 < v i)
    (hv : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i)
    (hw : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * w j) = lam * w i) :
    ∃ c : ℝ, w = fun i => c * v i := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let ratio : Fin k → ℝ := fun i => w i / v i
  rcases Finite.exists_min ratio with ⟨i, hi⟩
  let c := ratio i
  let x : Fin k → ℝ := fun j => w j - c * v j
  have hx0 : ∀ j, 0 ≤ x j := by
    intro j
    have hratio := hi j
    have hmul := (le_div_iff₀ (hvpos j)).mp hratio
    simpa [x, c, ratio] using sub_nonneg.mpr hmul
  have hxi : x i = 0 := by
    dsimp [x, c, ratio]
    field_simp [ne_of_gt (hvpos i)]
    ring
  have hxEig : ∀ j,
      (Finset.univ.sum fun t : Fin k => A j t * x t) = lam * x j := by
    intro j
    calc
      (Finset.univ.sum fun t : Fin k => A j t * x t) =
          (Finset.univ.sum fun t : Fin k => A j t * w t) -
            (Finset.univ.sum fun t : Fin k => A j t * (c * v t)) := by
        simp only [x, mul_sub, Finset.sum_sub_distrib]
      _ = (Finset.univ.sum fun t : Fin k => A j t * w t) -
            c * (Finset.univ.sum fun t : Fin k => A j t * v t) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = lam * x j := by rw [hw j, hv j]; simp only [x]; ring
  by_cases hxeq : x = 0
  · refine ⟨c, ?_⟩
    funext j
    have := congrFun hxeq j
    simpa [x] using sub_eq_zero.mp this
  · have hxpos := (irreducible_rightEigenvector_strictlyPositive hA hx0 hxeq hxEig).2 i
    rw [hxi] at hxpos
    exact False.elim (lt_irrefl 0 hxpos)

theorem no_generalized_rightEigenvector_of_positive_left_right {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {lam : ℝ} {u v : Fin k → ℝ}
    (hk : 0 < k) (hupos : ∀ i, 0 < u i) (hvpos : ∀ i, 0 < v i)
    (hu : ∀ j, (Finset.univ.sum fun i : Fin k => u i * A i j) = lam * u j) :
    ¬ ∃ w : Fin k → ℝ,
      ∀ i, (Finset.univ.sum fun j : Fin k => A i j * w j) - lam * w i = v i := by
  rintro ⟨w, hw⟩
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hpos : 0 < Finset.univ.sum fun i : Fin k => u i * v i := by
    exact Finset.sum_pos' (fun i _ => mul_nonneg (le_of_lt (hupos i)) (le_of_lt (hvpos i)))
      ⟨Classical.choice inferInstance, Finset.mem_univ _,
        mul_pos (hupos _) (hvpos _)⟩
  have hzero : Finset.univ.sum (fun i : Fin k => u i * v i) = 0 := by
    calc
      Finset.univ.sum (fun i : Fin k => u i * v i) =
          Finset.univ.sum (fun i : Fin k =>
            u i * ((Finset.univ.sum fun j : Fin k => A i j * w j) - lam * w i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hw i]
      _ = (Finset.univ.sum fun j : Fin k =>
            w j * (Finset.univ.sum fun i : Fin k => u i * A i j)) -
          lam * (Finset.univ.sum fun i : Fin k => u i * w i) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        congr 1
        · calc
            (Finset.univ.sum fun x : Fin k =>
                u x * (Finset.univ.sum fun j : Fin k => A x j * w j)) =
                Finset.univ.sum fun x : Fin k =>
                  Finset.univ.sum fun j : Fin k => u x * (A x j * w j) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.mul_sum]
            _ = Finset.univ.sum fun j : Fin k =>
                  Finset.univ.sum fun i : Fin k => u i * (A i j * w j) :=
              Finset.sum_comm
            _ = Finset.univ.sum fun j : Fin k =>
                  w j * (Finset.univ.sum fun i : Fin k => u i * A i j) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = 0 := by
        simp_rw [hu]
        have hs : (Finset.univ.sum fun j : Fin k => w j * (lam * u j)) =
            lam * (Finset.univ.sum fun i : Fin k => u i * w i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hs]
        ring
  linarith

theorem realEigenvalue_le_of_positive_rightEigenvector {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {lam z : ℝ} {v w : Fin k → ℝ}
    (hk : 0 < k) (hA0 : IsNonnegativeMatrix k A) (hvpos : ∀ i, 0 < v i)
    (hv : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i)
    (hwne : w ≠ 0)
    (hw : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * w j) = z * w i) :
    z ≤ lam := by
  let wc : Fin k → ℂ := fun i => (w i : ℂ)
  have hwcne : wc ≠ 0 := by
    intro h
    apply hwne
    funext i
    have hi := congrFun h i
    change (w i : ℂ) = 0 at hi
    exact_mod_cast hi
  have hwc : ∀ i,
      (Finset.univ.sum fun j : Fin k => (A i j : ℂ) * wc j) = (z : ℂ) * wc i := by
    intro i
    dsimp [wc]
    exact_mod_cast hw i
  have hnorm := complexEigenvalue_norm_le_of_positive_rightEigenvector
    hk hA0 hvpos hv hwcne hwc
  have habs : |z| ≤ lam := by simpa [Complex.norm_real, Real.norm_eq_abs] using hnorm
  exact (le_abs_self z).trans habs

theorem irreducible_nonnegative_eigenvalue_unique {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} {lam z : ℝ} {v w : Fin k → ℝ}
    (hk : 0 < k) (hA : IsIrreducibleNonnegativeMatrix k A)
    (hvpos : ∀ i, 0 < v i)
    (hv : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i)
    (hw0 : ∀ i, 0 ≤ w i) (hwne : w ≠ 0)
    (hw : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * w j) = z * w i) :
    z = lam := by
  have hwpos := (irreducible_rightEigenvector_strictlyPositive hA hw0 hwne hw).2
  have hzle : z ≤ lam :=
    realEigenvalue_le_of_positive_rightEigenvector hk hA.1 hvpos hv hwne hw
  have hvne : v ≠ 0 := by
    intro h
    let i0 : Fin k := ⟨0, hk⟩
    have hz : v i0 = 0 := by rw [h]; rfl
    exact (ne_of_gt (hvpos i0)) hz
  have hlamle : lam ≤ z :=
    realEigenvalue_le_of_positive_rightEigenvector hk hA.1 hwpos hw hvne hv
  exact le_antisymm hzle hlamle

structure PerronFrobeniusBaseData (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) where
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  spectral_bound : ∀ z : ℂ, IsComplexEigenvalueOfRealMatrix k A z → ‖z‖ ≤ lam
  row_bounds : ∃ imin imax : Fin k,
    (Finset.univ.sum fun j : Fin k => A imin j) ≤ lam ∧
      lam ≤ Finset.univ.sum fun j : Fin k => A imax j
  u : Fin k → ℝ
  v : Fin k → ℝ
  u_ne : u ≠ 0
  v_ne : v ≠ 0
  u_nonneg : ∀ i, 0 ≤ u i
  v_nonneg : ∀ i, 0 ≤ v i
  left_eigen : ∀ j, (Finset.univ.sum fun i : Fin k => u i * A i j) = lam * u j
  right_eigen : ∀ i, (Finset.univ.sum fun j : Fin k => A i j * v j) = lam * v i

theorem PerronFrobeniusBaseData.toStatement {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (D : PerronFrobeniusBaseData k A) :
    IsPerronFrobeniusMatrixStatement k A := by
  intro hk _
  refine ⟨D.lam, D.lam_nonneg, D.spectral_bound, D.row_bounds,
    D.u, D.v, D.u_ne, D.v_ne, ?_, D.left_eigen, D.right_eigen, ?_⟩
  · intro i
    exact ⟨D.u_nonneg i, D.v_nonneg i⟩
  · intro hIrr
    have huStrict := irreducible_leftEigenvector_strictlyPositive
      hIrr D.u_nonneg D.u_ne D.left_eigen
    have hvStrict := irreducible_rightEigenvector_strictlyPositive
      hIrr D.v_nonneg D.v_ne D.right_eigen
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨huStrict.2 i, hvStrict.2 i⟩
    · intro w hw
      exact irreducible_rightEigenvector_unique hk hIrr hvStrict.2 D.right_eigen hw
    · exact no_generalized_rightEigenvector_of_positive_left_right
        hk huStrict.2 hvStrict.2 D.left_eigen
    · intro z hz
      rcases hz with ⟨w, hw0, hwne, hw⟩
      exact irreducible_nonnegative_eigenvalue_unique
        hk hIrr hvStrict.2 D.right_eigen hw0 hwne hw

end Chapter00
