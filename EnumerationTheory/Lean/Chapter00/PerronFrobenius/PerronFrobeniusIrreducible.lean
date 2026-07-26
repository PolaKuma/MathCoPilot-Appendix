import Chapter00.PerronFrobenius.PerronFrobenius

noncomputable section

open Classical
open scoped BigOperators

namespace Chapter00

theorem irreduciblePerronFrobeniusBaseData {k : ℕ}
    (hk : 0 < k) (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : IsIrreducibleNonnegativeMatrix k A) :
    ∃ D : PerronFrobeniusBaseData k A, True := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hMI : A.IsIrreducible := hA.toMatrixIsIrreducible
  obtain ⟨lam, v, hlam, hvpos, hv, hroot⟩ :=
    Matrix.perron_root_eq_positive_eigenvalue hMI hA.1
  have hvne : v ≠ 0 := by
    intro hv0
    exact (ne_of_gt (hvpos (Classical.arbitrary (Fin k)))) (congrFun hv0 _)
  have hAT : A.transpose.IsIrreducible := Matrix.IsIrreducible.transpose hMI
  obtain ⟨lamT, u, hlamT, hupos, huT, hrootT⟩ :=
    Matrix.perron_root_eq_positive_eigenvalue hAT (fun i j ↦ hA.1 j i)
  have hlamT_eq : lamT = lam := by
    calc
      lamT = Matrix.CollatzWielandt.perronRoot_alt A.transpose := hrootT.symm
      _ = Matrix.CollatzWielandt.perronRoot_alt A :=
        (Matrix.perronRoot_transpose_eq A hMI).symm
      _ = lam := hroot
  have hune : u ≠ 0 := by
    intro hu0
    exact (ne_of_gt (hupos (Classical.arbitrary (Fin k)))) (congrFun hu0 _)
  obtain ⟨imin, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin k)) v Finset.univ_nonempty
  obtain ⟨imax, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin k)) v Finset.univ_nonempty
  have hrow_min : (∑ j, A imin j) ≤ lam := by
    apply (mul_le_mul_iff_of_pos_right (hvpos imin)).mp
    calc
      (∑ j, A imin j) * v imin = ∑ j, A imin j * v imin := by
        rw [Finset.sum_mul]
      _ ≤ ∑ j, A imin j * v j := by
        exact Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ j)) (hA.1 imin j)
      _ = lam * v imin := by
        simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using congrFun hv imin
  have hrow_max : lam ≤ ∑ j, A imax j := by
    apply (mul_le_mul_iff_of_pos_right (hvpos imax)).mp
    calc
      lam * v imax = ∑ j, A imax j * v j := by
        simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using (congrFun hv imax).symm
      _ ≤ ∑ j, A imax j * v imax := by
        exact Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hA.1 imax j)
      _ = (∑ j, A imax j) * v imax := by rw [Finset.sum_mul]
  refine ⟨
    { lam := lam
      lam_nonneg := le_of_lt hlam
      spectral_bound := ?_
      row_bounds := ⟨imin, imax, hrow_min, hrow_max⟩
      u := u
      v := v
      u_ne := hune
      v_ne := hvne
      u_nonneg := fun i ↦ le_of_lt (hupos i)
      v_nonneg := fun i ↦ le_of_lt (hvpos i)
      left_eigen := ?_
      right_eigen := ?_ }, trivial⟩
  · intro z hz
    rcases hz with ⟨w, hwne, hw⟩
    have hspec : z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) := by
      apply Matrix.mem_spectrum_of_eigenvalue hwne
      ext i
      simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using hw i
    simpa [hroot] using Matrix.eigenvalue_abs_le_perron_root hMI hA.1 hspec
  · intro j
    have hu := congrFun huT j
    simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply,
      hlamT_eq, mul_comm] using hu
  · intro i
    simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using congrFun hv i

end Chapter00
