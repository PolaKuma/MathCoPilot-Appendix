import Chapter00.PerronFrobenius.PerronFrobeniusIrreducible

noncomputable section

open Classical Filter Set Topology
open scoped BigOperators

namespace Chapter00

private def pfEps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private def pfPerturb {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) :
    Matrix (Fin k) (Fin k) ℝ := fun i j ↦ A i j + pfEps n

private def pfNormalize {k : ℕ} (w : Fin k → ℝ) : Fin k → ℝ :=
  (∑ i, w i)⁻¹ • w

private theorem pfEps_pos (n : ℕ) : 0 < pfEps n := by
  unfold pfEps
  positivity

private theorem pfEps_le_one (n : ℕ) : pfEps n ≤ 1 := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact (div_le_one hden).2 (by linarith)

private theorem pfPerturb_irreducible {k : ℕ} (hk : 0 < k)
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsNonnegativeMatrix k A) (n : ℕ) :
    IsIrreducibleNonnegativeMatrix k (pfPerturb A n) := by
  constructor
  · intro i j
    exact add_nonneg (hA i j) (le_of_lt (pfEps_pos n))
  · intro i j
    refine ⟨1, by norm_num, ?_⟩
    simpa [pfPerturb] using add_pos_of_nonneg_of_pos (hA i j) (pfEps_pos n)

private theorem pfNormalize_mem_stdSimplex {k : ℕ} (hk : 0 < k)
    {w : Fin k → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hwne : w ≠ 0) :
    pfNormalize w ∈ stdSimplex ℝ (Fin k) := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hsum_pos : 0 < ∑ i, w i := by
    obtain ⟨i, hi⟩ := Function.exists_ne_zero_of_ne_zero hwne
    apply Finset.sum_pos' (fun j _ ↦ hw0 j)
    exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hw0 i) hi.symm⟩
  constructor
  · intro i
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hsum_pos)) (hw0 i)
  · change ∑ i, (∑ j, w j)⁻¹ * w i = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hsum_pos)

private theorem pfNormalize_ne_zero {k : ℕ} (hk : 0 < k)
    {w : Fin k → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hwne : w ≠ 0) :
    pfNormalize w ≠ 0 := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  exact ne_zero_of_mem_stdSimplex (pfNormalize_mem_stdSimplex hk hw0 hwne)

private theorem pfNormalize_eigen {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    {lam : ℝ} {w : Fin k → ℝ}
    (hw : Matrix.mulVec A w = lam • w) :
    Matrix.mulVec A (pfNormalize w) = lam • pfNormalize w := by
  rw [pfNormalize, Matrix.mulVec_smul, hw, smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

private def pfData {k : ℕ} (hk : 0 < k) (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : IsNonnegativeMatrix k A) (n : ℕ) :
    PerronFrobeniusBaseData k (pfPerturb A n) :=
  Classical.choose
    (irreduciblePerronFrobeniusBaseData hk (pfPerturb A n)
      (pfPerturb_irreducible hk A hA n))

private def pfBound {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (∑ i, ∑ j, A i j) + k

private theorem pfData_lam_le_bound {k : ℕ} (hk : 0 < k)
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsNonnegativeMatrix k A) (n : ℕ) :
    (pfData hk A hA n).lam ≤ pfBound A := by
  rcases (pfData hk A hA n).row_bounds with ⟨imin, imax, _, hmax⟩
  have hrow_le : (∑ j, A imax j) ≤ ∑ i, ∑ j, A i j := by
    exact Finset.single_le_sum
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hA i j) (Finset.mem_univ imax)
  have hkeps_le : (k : ℝ) * pfEps n ≤ k := by
    simpa using mul_le_mul_of_nonneg_left (pfEps_le_one n) (Nat.cast_nonneg k)
  refine hmax.trans ?_
  calc
    (∑ j, pfPerturb A n imax j) = (∑ j, A imax j) + k * pfEps n := by
      simp [pfPerturb, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ i, ∑ j, A i j) + k := add_le_add hrow_le hkeps_le
    _ = pfBound A := rfl

theorem nonnegativePerronFrobeniusBaseData {k : ℕ} (hk : 0 < k)
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsNonnegativeMatrix k A) :
    ∃ D : PerronFrobeniusBaseData k A, True := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let D : (n : ℕ) → PerronFrobeniusBaseData k (pfPerturb A n) :=
    fun n ↦ pfData hk A hA n
  let un : ℕ → Fin k → ℝ := fun n ↦ pfNormalize (D n).u
  let vn : ℕ → Fin k → ℝ := fun n ↦ pfNormalize (D n).v
  let ln : ℕ → ℝ := fun n ↦ (D n).lam
  have hun_mem : ∀ n, un n ∈ stdSimplex ℝ (Fin k) := by
    intro n
    exact pfNormalize_mem_stdSimplex hk (D n).u_nonneg (D n).u_ne
  have hvn_mem : ∀ n, vn n ∈ stdSimplex ℝ (Fin k) := by
    intro n
    exact pfNormalize_mem_stdSimplex hk (D n).v_nonneg (D n).v_ne
  have hbound_nonneg : 0 ≤ pfBound A := by
    exact add_nonneg (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hA i j)
      (Nat.cast_nonneg k)
  let S : Set (((Fin k → ℝ) × (Fin k → ℝ)) × ℝ) :=
    (stdSimplex ℝ (Fin k) ×ˢ stdSimplex ℝ (Fin k)) ×ˢ Set.Icc 0 (pfBound A)
  let x : ℕ → (((Fin k → ℝ) × (Fin k → ℝ)) × ℝ) :=
    fun n ↦ ((un n, vn n), ln n)
  have hxS : ∀ n, x n ∈ S := by
    intro n
    exact ⟨⟨hun_mem n, hvn_mem n⟩,
      (D n).lam_nonneg, pfData_lam_le_bound hk A hA n⟩
  have hScompact : IsCompact S := by
    exact ((isCompact_stdSimplex (Fin k)).prod (isCompact_stdSimplex (Fin k))).prod
      isCompact_Icc
  obtain ⟨⟨⟨u, v⟩, lam⟩, huvlamS, φ, hφ, hxlim⟩ :=
    hScompact.isSeqCompact hxS
  have hulim : Tendsto (fun n ↦ un (φ n)) atTop (nhds u) := by
    have h := continuous_fst.continuousAt.tendsto.comp
      (continuous_fst.continuousAt.tendsto.comp hxlim)
    simpa [x, Function.comp_def] using h
  have hvlim : Tendsto (fun n ↦ vn (φ n)) atTop (nhds v) := by
    have h := continuous_snd.continuousAt.tendsto.comp
      (continuous_fst.continuousAt.tendsto.comp hxlim)
    simpa [x, Function.comp_def] using h
  have hllim : Tendsto (fun n ↦ ln (φ n)) atTop (nhds lam) := by
    have h := continuous_snd.continuousAt.tendsto.comp hxlim
    simpa [x, Function.comp_def] using h
  have hulim_i (i : Fin k) : Tendsto (fun n ↦ un (φ n) i) atTop (nhds (u i)) :=
    (tendsto_pi_nhds.mp hulim) i
  have hvlim_i (i : Fin k) : Tendsto (fun n ↦ vn (φ n) i) atTop (nhds (v i)) :=
    (tendsto_pi_nhds.mp hvlim) i
  have hepslim : Tendsto (fun n ↦ pfEps (φ n)) atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hright_n : ∀ n,
      Matrix.mulVec (pfPerturb A n) (vn n) = ln n • vn n := by
    intro n
    apply pfNormalize_eigen
    ext i
    simpa [D, ln, Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using (D n).right_eigen i
  have hleft_n : ∀ n,
      Matrix.mulVec (pfPerturb A n).transpose (un n) = ln n • un n := by
    intro n
    apply pfNormalize_eigen
    ext j
    simpa [D, ln, Matrix.mulVec, Pi.smul_apply, smul_eq_mul,
      Matrix.transpose_apply, mul_comm] using (D n).left_eigen j
  have hright : ∀ i, (∑ j, A i j * v j) = lam * v i := by
    intro i
    have hterm : ∀ j : Fin k,
        Tendsto (fun n ↦ pfPerturb A (φ n) i j * vn (φ n) j)
          atTop (nhds (A i j * v j)) := by
      intro j
      have hentry : Tendsto (fun n ↦ pfPerturb A (φ n) i j) atTop (nhds (A i j)) := by
        simpa [pfPerturb] using (tendsto_const_nhds.add hepslim)
      exact hentry.mul (hvlim_i j)
    have hsum := tendsto_finset_sum Finset.univ (fun j _ ↦ hterm j)
    have hrhs := hllim.mul (hvlim_i i)
    exact tendsto_nhds_unique hsum (by
      convert hrhs using 1
      ext n
      simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul, vn, ln] using
        congrFun (hright_n (φ n)) i)
  have hleft : ∀ j, (∑ i, u i * A i j) = lam * u j := by
    intro j
    have hterm : ∀ i : Fin k,
        Tendsto (fun n ↦ un (φ n) i * pfPerturb A (φ n) i j)
          atTop (nhds (u i * A i j)) := by
      intro i
      have hentry : Tendsto (fun n ↦ pfPerturb A (φ n) i j) atTop (nhds (A i j)) := by
        simpa [pfPerturb] using (tendsto_const_nhds.add hepslim)
      exact (hulim_i i).mul hentry
    have hsum := tendsto_finset_sum Finset.univ (fun i _ ↦ hterm i)
    have hrhs := hllim.mul (hulim_i j)
    exact tendsto_nhds_unique hsum (by
      convert hrhs using 1
      ext n
      simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, un, ln,
        Matrix.transpose_apply, mul_comm] using congrFun (hleft_n (φ n)) j)
  rcases huvlamS with ⟨⟨huSimplex, hvSimplex⟩, hlam0, hlamBound⟩
  have hune : u ≠ 0 := ne_zero_of_mem_stdSimplex huSimplex
  have hvne : v ≠ 0 := ne_zero_of_mem_stdSimplex hvSimplex
  -- The remaining spectral and row bounds are inherited from the positive
  -- perturbations; they are established below before packaging the data.
  refine ⟨
    { lam := lam
      lam_nonneg := hlam0
      spectral_bound := ?_
      row_bounds := ?_
      u := u
      v := v
      u_ne := hune
      v_ne := hvne
      u_nonneg := huSimplex.1
      v_nonneg := hvSimplex.1
      left_eigen := hleft
      right_eigen := hright }, trivial⟩
  · intro z hz
    rcases hz with ⟨w, hwne, hw⟩
    let wabs : Fin k → ℝ := fun i ↦ ‖w i‖
    have hwabs0 : ∀ i, 0 ≤ wabs i := fun i ↦ norm_nonneg _
    have hwabsne : wabs ≠ 0 := by
      intro hzero
      apply hwne
      ext i
      exact norm_eq_zero.mp (congrFun hzero i)
    have hweigen :
        Matrix.mulVec (A.map (algebraMap ℝ ℂ)) w = z • w := by
      ext i
      simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using hw i
    have hsubA : ‖z‖ • wabs ≤ Matrix.mulVec A wabs :=
      Matrix.eigenvalue_abs_subinvariant hA hweigen
    have hbound_n : ∀ n, ‖z‖ ≤ ln n := by
      intro n
      have hBn0 : ∀ i j, 0 ≤ pfPerturb A n i j :=
        (pfPerturb_irreducible hk A hA n).1
      have hsubB : ‖z‖ • wabs ≤ Matrix.mulVec (pfPerturb A n) wabs := by
        exact hsubA.trans (fun i ↦ by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_le_sum fun j _ ↦ by
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (le_of_lt (pfEps_pos n))) (hwabs0 j))
      have hleRoot : ‖z‖ ≤ Matrix.CollatzWielandt.perronRoot_alt (pfPerturb A n) :=
        (Matrix.CollatzWielandt.le_of_subinvariant hBn0 hwabs0 hwabsne hsubB).trans
          (Matrix.collatzWielandtFn_le_perronRoot_alt hBn0 hwabs0 hwabsne)
      have hBI : (pfPerturb A n).IsIrreducible :=
        (pfPerturb_irreducible hk A hA n).toMatrixIsIrreducible
      have hvstrict := irreducible_rightEigenvector_strictlyPositive
        (pfPerturb_irreducible hk A hA n) (D n).v_nonneg (D n).v_ne
          (D n).right_eigen
      have hveig : Matrix.mulVec (pfPerturb A n) (D n).v = (D n).lam • (D n).v := by
        ext i
        simpa [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] using (D n).right_eigen i
      have hroot : Matrix.CollatzWielandt.perronRoot_alt (pfPerturb A n) = ln n := by
        simpa [ln] using (Matrix.eigenvalue_is_perron_root_of_positive_eigenvector
          hBI hBn0 hvstrict.1 hvstrict.2 hveig).symm
      simpa [hroot]
        using hleRoot
    exact ge_of_tendsto hllim (Filter.Eventually.of_forall fun n ↦ hbound_n (φ n))
  · let rowsum : Fin k → ℝ := fun i ↦ ∑ j, A i j
    obtain ⟨imin, -, hmin⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin k)) rowsum Finset.univ_nonempty
    obtain ⟨imax, -, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset (Fin k)) rowsum Finset.univ_nonempty
    have hmin_n : ∀ n, rowsum imin + k * pfEps n ≤ ln n := by
      intro n
      rcases (D n).row_bounds with ⟨i, j, hlo, hhi⟩
      calc
        rowsum imin + k * pfEps n ≤ rowsum i + k * pfEps n := by
          gcongr
          exact hmin i (Finset.mem_univ i)
        _ = ∑ q, pfPerturb A n i q := by
          simp [rowsum, pfPerturb, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul]
        _ ≤ ln n := hlo
    have hmax_n : ∀ n, ln n ≤ rowsum imax + k * pfEps n := by
      intro n
      rcases (D n).row_bounds with ⟨i, j, hlo, hhi⟩
      calc
        ln n ≤ ∑ q, pfPerturb A n j q := hhi
        _ = rowsum j + k * pfEps n := by
          simp [rowsum, pfPerturb, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul]
        _ ≤ rowsum imax + k * pfEps n := by
          gcongr
          exact hmax j (Finset.mem_univ j)
    have hminlim :
        Tendsto (fun n ↦ rowsum imin + k * pfEps (φ n)) atTop (nhds (rowsum imin)) := by
      simpa using tendsto_const_nhds.add ((hepslim.const_mul (k : ℝ)))
    have hmaxlim :
        Tendsto (fun n ↦ rowsum imax + k * pfEps (φ n)) atTop (nhds (rowsum imax)) := by
      simpa using tendsto_const_nhds.add ((hepslim.const_mul (k : ℝ)))
    have hlo : rowsum imin ≤ lam := by
      have hdiff := hllim.sub hminlim
      have : 0 ≤ lam - rowsum imin := ge_of_tendsto hdiff
        (Filter.Eventually.of_forall fun n ↦ sub_nonneg.mpr (hmin_n (φ n)))
      linarith
    have hhi : lam ≤ rowsum imax := by
      have hdiff := hmaxlim.sub hllim
      have : 0 ≤ rowsum imax - lam := ge_of_tendsto hdiff
        (Filter.Eventually.of_forall fun n ↦ sub_nonneg.mpr (hmax_n (φ n)))
      linarith
    exact ⟨imin, imax, hlo, hhi⟩

end Chapter00
