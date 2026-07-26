import Chapter02.Ergodic.StochasticCesaro
import Mathlib.LinearAlgebra.Eigenspace.Zero

noncomputable section

open Classical Filter Finset

namespace Chapter02
namespace FiniteMarkov

variable {k : ℕ}

lemma simpleFactor_iff_rootMultiplicity_eq_one (p : Polynomial ℝ) (hp : p ≠ 0)
    (a : ℝ) :
    (∃ q : Polynomial ℝ,
      p = (Polynomial.X - Polynomial.C a) * q ∧ q.eval a ≠ 0) ↔
      p.rootMultiplicity a = 1 := by
  constructor
  · rintro ⟨q, hpq, hq⟩
    have hprod : (Polynomial.X - Polynomial.C a) * q ≠ 0 := by
      rw [← hpq]
      exact hp
    rw [hpq, Polynomial.rootMultiplicity_mul hprod,
      Polynomial.rootMultiplicity_X_sub_C, if_pos rfl]
    have hnotroot : ¬q.IsRoot a := by simpa [Polynomial.IsRoot] using hq
    rw [Polynomial.rootMultiplicity_eq_zero hnotroot, add_zero]
  · intro hm
    obtain ⟨q, hpq, hndvd⟩ :=
      Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
    rw [hm, pow_one] at hpq
    refine ⟨q, hpq, ?_⟩
    intro heval
    exact hndvd (Polynomial.dvd_iff_isRoot.mpr heval)

lemma generalized_fixed_of_power_eq_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (U : V →ₗ[ℝ] V)
    (hpow : ∀ n : ℕ, ∀ y : V, ‖((U : V → V)^[n]) y‖ ≤ ‖y‖) :
    ∀ n : ℕ, ∀ x : V, ((U - 1) ^ n) x = 0 → U x = x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa using hx
      subst x
      simp
  | succ n ih =>
      intro x hx
      let y := (U - 1) x
      have hcomm : ((U - 1) ^ n) ((U - 1) x) =
          (U - 1) (((U - 1) ^ n) x) := by
        have hm : (U - 1) ^ n * (U - 1) = (U - 1) * (U - 1) ^ n := by
          rw [← pow_succ, ← pow_succ']
        exact DFunLike.congr_fun hm x
      have hyzero : ((U - 1) ^ n) y = 0 := by
        rw [show y = (U - 1) x by rfl, hcomm]
        simpa [pow_succ'] using hx
      have hyfix : U y = y := ih y hyzero
      have hyrange : y ∈ LinearMap.range (U - 1) := ⟨x, rfl⟩
      have hy0 := StochasticCesaro.fixed_mem_range_sub_id_eq_zero U hpow hyfix hyrange
      change U x - x = 0 at hy0
      exact sub_eq_zero.mp hy0

lemma maxGenEigenspace_one_eq_fixedSpace (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    Module.End.maxGenEigenspace (Matrix.toLin' P) 1 =
      LinearMap.eqLocus (StochasticCesaro.transitionLinearMap P) 1 := by
  have hU : Matrix.toLin' P = StochasticCesaro.transitionLinearMap P := by
    ext f i
    rfl
  ext x
  rw [Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨n, hn⟩
    change StochasticCesaro.transitionLinearMap P x = x
    apply generalized_fixed_of_power_eq_zero (StochasticCesaro.transitionLinearMap P)
      (StochasticCesaro.transitionLinearMap_iterate_norm_le P hP0 hPsum) n x
    simpa [hU] using hn
  · intro hx
    refine ⟨1, ?_⟩
    simpa [hU] using (sub_eq_zero.mpr hx)

lemma rootMultiplicity_one_eq_finrank_fixedSpace
    (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    (Matrix.charpoly P).rootMultiplicity 1 =
      Module.finrank ℝ (LinearMap.eqLocus
        (StochasticCesaro.transitionLinearMap P) 1) := by
  rw [← Matrix.charpoly_toLin', ← LinearMap.finrank_maxGenEigenspace_eq]
  exact congrArg
    (fun s : Submodule ℝ (Fin k → ℝ) => Module.finrank ℝ s)
    (maxGenEigenspace_one_eq_fixedSpace P hP0 hPsum)

lemma pow_nonnegative (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) : ∀ n i j, 0 ≤ (P ^ n) i j := by
  intro n
  induction n with
  | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split <;> positivity
  | succ n ih =>
      intro i j
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg fun l hl => mul_nonneg (hP0 i l) (ih l j)

lemma pow_rowsum_one (P : Matrix (Fin k) (Fin k) ℝ)
    (hPsum : ∀ i, ∑ j, P i j = 1) : ∀ n i, ∑ j, (P ^ n) i j = 1 := by
  intro n
  induction n with
  | zero => intro i; simp [Matrix.one_apply]
  | succ n ih =>
      intro i
      rw [pow_succ']
      simp_rw [Matrix.mul_apply]
      calc
        ∑ x, ∑ x_1, P i x_1 * (P ^ n) x_1 x =
            ∑ x_1, ∑ x, P i x_1 * (P ^ n) x_1 x := Finset.sum_comm
        _ =
            ∑ x_1, P i x_1 * ∑ x, (P ^ n) x_1 x := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [Finset.mul_sum]
        _ = ∑ x_1, P i x_1 := by simp_rw [ih, mul_one]
        _ = 1 := hPsum i

lemma pow_mul_fixed_column (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hPQ : P * Q = Q) : ∀ n, P ^ n * Q = Q := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Matrix.mul_assoc, ih, hPQ]

lemma irreducible_implies_rows_equal {P Q : Matrix (Fin k) (Fin k) ℝ}
    (hirr : IsIrreducibleStochasticMatrix P) (hPQ : P * Q = Q) :
    StochasticMatrixRowsEqual Q := by
  rcases hirr with ⟨hP0, hPsum, hirr⟩
  intro i i' j
  obtain ⟨imax, _, himax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin k)) (fun r => Q r j) ⟨i, Finset.mem_univ i⟩
  have hmax : ∀ r, Q r j ≤ Q imax j := by
    intro r
    exact himax r (Finset.mem_univ r)
  have hfixpow := pow_mul_fixed_column P Q hPQ
  have hall : ∀ r, Q r j = Q imax j := by
    intro r
    obtain ⟨n, hn⟩ := hirr imax r
    have hsum : ∑ l, (P ^ n) imax l * (Q imax j - Q l j) = 0 := by
      calc
        _ = Q imax j * ∑ l, (P ^ n) imax l -
            ∑ l, (P ^ n) imax l * Q l j := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
              apply congrArg₂ (· - ·)
              · apply Finset.sum_congr rfl
                intro l hl
                ring
              · rfl
        _ = Q imax j - (P ^ n * Q) imax j := by
              rw [pow_rowsum_one P hPsum]
              simp [Matrix.mul_apply]
        _ = 0 := by rw [hfixpow]; simp
    have hnonneg : ∀ l ∈ (Finset.univ : Finset (Fin k)),
        0 ≤ (P ^ n) imax l * (Q imax j - Q l j) := by
      intro l hl
      exact mul_nonneg (pow_nonnegative P hP0 n imax l) (sub_nonneg.mpr (hmax l))
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum r (Finset.mem_univ r)
    have hcoef : 0 < (P ^ n) imax r := hn
    have : Q imax j - Q r j = 0 := (mul_eq_zero.mp hzero).resolve_left hcoef.ne'
    linarith
  exact (hall i).trans (hall i').symm

lemma oneVector_mem_fixedSpace (P : Matrix (Fin k) (Fin k) ℝ)
    (hPsum : ∀ i, ∑ j, P i j = 1) :
    (fun _ : Fin k => (1 : ℝ)) ∈
      LinearMap.eqLocus (StochasticCesaro.transitionLinearMap P) 1 := by
  change StochasticCesaro.transitionLinearMap P (fun _ : Fin k => (1 : ℝ)) =
    (fun _ : Fin k => (1 : ℝ))
  funext i
  simpa [StochasticCesaro.transitionLinearMap_apply] using hPsum i

lemma irreducible_fixedSpace_eq_span_one (P : Matrix (Fin k) (Fin k) ℝ)
    (hirr : IsIrreducibleStochasticMatrix P) (i0 : Fin k) :
    LinearMap.eqLocus (StochasticCesaro.transitionLinearMap P) 1 =
      ℝ ∙ (fun _ : Fin k => (1 : ℝ)) := by
  rcases hirr with ⟨hP0, hPsum, hirr⟩
  apply le_antisymm
  · intro f hf
    let R : Matrix (Fin k) (Fin k) ℝ := fun i _j => f i
    have hPR : P * R = R := by
      ext i j
      change (StochasticCesaro.transitionLinearMap P f) i = f i
      exact congrFun hf i
    have hrows : StochasticMatrixRowsEqual R :=
      irreducible_implies_rows_equal ⟨hP0, hPsum, hirr⟩ hPR
    apply Submodule.mem_span_singleton.mpr
    refine ⟨f i0, ?_⟩
    funext i
    simpa [R] using (hrows i0 i i0)
  · intro f hf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    change StochasticCesaro.transitionLinearMap P
      (c • fun _ : Fin k => (1 : ℝ)) = c • fun _ : Fin k => (1 : ℝ)
    rw [map_smul]
    exact congrArg (c • ·) (oneVector_mem_fixedSpace P hPsum)

lemma irreducible_finrank_fixedSpace_eq_one (P : Matrix (Fin k) (Fin k) ℝ)
    (hirr : IsIrreducibleStochasticMatrix P) (i0 : Fin k) :
    Module.finrank ℝ (LinearMap.eqLocus
      (StochasticCesaro.transitionLinearMap P) 1) = 1 := by
  rw [irreducible_fixedSpace_eq_span_one P hirr i0]
  apply finrank_span_singleton
  intro hzero
  have := congrFun hzero i0
  norm_num at this

lemma rowsEqual_of_finrank_fixedSpace_eq_one
    (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hPsum : ∀ i, ∑ j, P i j = 1) (i0 : Fin k)
    (hfin : Module.finrank ℝ (LinearMap.eqLocus
      (StochasticCesaro.transitionLinearMap P) 1) = 1)
    (hPQ : P * Q = Q) : StochasticMatrixRowsEqual Q := by
  let pfix := LinearMap.eqLocus (StochasticCesaro.transitionLinearMap P) 1
  let s := ℝ ∙ (fun _ : Fin k => (1 : ℝ))
  have hone0 : (fun _ : Fin k => (1 : ℝ)) ≠ 0 := by
    intro hz
    have := congrFun hz i0
    norm_num at this
  have hsfin : Module.finrank ℝ s = 1 := finrank_span_singleton hone0
  have hsle : s ≤ pfix := by
    apply Submodule.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact oneVector_mem_fixedSpace P hPsum
  have hsp : s = pfix := Submodule.eq_of_le_of_finrank_eq hsle (hsfin.trans hfin.symm)
  intro i i' j
  let f : Fin k → ℝ := fun r => Q r j
  have hf : f ∈ pfix := by
    change StochasticCesaro.transitionLinearMap P f = f
    funext r
    exact congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A r j) hPQ
  have hfs : f ∈ s := hsp.symm ▸ hf
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfs
  have hci := congrFun hc i
  have hci' := congrFun hc i'
  simpa [f] using hci.symm.trans hci'

lemma stationary_pow (p : Fin k → ℝ) (P : Matrix (Fin k) (Fin k) ℝ)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j) :
    ∀ n j, ∑ i, p i * (P ^ n) i j = p j := by
  intro n
  induction n with
  | zero => intro j; simp [Matrix.one_apply]
  | succ n ih =>
      intro j
      rw [pow_succ]
      simp_rw [Matrix.mul_apply, Finset.mul_sum]
      calc
        ∑ i, ∑ x, p i * ((P ^ n) i x * P x j) =
            ∑ x, ∑ i, p i * ((P ^ n) i x * P x j) := Finset.sum_comm
        _ = ∑ x, (∑ i, p i * (P ^ n) i x) * P x j := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = ∑ x, p x * P x j := by simp_rw [ih]
        _ = p j := hstationary j

lemma stationary_cesaro_limit (p : Fin k → ℝ) (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, (P ^ n) i j)
      atTop (nhds (Q i j))) :
    ∀ j, ∑ i, p i * Q i j = p j := by
  intro j
  let A : ℕ → Fin k → ℝ := fun N i =>
    if N = 0 then 0 else ((N : ℝ)⁻¹) *
      ∑ n ∈ Finset.range N, (P ^ n) i j
  have hsumlim : Tendsto (fun N => ∑ i, p i * A N i) atTop
      (nhds (∑ i, p i * Q i j)) := by
    exact tendsto_finset_sum _ fun i _ => tendsto_const_nhds.mul (hlim i j)
  have hevent : ∀ᶠ N : ℕ in atTop, (∑ i, p i * A N i) = p j := by
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hrewrite : (∑ i, p i * A N i) =
        (N : ℝ)⁻¹ * ∑ n ∈ range N, ∑ i, p i * (P ^ n) i j := by
      simp only [A, if_neg hN]
      calc
        ∑ i, p i * ((N : ℝ)⁻¹ * ∑ n ∈ range N, (P ^ n) i j) =
            ∑ i, ∑ n ∈ range N, (N : ℝ)⁻¹ * (p i * (P ^ n) i j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              ring
        _ = ∑ n ∈ range N, ∑ i, (N : ℝ)⁻¹ * (p i * (P ^ n) i j) :=
          Finset.sum_comm
        _ = (N : ℝ)⁻¹ * ∑ n ∈ range N, ∑ i, p i * (P ^ n) i j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              rw [Finset.mul_sum]
    rw [hrewrite]
    simp_rw [stationary_pow p P hstationary]
    simp [hN]
  have heq : (fun _N : ℕ => p j) =ᶠ[atTop] (fun N => ∑ i, p i * A N i) := by
    filter_upwards [hevent] with N hN
    exact hN.symm
  exact tendsto_nhds_unique hsumlim (Filter.Tendsto.congr' heq tendsto_const_nhds)

lemma rows_equal_implies_strictlyPositive (p : Fin k → ℝ)
    (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hlim : ∀ i j, Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, (P ^ n) i j)
      atTop (nhds (Q i j)))
    (hrows : StochasticMatrixRowsEqual Q) :
    StochasticMatrixStrictlyPositive Q := by
  intro i j
  have hstat := stationary_cesaro_limit p P Q hstationary hlim j
  have hsum : ∑ l, p l * Q l j = Q i j := by
    calc
      _ = ∑ l, p l * Q i j := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hrows l i j]
      _ = (∑ l, p l) * Q i j := (Finset.sum_mul ..).symm
      _ = Q i j := by rw [hpsum, one_mul]
  rw [hsum] at hstat
  rw [hstat]
  exact hp j

lemma strictlyPositive_implies_irreducible (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hlim : ∀ i j, Tendsto
      (fun N : ℕ => if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, (P ^ n) i j)
      atTop (nhds (Q i j)))
    (hQpos : StochasticMatrixStrictlyPositive Q) :
    IsIrreducibleStochasticMatrix P := by
  refine ⟨hP0, hPsum, ?_⟩
  intro i j
  have hev := (hlim i j).eventually (Ioi_mem_nhds (hQpos i j))
  obtain ⟨N, hN⟩ := hev.exists
  have hN0 : N ≠ 0 := by
    intro hz
    subst N
    simp at hN
  have hsumpos : 0 < ∑ n ∈ Finset.range N, (P ^ n) i j := by
    have hcast : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    rw [if_neg hN0] at hN
    have hinv : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hcast
    nlinarith
  rw [Finset.sum_pos_iff_of_nonneg (fun n hn => pow_nonnegative P hP0 n i j)] at hsumpos
  obtain ⟨n, hnN, hnpos⟩ := hsumpos
  exact ⟨n, hnpos⟩

lemma rowsEqual_iff_strictlyPositive_iff_irreducible
    (p : Fin k → ℝ) (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hQ : IsStochasticCesaroLimit P Q) :
    (StochasticMatrixRowsEqual Q ↔ StochasticMatrixStrictlyPositive Q) ∧
    (StochasticMatrixStrictlyPositive Q ↔ IsIrreducibleStochasticMatrix P) := by
  rcases hQ with ⟨hlim, hPQ, hQP, hQQ⟩
  constructor
  · constructor
    · exact rows_equal_implies_strictlyPositive p P Q hp hpsum hstationary hlim
    · intro hpos
      exact irreducible_implies_rows_equal
        (strictlyPositive_implies_irreducible P Q hP0 hPsum hlim hpos) hPQ
  · constructor
    · exact strictlyPositive_implies_irreducible P Q hP0 hPsum hlim
    · intro hirr
      exact rows_equal_implies_strictlyPositive p P Q hp hpsum hstationary hlim
        (irreducible_implies_rows_equal hirr hPQ)

lemma irreducible_iff_hasSimpleEigenvalueOne
    (p : Fin k → ℝ) (P Q : Matrix (Fin k) (Fin k) ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (hstationary : ∀ j, ∑ i, p i * P i j = p j)
    (hQ : IsStochasticCesaroLimit P Q) :
    IsIrreducibleStochasticMatrix P ↔ HasSimpleEigenvalueOne P := by
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    simpa using hpsum
  let i0 : Fin k := ⟨0, hk⟩
  have hchar0 : Matrix.charpoly P ≠ 0 := (Matrix.charpoly_monic P).ne_zero
  constructor
  · intro hirr
    apply (simpleFactor_iff_rootMultiplicity_eq_one (Matrix.charpoly P) hchar0 1).mpr
    rw [rootMultiplicity_one_eq_finrank_fixedSpace P hP0 hPsum]
    exact irreducible_finrank_fixedSpace_eq_one P hirr i0
  · intro hsimple
    have hmult : (Matrix.charpoly P).rootMultiplicity 1 = 1 :=
      (simpleFactor_iff_rootMultiplicity_eq_one (Matrix.charpoly P) hchar0 1).mp hsimple
    have hfin : Module.finrank ℝ (LinearMap.eqLocus
        (StochasticCesaro.transitionLinearMap P) 1) = 1 := by
      rw [← rootMultiplicity_one_eq_finrank_fixedSpace P hP0 hPsum]
      exact hmult
    have hrows := rowsEqual_of_finrank_fixedSpace_eq_one P Q hPsum i0 hfin hQ.2.1
    have heq := rowsEqual_iff_strictlyPositive_iff_irreducible
      p P Q hp hpsum hP0 hPsum hstationary hQ
    exact heq.2.mp (heq.1.mp hrows)

end FiniteMarkov
end Chapter02
