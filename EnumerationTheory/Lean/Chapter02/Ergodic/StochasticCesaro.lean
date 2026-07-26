import Chapter02.Common
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.LinearAlgebra.Projection

noncomputable section

open Filter Finset Function

namespace Chapter02
namespace StochasticCesaro

variable {k : ℕ}

abbrev StateVector (k : ℕ) := Fin k → ℝ

def transitionLinearMap (P : Matrix (Fin k) (Fin k) ℝ) :
    StateVector k →ₗ[ℝ] StateVector k where
  toFun f i := ∑ j, P i j * f j
  map_add' f g := by
    funext i
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

lemma transitionLinearMap_apply (P : Matrix (Fin k) (Fin k) ℝ)
    (f : StateVector k) (i : Fin k) :
    transitionLinearMap P f i = ∑ j, P i j * f j := rfl

lemma transitionLinearMap_norm_le (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (f : StateVector k) : ‖transitionLinearMap P f‖ ≤ ‖f‖ := by
  by_cases hk : k = 0
  · subst k
    exact le_rfl
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg f)]
    intro i
    calc
      ‖transitionLinearMap P f i‖ = ‖∑ j, P i j * f j‖ := rfl
      _ ≤ ∑ j, ‖P i j * f j‖ := norm_sum_le _ _
      _ = ∑ j, P i j * ‖f j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hP0 i j)]
      _ ≤ ∑ j, P i j * ‖f‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f j) (hP0 i j)
      _ = ‖f‖ := by rw [← Finset.sum_mul, hPsum, one_mul]

lemma transitionLinearMap_lipschitz (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    LipschitzWith 1 (transitionLinearMap P) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro f g
  have h := transitionLinearMap_norm_le P hP0 hPsum (f - g)
  convert h using 1 <;> norm_num

lemma transitionLinearMap_iterate_norm_le (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (n : ℕ) (f : StateVector k) :
    ‖((transitionLinearMap P : StateVector k → StateVector k)^[n]) f‖ ≤ ‖f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (transitionLinearMap_norm_le P hP0 hPsum _).trans ih

lemma fixed_mem_range_sub_id_eq_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (U : V →ₗ[ℝ] V)
    (hpow : ∀ n : ℕ, ∀ y : V, ‖((U : V → V)^[n]) y‖ ≤ ‖y‖)
    {x : V} (hfix : U x = x) (hrange : x ∈ LinearMap.range (U - 1)) : x = 0 := by
  obtain ⟨y, hy⟩ := hrange
  have hstep : U y - y = x := by
    simpa using hy
  have hiter : ∀ n : ℕ, ((U : V → V)^[n]) y = y + (n : ℝ) • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, map_add, map_smul, hfix]
        rw [Nat.cast_succ, add_smul]
        have hUy : U y = y + x := by
          calc
            U y = (U y - y) + y := (sub_add_cancel (U y) y).symm
            _ = x + y := by rw [hstep]
            _ = y + x := add_comm _ _
        rw [hUy]
        module
  by_contra hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * ‖y‖) / ‖x‖)
  have hnlarge : 2 * ‖y‖ < (n : ℝ) * ‖x‖ := by
    exact (div_lt_iff₀ hxpos).mp hn
  have hbound : (n : ℝ) * ‖x‖ ≤ 2 * ‖y‖ := by
    calc
      (n : ℝ) * ‖x‖ = ‖(n : ℝ) • x‖ := by
        rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
      _ = ‖((U : V → V)^[n]) y - y‖ := by
        rw [hiter]
        congr 2
        abel
      _ ≤ ‖((U : V → V)^[n]) y‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ ‖y‖ + ‖y‖ := add_le_add (hpow n y) le_rfl
      _ = 2 * ‖y‖ := by ring
  linarith

lemma fixedSpace_disjoint_range_sub_id (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    Disjoint (LinearMap.eqLocus (transitionLinearMap P) 1)
      (LinearMap.range (transitionLinearMap P - 1)) := by
  rw [Submodule.disjoint_def]
  intro x hxfix hxrange
  exact fixed_mem_range_sub_id_eq_zero (transitionLinearMap P)
    (transitionLinearMap_iterate_norm_le P hP0 hPsum) hxfix hxrange

lemma fixedSpace_isCompl_range_sub_id (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    IsCompl (LinearMap.eqLocus (transitionLinearMap P) 1)
      (LinearMap.range (transitionLinearMap P - 1)) := by
  let U := transitionLinearMap P
  let p := LinearMap.eqLocus U 1
  let q := LinearMap.range (U - 1)
  have hpker : p = LinearMap.ker (U - 1) := by
    ext x
    change U x = x ↔ U x - x = 0
    constructor
    · intro hx
      rw [hx, sub_self]
    · exact sub_eq_zero.mp
  have hdisj : Disjoint p q := fixedSpace_disjoint_range_sub_id P hP0 hPsum
  have hdim : Module.finrank ℝ (StateVector k) ≤
      Module.finrank ℝ p + Module.finrank ℝ q := by
    rw [hpker, show q = LinearMap.range (U - 1) by rfl, add_comm]
    exact (LinearMap.finrank_range_add_finrank_ker (U - 1)).ge
  have htop : p ⊔ q = ⊤ := Submodule.eq_top_of_disjoint p q hdim hdisj
  exact ⟨hdisj, codisjoint_iff.mpr htop⟩

def meanProjection (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    StateVector k →L[ℝ] LinearMap.eqLocus (transitionLinearMap P) 1 :=
  ((LinearMap.eqLocus (transitionLinearMap P) 1).linearProjOfIsCompl
    (LinearMap.range (transitionLinearMap P - 1))
    (fixedSpace_isCompl_range_sub_id P hP0 hPsum)).toContinuousLinearMap

lemma tendsto_transition_birkhoffAverage (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (f : StateVector k) :
    Tendsto (birkhoffAverage ℝ (transitionLinearMap P) id · f) atTop
      (nhds ((meanProjection P hP0 hPsum f :
        LinearMap.eqLocus (transitionLinearMap P) 1) : StateVector k)) := by
  let U := transitionLinearMap P
  let p := LinearMap.eqLocus U 1
  let q := LinearMap.range (U - 1)
  let hc : IsCompl p q := fixedSpace_isCompl_range_sub_id P hP0 hPsum
  let g : StateVector k →L[ℝ] p := meanProjection P hP0 hPsum
  apply U.tendsto_birkhoffAverage_of_ker_subset_closure
    (transitionLinearMap_lipschitz P hP0 hPsum) g
  · intro x
    exact p.linearProjOfIsCompl_apply_left hc x
  · intro x hx
    apply subset_closure
    exact (p.linearProjOfIsCompl_apply_eq_zero_iff hc).mp hx

def basisVector (j : Fin k) : StateVector k := fun l => if l = j then 1 else 0

lemma transition_iterate_basisVector (P : Matrix (Fin k) (Fin k) ℝ)
    (n : ℕ) (i j : Fin k) :
    ((transitionLinearMap P : StateVector k → StateVector k)^[n])
        (basisVector j) i = (P ^ n) i j := by
  induction n generalizing i with
  | zero => simp [basisVector, Matrix.one_apply]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (∑ l, P i l *
        (((transitionLinearMap P : StateVector k → StateVector k)^[n])
          (basisVector j)) l) = _
      simp_rw [ih]
      rw [pow_succ']
      rfl

def cesaroLimitMatrix (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    Matrix (Fin k) (Fin k) ℝ := fun i j =>
  (meanProjection P hP0 hPsum (basisVector j) : StateVector k) i

lemma tendsto_cesaro_matrix_entry (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (i j : Fin k) :
    Tendsto (fun N : ℕ => if N = 0 then 0 else
      ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N, (P ^ n) i j) atTop
      (nhds (cesaroLimitMatrix P hP0 hPsum i j)) := by
  have hv := tendsto_transition_birkhoffAverage P hP0 hPsum (basisVector j)
  have hi := (tendsto_pi_nhds.mp hv) i
  convert hi using 1
  funext N
  by_cases hN : N = 0
  · simp [hN, birkhoffAverage, birkhoffSum]
  · rw [if_neg hN]
    simp only [birkhoffAverage, birkhoffSum, id_eq, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact (transition_iterate_basisVector P n i j).symm

lemma vector_eq_sum_basisVector (f : StateVector k) :
    f = ∑ j, f j • basisVector j := by
  funext i
  simp [basisVector]

lemma linearMap_apply_eq_sum_basisVector {W : Type*} [AddCommGroup W]
    [Module ℝ W] (L : StateVector k →ₗ[ℝ] W) (f : StateVector k) :
    L f = ∑ j, f j • L (basisVector j) := by
  conv_lhs => rw [vector_eq_sum_basisVector f]
  simp

lemma meanProjection_comp_transition (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1)
    (f : StateVector k) :
    meanProjection P hP0 hPsum (transitionLinearMap P f) =
      meanProjection P hP0 hPsum f := by
  let U := transitionLinearMap P
  let p := LinearMap.eqLocus U 1
  let q := LinearMap.range (U - 1)
  let hc : IsCompl p q := fixedSpace_isCompl_range_sub_id P hP0 hPsum
  have hq : U f - f ∈ q := by
    exact ⟨f, by simp⟩
  have hz : meanProjection P hP0 hPsum (U f - f) = 0 := by
    exact p.linearProjOfIsCompl_apply_eq_zero_iff hc |>.2 hq
  simpa only [map_sub, sub_eq_zero] using hz

lemma cesaroLimitMatrix_mul_left (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    P * cesaroLimitMatrix P hP0 hPsum = cesaroLimitMatrix P hP0 hPsum := by
  ext i j
  exact congrFun (meanProjection P hP0 hPsum (basisVector j)).property i

lemma cesaroLimitMatrix_mul_right (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    cesaroLimitMatrix P hP0 hPsum * P = cesaroLimitMatrix P hP0 hPsum := by
  ext i j
  have hrep := linearMap_apply_eq_sum_basisVector
    (meanProjection P hP0 hPsum).toLinearMap
    (transitionLinearMap P (basisVector j))
  have hcoord := congrFun (congrArg Subtype.val hrep) i
  have hcomm := congrArg (fun z : LinearMap.eqLocus (transitionLinearMap P) 1 =>
      (z : StateVector k) i)
    (meanProjection_comp_transition P hP0 hPsum (basisVector j))
  simpa [Matrix.mul_apply, cesaroLimitMatrix, transitionLinearMap_apply,
    basisVector, mul_comm] using hcoord.symm.trans hcomm

lemma cesaroLimitMatrix_idempotent (P : Matrix (Fin k) (Fin k) ℝ)
    (hP0 : ∀ i j, 0 ≤ P i j) (hPsum : ∀ i, ∑ j, P i j = 1) :
    cesaroLimitMatrix P hP0 hPsum * cesaroLimitMatrix P hP0 hPsum =
      cesaroLimitMatrix P hP0 hPsum := by
  ext i j
  let v : StateVector k :=
    (meanProjection P hP0 hPsum (basisVector j) : StateVector k)
  have hrep := linearMap_apply_eq_sum_basisVector
    (meanProjection P hP0 hPsum).toLinearMap v
  have hfixed : transitionLinearMap P v = v :=
    (meanProjection P hP0 hPsum (basisVector j)).property
  have hproj : meanProjection P hP0 hPsum v =
      meanProjection P hP0 hPsum (basisVector j) := by
    have hvp : v ∈ LinearMap.eqLocus (transitionLinearMap P) 1 := hfixed
    exact (LinearMap.eqLocus (transitionLinearMap P) 1).linearProjOfIsCompl_apply_left
      (fixedSpace_isCompl_range_sub_id P hP0 hPsum) ⟨v, hvp⟩
  have hcoord := congrFun (congrArg Subtype.val hrep) i
  have hprojcoord := congrArg
    (fun z : LinearMap.eqLocus (transitionLinearMap P) 1 => (z : StateVector k) i) hproj
  simpa [Matrix.mul_apply, cesaroLimitMatrix, v, mul_comm] using
    hcoord.symm.trans hprojcoord

theorem stochasticMatrixCesaroLimit : StochasticMatrixLimitStatement := by
  intro k P hP0 hPsum
  let Q := cesaroLimitMatrix P hP0 hPsum
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · exact tendsto_cesaro_matrix_entry P hP0 hPsum
  · exact cesaroLimitMatrix_mul_left P hP0 hPsum
  · exact cesaroLimitMatrix_mul_right P hP0 hPsum
  · exact cesaroLimitMatrix_idempotent P hP0 hPsum

end StochasticCesaro
end Chapter02
