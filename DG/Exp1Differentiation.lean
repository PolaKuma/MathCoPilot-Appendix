import Exp1Projection

open scoped ENNReal MeasureTheory Topology Interval BigOperators
open MeasureTheory Set Filter

noncomputable section
namespace Exp1

def referenceGram {K : ℕ} (i k : Fin (K + 1)) : ℝ :=
  ∫ x, x ^ (i : ℕ) * x ^ (k : ℕ)
    ∂(volume.restrict Exp2.referenceCell)

lemma coefficient_monomial_product_integrable {K : ℕ}
    (c d : Fin (K + 1) → ℝ) (i k : Fin (K + 1)) :
    Integrable (fun x : ℝ ↦
      (c i * x ^ (i : ℕ)) * (d k * x ^ (k : ℕ)))
      (volume.restrict Exp2.referenceCell) := by
  have h := Exp2.polynomial_eval_integrable_reference
    (Polynomial.C (c i * d k) * Polynomial.X ^ ((i : ℕ) + (k : ℕ)))
  convert h using 1
  funext x
  simp [pow_add]
  ring

lemma integral_coefficient_monomial_product {K : ℕ}
    (c d : Fin (K + 1) → ℝ) :
    (∫ x, (∑ i, c i * x ^ (i : ℕ)) * (∑ k, d k * x ^ (k : ℕ))
      ∂(volume.restrict Exp2.referenceCell)) =
      ∑ i, ∑ k, c i * d k * referenceGram i k := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (K + 1))),
      ∀ k ∈ (Finset.univ : Finset (Fin (K + 1))),
      Integrable (fun x : ℝ ↦
        (c i * x ^ (i : ℕ)) * (d k * x ^ (k : ℕ)))
        (volume.restrict Exp2.referenceCell) := by
    intro i hi k hk
    exact coefficient_monomial_product_integrable c d i k
  calc
    _ = ∫ x, ∑ i, ∑ k,
        (c i * x ^ (i : ℕ)) * (d k * x ^ (k : ℕ))
        ∂(volume.restrict Exp2.referenceCell) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i, ∫ x, ∑ k,
        (c i * x ^ (i : ℕ)) * (d k * x ^ (k : ℕ))
        ∂(volume.restrict Exp2.referenceCell) := by
      rw [integral_finset_sum]
      intro i hi
      exact integrable_finset_sum Finset.univ
        (fun k hk ↦ hterm i (by simp) k hk)
    _ = ∑ i, ∑ k, ∫ x,
        (c i * x ^ (i : ℕ)) * (d k * x ^ (k : ℕ))
        ∂(volume.restrict Exp2.referenceCell) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum]
      exact fun k hk ↦ hterm i hi k hk
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      have heq : (fun x : ℝ ↦
          (c i * x ^ (i : ℕ)) * (d k * x ^ (k : ℕ))) =
          fun x ↦ (c i * d k) * (x ^ (i : ℕ) * x ^ (k : ℕ)) := by
        funext x
        ring
      rw [heq, integral_const_mul]
      rfl

lemma referenceGram_comm {K : ℕ} (i k : Fin (K + 1)) :
    referenceGram i k = referenceGram k i := by
  unfold referenceGram
  apply integral_congr_ae
  filter_upwards with x
  ring

lemma coefficientQuadratic_hasDerivWithinAt {K : ℕ}
    (c : ℝ → Fin (K + 1) → ℝ) (d : Fin (K + 1) → ℝ)
    (h : ℝ) {t T : ℝ}
    (hc : ∀ i : Fin (K + 1), HasDerivWithinAt (fun s ↦ c s i) (d i)
      (Set.Icc (0 : ℝ) T) t) :
    HasDerivWithinAt
      (fun s ↦ h * ∑ i, ∑ k, c s i * c s k * referenceGram i k)
      (2 * h * ∑ i, ∑ k, d i * c t k * referenceGram i k)
      (Set.Icc (0 : ℝ) T) t := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (K + 1))),
      ∀ k ∈ (Finset.univ : Finset (Fin (K + 1))),
      HasDerivWithinAt
        (fun s ↦ h * (c s i * c s k * referenceGram i k))
        (h * ((d i * c t k + c t i * d k) * referenceGram i k))
        (Set.Icc (0 : ℝ) T) t := by
    intro i hi k hk
    have hraw := ((hc i).mul (hc k)).mul_const (h * referenceGram i k)
    convert hraw using 1
    · funext s
      simp only [Pi.mul_apply]
      ring
    · ring
  have hinner (i : Fin (K + 1)) : HasDerivWithinAt
      (fun s ↦ ∑ k, h * (c s i * c s k * referenceGram i k))
      (∑ k, h * ((d i * c t k + c t i * d k) * referenceGram i k))
      (Set.Icc (0 : ℝ) T) t := by
    have hraw := HasDerivWithinAt.sum (u := Finset.univ)
      (fun k hk ↦ hterm i (by simp) k hk)
    have hfun :
        (fun s ↦ ∑ k, h * (c s i * c s k * referenceGram i k)) =
      ∑ k, (fun s ↦ h * (c s i * c s k * referenceGram i k)) := by
      funext s
      simp
    rw [hfun]
    exact hraw
  have hraw := HasDerivWithinAt.sum (u := Finset.univ)
    (fun i hi ↦ hinner i)
  have hfun :
      (fun s ↦ h * ∑ i, ∑ k, c s i * c s k * referenceGram i k) =
      ∑ i, (fun s ↦ ∑ k, h * (c s i * c s k * referenceGram i k)) := by
    funext s
    simp_rw [Finset.mul_sum]
    simp
  rw [hfun]
  convert hraw using 1
  have hswap :
      (∑ i, ∑ k, c t i * d k * referenceGram i k) =
      ∑ i, ∑ k, d i * c t k * referenceGram i k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [referenceGram_comm]
    ring
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap]
  ring

def regularityEnergy {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ}
    {v vt : DGTrajectory N} (r : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) : ℝ :=
  ∑ j : Fin N, cellLength mesh j *
    ∑ i, ∑ k, r.coefficient t j i * r.coefficient t j k * referenceGram i k

def regularityPair {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ}
    {v vt : DGTrajectory N} (r : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) : ℝ :=
  ∑ j : Fin N, cellLength mesh j *
    ∑ i, ∑ k, r.timeDerivativeCoefficient t j i *
      r.coefficient t j k * referenceGram i k

lemma regularityEnergy_hasDerivWithinAt {K N : ℕ}
    {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (r : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (regularityEnergy r) (2 * regularityPair r t)
      (Set.Icc (0 : ℝ) T) t := by
  have hcell : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      HasDerivWithinAt
        (fun s ↦ cellLength mesh j * ∑ i, ∑ k,
          r.coefficient s j i * r.coefficient s j k * referenceGram i k)
        (2 * cellLength mesh j * ∑ i, ∑ k,
          r.timeDerivativeCoefficient t j i * r.coefficient t j k *
            referenceGram i k)
        (Set.Icc (0 : ℝ) T) t := by
    intro j hj
    exact coefficientQuadratic_hasDerivWithinAt
      (fun s i ↦ r.coefficient s j i)
      (fun i ↦ r.timeDerivativeCoefficient t j i)
      (cellLength mesh j)
      (fun i ↦ r.coefficient_hasDerivWithinAt j i t ht)
  have hraw := HasDerivWithinAt.sum hcell
  have hfun : regularityEnergy r =
      ∑ j : Fin N, (fun s ↦ cellLength mesh j * ∑ i, ∑ k,
        r.coefficient s j i * r.coefficient s j k * referenceGram i k) := by
    funext s
    simp [regularityEnergy]
  rw [hfun]
  convert hraw using 1
  simp only [regularityPair, Finset.mul_sum]
  ring

lemma regularity_cell_l2_sq_eq {K N : ℕ}
    {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (r : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : Fin N)
    (hmem : MemLp (v t j) 2
      (volume.restrict (meshCell mesh j : Set ℝ))) :
    (Exp2.l2NormOn (meshCell mesh j) (v t j)) ^ 2 =
      cellLength mesh j * ∑ i, ∑ k,
        r.coefficient t j i * r.coefficient t j k * referenceGram i k := by
  let f : ℝ → ℝ := fun x ↦ (v t j x) ^ 2
  have hscale := Exp2AffineMeasure.setIntegral_comp_affine_Ioo
    (a := cellLeft mesh j) f (cellLength_pos mesh j)
  have href :
      (∫ xHat in Set.Ioo (0 : ℝ) 1,
        f (cellLeft mesh j + cellLength mesh j * xHat)) =
      ∑ i, ∑ k, r.coefficient t j i * r.coefficient t j k *
        referenceGram i k := by
    calc
      _ = ∫ xHat, (∑ i, r.coefficient t j i * xHat ^ (i : ℕ)) *
          (∑ k, r.coefficient t j k * xHat ^ (k : ℕ))
          ∂(volume.restrict Exp2.referenceCell) := by
        have heq :
            (∫ xHat, f (cellLeft mesh j + cellLength mesh j * xHat)
              ∂(volume.restrict Exp2.referenceCell)) =
            ∫ xHat, (∑ i, r.coefficient t j i * xHat ^ (i : ℕ)) *
              (∑ k, r.coefficient t j k * xHat ^ (k : ℕ))
              ∂(volume.restrict Exp2.referenceCell) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
          have hxphys : cellLeft mesh j + cellLength mesh j * xHat ∈
              Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
            constructor
            · nlinarith [cellLength_pos mesh j, hxHat.1]
            · have hright : cellRight mesh j =
                  cellLeft mesh j + cellLength mesh j := by simp [cellLength]
              rw [hright]
              nlinarith [cellLength_pos mesh j, hxHat.2]
          have hvalue := r.value_eq t ht j
            (cellLeft mesh j + cellLength mesh j * xHat) hxphys
          have hcoord :
              (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
                cellLength mesh j = xHat := by
            rw [add_sub_cancel_left]
            exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
          rw [hcoord] at hvalue
          simp only [f, hvalue, pow_two]
        simpa [Exp2.referenceCell, Exp2.cell] using heq
      _ = _ := integral_coefficient_monomial_product
        (r.coefficient t j) (r.coefficient t j)
  have hintegral_nonneg : 0 ≤ ∫ x, ‖v t j x‖ ^ 2
      ∂(volume.restrict (meshCell mesh j : Set ℝ)) :=
    integral_nonneg (fun x ↦ sq_nonneg _)
  rw [Exp2.l2NormOn_eq_sqrt_integral_sq hmem,
    Real.sq_sqrt hintegral_nonneg]
  have hnormeq : (∫ x, ‖v t j x‖ ^ 2
      ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      ∫ x, f x ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
    apply integral_congr_ae
    filter_upwards with x
    simp [f, Real.norm_eq_abs, sq_abs]
  rw [hnormeq]
  simp only [smul_eq_mul] at hscale
  rw [href] at hscale
  have hne := (cellLength_pos mesh j).ne'
  field_simp [hne] at hscale
  calc
    (∫ x, f x ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
        ∫ x in Set.Ioo (cellLeft mesh j)
          (cellLeft mesh j + cellLength mesh j), f x := by
            rfl
    _ = (∑ i, ∑ k, r.coefficient t j i * r.coefficient t j k *
          referenceGram i k) * cellLength mesh j := hscale.symm
    _ = _ := by ring

lemma regularity_cell_pair_eq {K N : ℕ}
    {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (r : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : Fin N) :
    (∫ x, vt t j x * v t j x
      ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      cellLength mesh j * ∑ i, ∑ k,
        r.timeDerivativeCoefficient t j i * r.coefficient t j k *
          referenceGram i k := by
  let f : ℝ → ℝ := fun x ↦ vt t j x * v t j x
  have hscale := Exp2AffineMeasure.setIntegral_comp_affine_Ioo
    (a := cellLeft mesh j) f (cellLength_pos mesh j)
  have href :
      (∫ xHat in Set.Ioo (0 : ℝ) 1,
        f (cellLeft mesh j + cellLength mesh j * xHat)) =
      ∑ i, ∑ k, r.timeDerivativeCoefficient t j i *
        r.coefficient t j k * referenceGram i k := by
    have heq :
        (∫ xHat, f (cellLeft mesh j + cellLength mesh j * xHat)
          ∂(volume.restrict Exp2.referenceCell)) =
        ∫ xHat,
          (∑ i, r.timeDerivativeCoefficient t j i * xHat ^ (i : ℕ)) *
          (∑ k, r.coefficient t j k * xHat ^ (k : ℕ))
          ∂(volume.restrict Exp2.referenceCell) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
      have hxphys : cellLeft mesh j + cellLength mesh j * xHat ∈
          Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
        constructor
        · nlinarith [cellLength_pos mesh j, hxHat.1]
        · have hright : cellRight mesh j =
              cellLeft mesh j + cellLength mesh j := by simp [cellLength]
          rw [hright]
          nlinarith [cellLength_pos mesh j, hxHat.2]
      have hv := r.value_eq t ht j
        (cellLeft mesh j + cellLength mesh j * xHat) hxphys
      have hvt := r.timeDerivativeValue_eq t ht j
        (cellLeft mesh j + cellLength mesh j * xHat) hxphys
      have hcoord :
          (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
            cellLength mesh j = xHat := by
        rw [add_sub_cancel_left]
        exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
      rw [hcoord] at hv hvt
      simp only [f, hv, hvt]
    have heq' := integral_coefficient_monomial_product
      (r.timeDerivativeCoefficient t j) (r.coefficient t j)
    simpa [Exp2.referenceCell, Exp2.cell] using heq.trans heq'
  simp only [smul_eq_mul] at hscale
  rw [href] at hscale
  have hne := (cellLength_pos mesh j).ne'
  field_simp [hne] at hscale
  calc
    (∫ x, vt t j x * v t j x
      ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
        ∫ x in Set.Ioo (cellLeft mesh j)
          (cellLeft mesh j + cellLength mesh j), f x := by rfl
    _ = (∑ i, ∑ k, r.timeDerivativeCoefficient t j i *
          r.coefficient t j k * referenceGram i k) * cellLength mesh j :=
      hscale.symm
    _ = _ := by ring

lemma DGTrajectoryRegularity.brokenL2Norm_sq_eq_regularityEnergy
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (r : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hmem : ∀ j : Fin N, MemLp (v t j) 2
      (volume.restrict (meshCell mesh j : Set ℝ))) :
    (brokenL2Norm mesh (v t)) ^ 2 = regularityEnergy r t := by
  unfold brokenL2Norm
  rw [Real.sq_sqrt]
  · unfold regularityEnergy
    apply Finset.sum_congr rfl
    intro j hj
    exact regularity_cell_l2_sq_eq r t ht j (hmem j)
  · exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _

lemma DGTrajectoryRegularity.regularityPair_eq_integral_sum
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (r : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    regularityPair r t = ∑ j : Fin N, ∫ x, vt t j x * v t j x
      ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
  unfold regularityPair
  apply Finset.sum_congr rfl
  intro j hj
  exact (regularity_cell_pair_eq r t ht j).symm

lemma DGTrajectoryRegularity.energy_hasDerivWithinAt
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (r : DGTrajectoryRegularity K mesh T v vt)
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ j : Fin N,
      MemLp (v s j) 2 (volume.restrict (meshCell mesh j : Set ℝ)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s ↦ (brokenL2Norm mesh (v s)) ^ 2)
      (2 * ∑ j : Fin N, ∫ x, vt t j x * v t j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)))
      (Set.Icc (0 : ℝ) T) t := by
  have hraw := regularityEnergy_hasDerivWithinAt r t ht
  rw [r.regularityPair_eq_integral_sum t ht] at hraw
  apply hraw.congr
  · intro s hs
    exact r.brokenL2Norm_sq_eq_regularityEnergy s hs (hmem s hs)
  · exact r.brokenL2Norm_sq_eq_regularityEnergy t ht (hmem t ht)

def DGTrajectoryRegularity.sub {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ}
    {v vt w wt : DGTrajectory N}
    (rv : DGTrajectoryRegularity K mesh T v vt)
    (rw : DGTrajectoryRegularity K mesh T w wt) :
    DGTrajectoryRegularity K mesh T
      (fun t j x ↦ v t j x - w t j x)
      (fun t j x ↦ vt t j x - wt t j x) where
  coefficient := fun t j i ↦ rv.coefficient t j i - rw.coefficient t j i
  timeDerivativeCoefficient := fun t j i ↦
    rv.timeDerivativeCoefficient t j i - rw.timeDerivativeCoefficient t j i
  value_eq := by
    intro t ht j x hx
    rw [rv.value_eq t ht j x hx, rw.value_eq t ht j x hx,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  timeDerivativeValue_eq := by
    intro t ht j x hx
    rw [rv.timeDerivativeValue_eq t ht j x hx,
      rw.timeDerivativeValue_eq t ht j x hx, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  coefficient_hasDerivWithinAt := by
    intro j i t ht
    exact (rv.coefficient_hasDerivWithinAt j i t ht).sub
      (rw.coefficient_hasDerivWithinAt j i t ht)

end Exp1
