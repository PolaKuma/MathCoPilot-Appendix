import Exp2TraceBoundProbe
import Mathlib.LinearAlgebra.Dual.Basis

open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter

noncomputable section
namespace Exp2

/-- The algebraic isomorphism defined by the positive weighted moment form. -/
def weightedMomentEquiv (k : ℕ) :
    MomentPoly k ≃ₗ[ℝ] Module.Dual ℝ (MomentPoly k) :=
  LinearEquiv.ofBijective (weightedMomentMap k)
    ⟨weightedMomentMap_injective k, weightedMomentMap_surjective k⟩

/-- The unique coefficient polynomial determined by the endpoint and moment data. -/
def radauCoefficient (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) : MomentPoly k :=
  (weightedMomentEquiv k).symm (radauRhs k w)

lemma weightedMomentMap_radauCoefficient (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    weightedMomentMap k (radauCoefficient k w) = radauRhs k w := by
  exact (weightedMomentEquiv k).apply_symm_apply (radauRhs k w)

/-- A fixed finite basis used only for coefficient estimates. -/
def momentBasis (k : ℕ) :
    Module.Basis (Module.Free.ChooseBasisIndex ℝ (MomentPoly k)) ℝ (MomentPoly k) :=
  Module.Free.chooseBasis ℝ (MomentPoly k)

/-- Coordinates in the dual basis are exactly evaluations on the primal basis. -/
lemma dualCoordinates_apply (k : ℕ) (y : Module.Dual ℝ (MomentPoly k))
    (i : Module.Free.ChooseBasisIndex ℝ (MomentPoly k)) :
    (momentBasis k).dualBasis.equivFun y i = y (momentBasis k i) := by
  exact (momentBasis k).dualBasis_equivFun y i

/-- In fixed primal/dual coordinates, inversion of the weighted moment system is a linear map
between two finite products of `ℝ`. -/
def radauCoordinateInverse (k : ℕ) :
    (Module.Free.ChooseBasisIndex ℝ (MomentPoly k) → ℝ) →ₗ[ℝ]
      (Module.Free.ChooseBasisIndex ℝ (MomentPoly k) → ℝ) :=
  (momentBasis k).equivFun.toLinearMap.comp
    ((weightedMomentEquiv k).symm.toLinearMap.comp
      (momentBasis k).dualBasis.equivFun.symm.toLinearMap)

/-- The finite-dimensional coefficient estimate furnished by the moment equations.  Both norms
are the standard supremum norms on the finite coordinate products. -/
lemma radauCoefficient_coordinate_bound (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    ‖(momentBasis k).equivFun (radauCoefficient k w)‖ ≤
      ‖(radauCoordinateInverse k).toContinuousLinearMap‖ *
        ‖(momentBasis k).dualBasis.equivFun (radauRhs k w)‖ := by
  have h := ContinuousLinearMap.le_opNorm
    (f := (radauCoordinateInverse k).toContinuousLinearMap)
    ((momentBasis k).dualBasis.equivFun (radauRhs k w))
  simpa [radauCoordinateInverse, radauCoefficient, weightedMomentEquiv] using h

lemma radauRhs_apply_bound (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) (v : MomentPoly k) :
    |radauRhs k w v| ≤
      |∫ x, v.1.eval x ∂(volume.restrict referenceCell)| * |w 1| +
        l2NormOn referenceCell w.toFun *
          l2NormOn referenceCell (fun x ↦ v.1.eval x) := by
  have hcs := abs_integral_mul_le_l2NormOn w.toFun_memLp
    (polynomial_eval_memLp_reference v.1)
  dsimp [radauRhs]
  calc
    |w 1 * (∫ x, v.1.eval x ∂(volume.restrict referenceCell)) -
        ∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell)| ≤
      |w 1 * (∫ x, v.1.eval x ∂(volume.restrict referenceCell))| +
        |∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell)| := abs_sub _ _
    _ ≤ |∫ x, v.1.eval x ∂(volume.restrict referenceCell)| * |w 1| +
        l2NormOn referenceCell w.toFun *
          l2NormOn referenceCell (fun x ↦ v.1.eval x) := by
      rw [abs_mul]
      calc
        |w 1| * |∫ x, v.1.eval x ∂(volume.restrict referenceCell)| +
            |∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell)| ≤
          |w 1| * |∫ x, v.1.eval x ∂(volume.restrict referenceCell)| +
            l2NormOn referenceCell w.toFun *
              l2NormOn referenceCell (fun x ↦ v.1.eval x) :=
            add_le_add (le_refl _) hcs
        _ = _ := by ring

def momentIntegralCoordinates (k : ℕ) :
    Module.Free.ChooseBasisIndex ℝ (MomentPoly k) → ℝ :=
  fun i ↦ ∫ x, (momentBasis k i).1.eval x ∂(volume.restrict referenceCell)

def momentL2Coordinates (k : ℕ) :
    Module.Free.ChooseBasisIndex ℝ (MomentPoly k) → ℝ :=
  fun i ↦ l2NormOn referenceCell (fun x ↦ (momentBasis k i).1.eval x)

lemma radauRhs_coordinate_norm_bound (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    ‖(momentBasis k).dualBasis.equivFun (radauRhs k w)‖ ≤
      (‖momentIntegralCoordinates k‖ *
          (2 * l2NormOn referenceCell traceRho + 1) +
        ‖momentL2Coordinates k‖) * sobolevNorm w := by
  let A := ‖momentIntegralCoordinates k‖
  let B := ‖momentL2Coordinates k‖
  let T := 2 * l2NormOn referenceCell traceRho + 1
  let H := sobolevNorm w
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hT : 0 ≤ T := by
    dsimp [T]
    have hρ := l2NormOn_nonneg referenceCell traceRho
    linarith
  have hH : 0 ≤ H := sobolevNorm_nonneg w
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg (mul_nonneg hA hT) hB) hH)).2
  intro i
  rw [Real.norm_eq_abs, dualCoordinates_apply]
  have hi := radauRhs_apply_bound k w (momentBasis k i)
  have hIi : |momentIntegralCoordinates k i| ≤ A := by
    simpa [A, momentIntegralCoordinates, Real.norm_eq_abs] using
      norm_le_pi_norm (momentIntegralCoordinates k) i
  have hVi : momentL2Coordinates k i ≤ B := by
    have h := norm_le_pi_norm (momentL2Coordinates k) i
    simpa [B, momentL2Coordinates, abs_of_nonneg
      (l2NormOn_nonneg referenceCell (fun x ↦ (momentBasis k i).1.eval x))] using h
  have htrace : |w 1| ≤ T * H := by
    simpa [T, H] using w.abs_eval_one_le_sobolevNorm
  have hw0 : l2NormOn referenceCell w.toFun ≤ H := by
    have h := l2NormOn_derivative_le_sobolevNorm w (j := 0) (Nat.zero_le _)
    simpa [H, w.derivative_zero] using h
  calc
    |radauRhs k w (momentBasis k i)| ≤
        |momentIntegralCoordinates k i| * |w 1| +
          l2NormOn referenceCell w.toFun * momentL2Coordinates k i := by
      simpa [momentIntegralCoordinates, momentL2Coordinates] using hi
    _ ≤ A * (T * H) + H * B := by
      exact add_le_add
        (mul_le_mul hIi htrace (abs_nonneg _) hA)
        (mul_le_mul hw0 hVi
          (by
            dsimp [momentL2Coordinates]
            exact l2NormOn_nonneg referenceCell
              (fun x ↦ (momentBasis k i).1.eval x)) hH)
    _ = (A * T + B) * H := by ring
    _ = (‖momentIntegralCoordinates k‖ *
          (2 * l2NormOn referenceCell traceRho + 1) +
        ‖momentL2Coordinates k‖) * sobolevNorm w := by rfl

lemma radauCoefficient_coordinate_sobolev_bound (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    ‖(momentBasis k).equivFun (radauCoefficient k w)‖ ≤
      (‖(radauCoordinateInverse k).toContinuousLinearMap‖ *
        (‖momentIntegralCoordinates k‖ *
            (2 * l2NormOn referenceCell traceRho + 1) +
          ‖momentL2Coordinates k‖)) * sobolevNorm w := by
  have hcoeff := radauCoefficient_coordinate_bound k w
  have hrhs := radauRhs_coordinate_norm_bound k w
  have hop : 0 ≤ ‖(radauCoordinateInverse k).toContinuousLinearMap‖ := norm_nonneg _
  calc
    ‖(momentBasis k).equivFun (radauCoefficient k w)‖ ≤
        ‖(radauCoordinateInverse k).toContinuousLinearMap‖ *
          ‖(momentBasis k).dualBasis.equivFun (radauRhs k w)‖ := hcoeff
    _ ≤ ‖(radauCoordinateInverse k).toContinuousLinearMap‖ *
        ((‖momentIntegralCoordinates k‖ *
            (2 * l2NormOn referenceCell traceRho + 1) +
          ‖momentL2Coordinates k‖) * sobolevNorm w) :=
      mul_le_mul_of_nonneg_left hrhs hop
    _ = _ := by ring

/-- The `L²` sizes of the fixed weighted basis polynomials. -/
def weightedBasisL2Coordinates (k : ℕ) :
    Module.Free.ChooseBasisIndex ℝ (MomentPoly k) → ℝ :=
  fun i ↦ l2NormOn referenceCell (fun x ↦
    (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
      (momentBasis k i).1).eval x)

set_option maxHeartbeats 800000 in
/-- Expanding in the fixed finite basis turns the weighted polynomial `L²` norm into a
finite-coordinate estimate. -/
lemma weightedPolynomial_l2NormOn_le (k : ℕ) (r : MomentPoly k) :
    l2NormOn referenceCell (fun x ↦
        (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * r.1).eval x) ≤
      ‖(momentBasis k).equivFun r‖ *
        ∑ i, weightedBasisL2Coordinates k i := by
  let b := momentBasis k
  let a := b.equivFun r
  let q : Polynomial ℝ := Polynomial.X - Polynomial.C 1
  let F : Module.Free.ChooseBasisIndex ℝ (MomentPoly k) → ℝ → ℝ :=
    fun i x ↦ (q * (b i).1).eval x
  have hrsub : ∑ i, a i • b i = r := b.sum_equivFun r
  have hrpoly : ∑ i, a i • (b i).1 = r.1 := by
    simpa using congrArg Subtype.val hrsub
  have hpoly : q * r.1 = ∑ i, a i • (q * (b i).1) := by
    rw [← hrpoly]
    simp [Finset.mul_sum]
  have hfun : (fun x ↦ (q * r.1).eval x) = ∑ i, a i • F i := by
    funext x
    rw [hpoly]
    change (Polynomial.evalRingHom x)
      (∑ i, a i • (q * (b i).1)) = _
    rw [map_sum]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    change Polynomial.eval x (a i • (q * (b i).1)) = _
    rw [Polynomial.eval_smul]
    rfl
  change l2NormOn referenceCell (fun x ↦ (q * r.1).eval x) ≤ _
  calc
    l2NormOn referenceCell (fun x ↦ (q * r.1).eval x) =
      l2NormOn referenceCell (∑ i, a i • F i) :=
      congrArg (l2NormOn referenceCell) hfun
    _ ≤ ∑ i, l2NormOn referenceCell (a i • F i) := by
        apply l2NormOn_finset_sum_le
        intro i hi
        simpa [F] using
          (polynomial_eval_memLp_reference (q * (b i).1)).const_smul (a i)
    _ = ∑ i, |a i| * weightedBasisL2Coordinates k i := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [F, q, weightedBasisL2Coordinates, b] using
        l2NormOn_const_smul referenceCell (a i) (F i)
    _ ≤ ∑ i, ‖a‖ * weightedBasisL2Coordinates k i := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right
      · simpa [Real.norm_eq_abs] using norm_le_pi_norm a i
      · exact l2NormOn_nonneg referenceCell _
    _ = ‖(momentBasis k).equivFun r‖ *
        ∑ i, weightedBasisL2Coordinates k i := by
      simp [a, b, Finset.mul_sum]

def radauCandidate (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) : PolyLE k :=
  ⟨Polynomial.C (w 1) +
      ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * (radauCoefficient k w).1,
    radauPolynomial_mem k (w 1) (radauCoefficient k w)⟩

lemma radauCandidate_spec (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    IsGaussRadauAt k w (radauCandidate k w) := by
  have hr := weightedMomentMap_radauCoefficient k w
  constructor
  · intro v hv
    let vsub : MomentPoly k := ⟨v, mem_MomentPoly_of_natDegree_lt hv⟩
    have hrv := LinearMap.congr_fun hr vsub
    change (∫ x, (1 - x) * (radauCoefficient k w).1.eval x * v.eval x
        ∂(volume.restrict referenceCell)) =
      w 1 * (∫ x, v.eval x ∂(volume.restrict referenceCell)) -
        ∫ x, w x * v.eval x ∂(volume.restrict referenceCell) at hrv
    have hvInt := polynomial_eval_integrable_reference v
    have hvLp := polynomial_eval_memLp_reference v
    have hwLp := w.toFun_memLp
    have hwvInt : Integrable (fun x ↦ w x * v.eval x)
        (volume.restrict referenceCell) := hwLp.integrable_mul hvLp
    have hcInt : Integrable (fun x ↦ w 1 * v.eval x)
        (volume.restrict referenceCell) := hvInt.const_mul (w 1)
    have hbInt := polynomial_weighted_product_integrable (radauCoefficient k w).1 v
    have houter :
        (∫ x, (w 1 * v.eval x - w x * v.eval x) -
            (1 - x) * (radauCoefficient k w).1.eval x * v.eval x
            ∂(volume.restrict referenceCell)) =
          (∫ x, w 1 * v.eval x - w x * v.eval x
              ∂(volume.restrict referenceCell)) -
            ∫ x, (1 - x) * (radauCoefficient k w).1.eval x * v.eval x
              ∂(volume.restrict referenceCell) := by
      simpa only [Pi.sub_apply] using integral_sub (hcInt.sub hwvInt) hbInt
    have hinner :
        (∫ x, w 1 * v.eval x - w x * v.eval x
            ∂(volume.restrict referenceCell)) =
          (∫ x, w 1 * v.eval x ∂(volume.restrict referenceCell)) -
            ∫ x, w x * v.eval x ∂(volume.restrict referenceCell) := by
      simpa only [Pi.sub_apply] using integral_sub hcInt hwvInt
    calc
      (∫ x, ((radauCandidate k w).1.eval x - w x) * v.eval x
          ∂(volume.restrict referenceCell)) =
          ∫ x, ((w 1 * v.eval x - w x * v.eval x) -
            (1 - x) * (radauCoefficient k w).1.eval x * v.eval x)
            ∂(volume.restrict referenceCell) := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [radauCandidate, Polynomial.eval_add, Polynomial.eval_C,
                Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X]
              ring
      _ = ((∫ x, w 1 * v.eval x ∂(volume.restrict referenceCell)) -
            ∫ x, w x * v.eval x ∂(volume.restrict referenceCell)) -
          ∫ x, (1 - x) * (radauCoefficient k w).1.eval x * v.eval x
            ∂(volume.restrict referenceCell) := by
              rw [houter, hinner]
      _ = (w 1 * (∫ x, v.eval x ∂(volume.restrict referenceCell)) -
            ∫ x, w x * v.eval x ∂(volume.restrict referenceCell)) -
          ∫ x, (1 - x) * (radauCoefficient k w).1.eval x * v.eval x
            ∂(volume.restrict referenceCell) := by
              rw [integral_const_mul]
      _ = 0 := by rw [← hrv]; ring
  · simp [radauCandidate]

lemma gaussRadau_eq_radauCandidate (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    gaussRadau k w = radauCandidate k w := by
  exact gaussRadauAt_unique k w (gaussRadau_spec k w) (radauCandidate_spec k w)

end Exp2
