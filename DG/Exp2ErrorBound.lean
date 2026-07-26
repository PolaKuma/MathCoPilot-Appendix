import Exp2FiniteCoordinates

open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter

noncomputable section
namespace Exp2

/-- The explicit finite-dimensional constant controlling the reference-cell projection. -/
def radauPolynomialSobolevConstant (k : ℕ) : ℝ :=
  (2 * l2NormOn referenceCell traceRho + 1) +
    (‖(radauCoordinateInverse k).toContinuousLinearMap‖ *
      (‖momentIntegralCoordinates k‖ *
          (2 * l2NormOn referenceCell traceRho + 1) +
        ‖momentL2Coordinates k‖)) *
      (∑ i, weightedBasisL2Coordinates k i)

lemma radauPolynomialSobolevConstant_nonneg (k : ℕ) :
    0 ≤ radauPolynomialSobolevConstant k := by
  have hρ := l2NormOn_nonneg referenceCell traceRho
  have hT : 0 ≤ 2 * l2NormOn referenceCell traceRho + 1 := by linarith
  have hInv : 0 ≤ ‖(radauCoordinateInverse k).toContinuousLinearMap‖ := norm_nonneg _
  have hI : 0 ≤ ‖momentIntegralCoordinates k‖ := norm_nonneg _
  have hL : 0 ≤ ‖momentL2Coordinates k‖ := norm_nonneg _
  have hA : 0 ≤ ‖(radauCoordinateInverse k).toContinuousLinearMap‖ *
      (‖momentIntegralCoordinates k‖ *
          (2 * l2NormOn referenceCell traceRho + 1) +
        ‖momentL2Coordinates k‖) :=
    mul_nonneg hInv (add_nonneg (mul_nonneg hI hT) hL)
  have hD : 0 ≤ ∑ i, weightedBasisL2Coordinates k i := by
    exact Finset.sum_nonneg fun i hi ↦ l2NormOn_nonneg referenceCell _
  exact add_nonneg hT (mul_nonneg hA hD)

/-- The explicit Gauss--Radau candidate is bounded in `L²` by the full Sobolev norm. -/
lemma radauCandidate_l2NormOn_le (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    l2NormOn referenceCell (fun x ↦ (radauCandidate k w).1.eval x) ≤
      radauPolynomialSobolevConstant k * sobolevNorm w := by
  let q : Polynomial ℝ := Polynomial.X - Polynomial.C 1
  let r := radauCoefficient k w
  let T := 2 * l2NormOn referenceCell traceRho + 1
  let A := ‖(radauCoordinateInverse k).toContinuousLinearMap‖ *
    (‖momentIntegralCoordinates k‖ *
        (2 * l2NormOn referenceCell traceRho + 1) +
      ‖momentL2Coordinates k‖)
  let D := ∑ i, weightedBasisL2Coordinates k i
  let H := sobolevNorm w
  have hconstMem : MemLp (fun _ : ℝ ↦ w 1) 2
      (volume.restrict referenceCell) := by
    let μ := volume.restrict (referenceCell : Set ℝ)
    letI : IsFiniteMeasure μ := by
      rw [isFiniteMeasure_iff]
      simp [μ, referenceCell, cell]
    simpa [μ] using (memLp_const (μ := μ) (w 1))
  have hweightedMem : MemLp (fun x ↦ (q * r.1).eval x) 2
      (volume.restrict referenceCell) := polynomial_eval_memLp_reference _
  have heval : (fun x ↦ (radauCandidate k w).1.eval x) =
      (fun _ : ℝ ↦ w 1) + (fun x ↦ (q * r.1).eval x) := by
    funext x
    simp [radauCandidate, q, r]
  have hconstNorm : l2NormOn referenceCell (fun _ : ℝ ↦ w 1) = |w 1| := by
    have hfun : (fun _ : ℝ ↦ w 1) = (w 1) • (fun _ : ℝ ↦ (1 : ℝ)) := by
      funext x
      simp
    have h := l2NormOn_const_smul referenceCell (w 1) (fun _ : ℝ ↦ (1 : ℝ))
    rw [hfun]
    simpa only [l2NormOn_const_one_reference, mul_one] using h
  have htrace : |w 1| ≤ T * H := by
    simpa [T, H] using w.abs_eval_one_le_sobolevNorm
  have hcoeff : ‖(momentBasis k).equivFun r‖ ≤ A * H := by
    simpa [r, A, H] using radauCoefficient_coordinate_sobolev_bound k w
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun i hi ↦ l2NormOn_nonneg referenceCell _
  have hweighted0 :
      l2NormOn referenceCell (fun x ↦ (q * r.1).eval x) ≤
        ‖(momentBasis k).equivFun r‖ * D := by
    simpa [q, r, D] using weightedPolynomial_l2NormOn_le k r
  have hweighted :
      l2NormOn referenceCell (fun x ↦ (q * r.1).eval x) ≤ A * D * H := by
    calc
      l2NormOn referenceCell (fun x ↦ (q * r.1).eval x) ≤
          ‖(momentBasis k).equivFun r‖ * D := hweighted0
      _ ≤ (A * H) * D := mul_le_mul_of_nonneg_right hcoeff hD
      _ = A * D * H := by ring
  rw [heval]
  calc
    l2NormOn referenceCell
        ((fun _ : ℝ ↦ w 1) + (fun x ↦ (q * r.1).eval x)) ≤
      l2NormOn referenceCell (fun _ : ℝ ↦ w 1) +
        l2NormOn referenceCell (fun x ↦ (q * r.1).eval x) :=
      l2NormOn_add_le hconstMem hweightedMem
    _ = |w 1| + l2NormOn referenceCell (fun x ↦ (q * r.1).eval x) := by
      rw [hconstNorm]
    _ ≤ T * H + A * D * H := add_le_add htrace hweighted
    _ = radauPolynomialSobolevConstant k * sobolevNorm w := by
      simp only [radauPolynomialSobolevConstant, T, A, D, H]
      ring

lemma gaussRadau_l2NormOn_le (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    l2NormOn referenceCell (fun x ↦ (gaussRadau k w).1.eval x) ≤
      radauPolynomialSobolevConstant k * sobolevNorm w := by
  rw [gaussRadau_eq_radauCandidate]
  exact radauCandidate_l2NormOn_le k w

/-- Complete proof of boundedness of the source error functional. -/
theorem gaussRadau_errorFunctional_bounded_complete (k : ℕ) :
    ErrorFunctionalBounded k := by
  refine ⟨radauPolynomialSobolevConstant k + 1, ?_, ?_⟩
  · linarith [radauPolynomialSobolevConstant_nonneg k]
  · intro w z hz hzunit
    have hp : MemLp (fun x ↦ (gaussRadau k w).1.eval x) 2
        (volume.restrict referenceCell) := polynomial_eval_memLp_reference _
    have hw := w.toFun_memLp
    have herr : MemLp (referenceError k w) 2
        (volume.restrict referenceCell) := by
      simpa [referenceError, sub_eq_add_neg] using hp.add hw.neg
    have herrNorm : l2NormOn referenceCell (referenceError k w) ≤
        l2NormOn referenceCell (fun x ↦ (gaussRadau k w).1.eval x) +
          l2NormOn referenceCell w.toFun := by
      have h := l2NormOn_add_le hp hw.neg
      simpa [referenceError, sub_eq_add_neg, l2NormOn_neg] using h
    have hw0 : l2NormOn referenceCell w.toFun ≤ sobolevNorm w := by
      have h := l2NormOn_derivative_le_sobolevNorm w (j := 0) (Nat.zero_le _)
      simpa [w.derivative_zero] using h
    have hpair := abs_integral_mul_le_l2NormOn herr hz
    calc
      |errorFunctional k w z| ≤
          l2NormOn referenceCell (referenceError k w) *
            l2NormOn referenceCell z := by
        simpa [errorFunctional] using hpair
      _ ≤ l2NormOn referenceCell (referenceError k w) * 1 :=
        mul_le_mul_of_nonneg_left hzunit
          (l2NormOn_nonneg referenceCell (referenceError k w))
      _ = l2NormOn referenceCell (referenceError k w) := by ring
      _ ≤ l2NormOn referenceCell (fun x ↦ (gaussRadau k w).1.eval x) +
          l2NormOn referenceCell w.toFun := herrNorm
      _ ≤ radauPolynomialSobolevConstant k * sobolevNorm w +
          sobolevNorm w := add_le_add (gaussRadau_l2NormOn_le k w) hw0
      _ = (radauPolynomialSobolevConstant k + 1) * sobolevNorm w := by ring

end Exp2
