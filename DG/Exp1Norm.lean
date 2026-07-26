import Exp1Core
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ENNReal MeasureTheory Topology Interval BigOperators
open MeasureTheory Set

noncomputable section
namespace Exp1

/-- Cellwise `L²` obeys the triangle inequality for broken fields. -/
theorem brokenL2Norm_triangle {N : ℕ} (mesh : PeriodicMesh N)
    (v w : DGField N)
    (hv : ∀ j : Fin N, MemLp (v j) 2 (volume.restrict (meshCell mesh j : Set ℝ)))
    (hw : ∀ j : Fin N, MemLp (w j) 2 (volume.restrict (meshCell mesh j : Set ℝ))) :
    brokenL2Norm mesh (fun j x ↦ v j x + w j x) ≤
      brokenL2Norm mesh v + brokenL2Norm mesh w := by
  let V : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun j ↦ Exp2.l2NormOn (meshCell mesh j) (v j))
  let W : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun j ↦ Exp2.l2NormOn (meshCell mesh j) (w j))
  let S : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun j ↦ Exp2.l2NormOn (meshCell mesh j) (fun x ↦ v j x + w j x))
  have hV : ‖V‖ = brokenL2Norm mesh v := by
    rw [EuclideanSpace.norm_eq]
    unfold brokenL2Norm
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [V, Real.norm_eq_abs,
      abs_of_nonneg (Exp2.l2NormOn_nonneg _ _)]
  have hW : ‖W‖ = brokenL2Norm mesh w := by
    rw [EuclideanSpace.norm_eq]
    unfold brokenL2Norm
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [W, Real.norm_eq_abs,
      abs_of_nonneg (Exp2.l2NormOn_nonneg _ _)]
  have hS : ‖S‖ = brokenL2Norm mesh (fun j x ↦ v j x + w j x) := by
    rw [EuclideanSpace.norm_eq]
    unfold brokenL2Norm
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [S, Real.norm_eq_abs,
      abs_of_nonneg (Exp2.l2NormOn_nonneg _ _)]
  have hcell : ∀ j : Fin N,
      Exp2.l2NormOn (meshCell mesh j) (fun x ↦ v j x + w j x) ≤
        Exp2.l2NormOn (meshCell mesh j) (v j) +
          Exp2.l2NormOn (meshCell mesh j) (w j) := by
    intro j
    simpa only [Pi.add_apply] using Exp2.l2NormOn_add_le (hv j) (hw j)
  have hcoord : ‖S‖ ≤ ‖V + W‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j hj
    simp only [S, V, W, PiLp.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (Exp2.l2NormOn_nonneg _ _)]
    have hs := Exp2.l2NormOn_nonneg (meshCell mesh j)
      (fun x ↦ v j x + w j x)
    have hvn := Exp2.l2NormOn_nonneg (meshCell mesh j) (v j)
    have hwn := Exp2.l2NormOn_nonneg (meshCell mesh j) (w j)
    rw [abs_of_nonneg (add_nonneg hvn hwn)]
    nlinarith [hcell j]
  rw [← hS, ← hV, ← hW]
  exact hcoord.trans (norm_add_le V W)

end Exp1
