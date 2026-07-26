import Exp1Norm
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral

open scoped ENNReal MeasureTheory Topology Interval BigOperators
open MeasureTheory Set Filter

noncomputable section
namespace Exp1

lemma cellRight_mem_unit {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) :
    cellRight mesh j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← mesh.left_boundary]
    exact mesh.nodes_strictMono.monotone (Fin.zero_le _)
  · rw [← mesh.right_boundary]
    exact mesh.nodes_strictMono.monotone (Fin.le_last _)

lemma cellLeft_mem_unit {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) :
    cellLeft mesh j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← mesh.left_boundary]
    exact mesh.nodes_strictMono.monotone (Fin.zero_le _)
  · rw [← mesh.right_boundary]
    exact mesh.nodes_strictMono.monotone (Fin.le_last _)

/-- Joint continuity supplies the uniform time-derivative bound on the compact collar used
for differentiation under the integral. -/
lemma SmoothPeriodicAdvectionSolution.uniformTimeDerivativeBound
    {K : ℕ} {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (hT : 0 ≤ T) : ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) (T + 1),
        |solution.ut x t| ≤ M := by
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) (T + 1)
  let f : ℝ × ℝ → ℝ := fun z ↦ |solution.ut z.1 z.2|
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hnonempty : S.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    exact ⟨⟨le_rfl, by norm_num⟩, ⟨by norm_num, by linarith⟩⟩
  have hfcont : Continuous f := solution.ut_joint_continuous.abs
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hnonempty hfcont.continuousOn
  refine ⟨f z, abs_nonneg _, ?_⟩
  intro x hx t ht
  have hxt : (x, t) ∈ S := ⟨hx, ⟨ht.1.le, ht.2.le⟩⟩
  exact hmax hxt

def localProjectionValue (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T) : DGTrajectory N :=
  fun t j x ↦ (Exp2.gaussRadau K (solution.uCellPullback mesh j t)).1.eval
    ((x - cellLeft mesh j) / cellLength mesh j)

def localProjectionTimeDerivativeValue (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T) : DGTrajectory N :=
  fun t j x ↦ (Exp2.gaussRadau K (solution.utCellPullback mesh j t)).1.eval
    ((x - cellLeft mesh j) / cellLength mesh j)

def pullbackRadauData (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) :
    Module.Free.ChooseBasisIndex ℝ (Exp2.MomentPoly K) → ℝ :=
  fun i ↦ solution.u (cellRight mesh j) t *
      (∫ xHat, (Exp2.momentBasis K i).1.eval xHat
        ∂(volume.restrict Exp2.referenceCell)) -
    ∫ xHat, solution.u (cellLeft mesh j + cellLength mesh j * xHat) t *
        (Exp2.momentBasis K i).1.eval xHat
      ∂(volume.restrict Exp2.referenceCell)

def pullbackRadauTimeDerivativeData (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) :
    Module.Free.ChooseBasisIndex ℝ (Exp2.MomentPoly K) → ℝ :=
  fun i ↦ solution.ut (cellRight mesh j) t *
      (∫ xHat, (Exp2.momentBasis K i).1.eval xHat
        ∂(volume.restrict Exp2.referenceCell)) -
    ∫ xHat, solution.ut (cellLeft mesh j + cellLength mesh j * xHat) t *
        (Exp2.momentBasis K i).1.eval xHat
      ∂(volume.restrict Exp2.referenceCell)

/-- Joint smoothness and the uniform time-derivative bound justify differentiation of every
fixed polynomial moment. -/
lemma SmoothPeriodicAdvectionSolution.pullbackMomentTimeDerivative
    (solution : SmoothPeriodicAdvectionSolution K a T) {N : ℕ}
    (mesh : PeriodicMesh N) (j : Fin N) (q : Polynomial ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (fun s ↦ ∫ xHat,
        solution.u (cellLeft mesh j + cellLength mesh j * xHat) s * q.eval xHat
          ∂(volume.restrict Exp2.referenceCell))
      (∫ xHat,
        solution.ut (cellLeft mesh j + cellLength mesh j * xHat) t * q.eval xHat
          ∂(volume.restrict Exp2.referenceCell))
      (Set.Icc (0 : ℝ) T) t := by
  let μ := volume.restrict (Exp2.referenceCell : Set ℝ)
  let s : Set ℝ := Set.Ioo (-1 : ℝ) (T + 1)
  let F : ℝ → ℝ → ℝ := fun r xHat ↦
    solution.u (cellLeft mesh j + cellLength mesh j * xHat) r * q.eval xHat
  let F' : ℝ → ℝ → ℝ := fun r xHat ↦
    solution.ut (cellLeft mesh j + cellLength mesh j * xHat) r * q.eval xHat
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨M, hM, hboundM⟩ := solution.uniformTimeDerivativeBound hT0
  let bound : ℝ → ℝ := fun xHat ↦ M * |q.eval xHat|
  have ht_s : t ∈ s := by
    dsimp [s]
    constructor <;> linarith [ht.1, ht.2]
  have hs : s ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht_s
  have hphysical : ∀ xHat ∈ Set.Icc (0 : ℝ) 1,
      cellLeft mesh j + cellLength mesh j * xHat ∈ Set.Icc (0 : ℝ) 1 := by
    intro xHat hxHat
    have hl := cellLeft_mem_unit mesh j
    have hr := cellRight_mem_unit mesh j
    have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
      simp [cellLength]
    constructor
    · exact hl.1.trans (le_add_of_nonneg_right
        (mul_nonneg (cellLength_pos mesh j).le hxHat.1))
    · rw [hright] at hr
      have hm := mul_le_mul_of_nonneg_left hxHat.2 (cellLength_pos mesh j).le
      nlinarith [hm, hr.2]
  have hFcont : ∀ r : ℝ, Continuous (F r) := by
    intro r
    have harg : Continuous (fun xHat : ℝ ↦
        (cellLeft mesh j + cellLength mesh j * xHat, r)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).prodMk continuous_const
    have hu := solution.u_joint_continuous.comp harg
    simpa [F, Function.uncurry] using hu.mul (Exp2.polynomial_eval_continuous q)
  have hF'cont : ∀ r : ℝ, Continuous (F' r) := by
    intro r
    have harg : Continuous (fun xHat : ℝ ↦
        (cellLeft mesh j + cellLength mesh j * xHat, r)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).prodMk continuous_const
    have hu := solution.ut_joint_continuous.comp harg
    simpa [F', Function.uncurry] using hu.mul (Exp2.polynomial_eval_continuous q)
  have hF_meas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) μ := by
    filter_upwards with r
    exact (hFcont r).aestronglyMeasurable
  have hF_int : Integrable (F t) μ := by
    have hIcc : IntegrableOn (F t) (Set.Icc (0 : ℝ) 1) volume :=
      (hFcont t).integrableOn_Icc
    apply hIcc.mono_set
    intro x hx
    exact ⟨hx.1.le, by simpa using hx.2.le⟩
  have hF'_meas : AEStronglyMeasurable (F' t) μ :=
    (hF'cont t).aestronglyMeasurable
  have hboundInt : Integrable bound μ := by
    have hq := (Exp2.polynomial_eval_integrable_reference q).norm
    simpa [bound, Real.norm_eq_abs] using hq.const_mul M
  have h_bound : ∀ᵐ xHat ∂μ, ∀ r ∈ s, ‖F' r xHat‖ ≤ bound xHat := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
    intro r hr
    have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
    have hu := hboundM _ (hphysical xHat hxHat') r hr
    dsimp [F', bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  have h_diff : ∀ᵐ xHat ∂μ, ∀ r ∈ s,
      HasDerivAt (F · xHat) (F' r xHat) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
    intro r hr
    have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
    have htime := solution.timeDerivative _ (hphysical xHat hxHat') r hr
    simpa [F, F'] using htime.mul_const (q.eval xHat)
  have hraw := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := bound) hs hF_meas hF_int
      hF'_meas h_bound hboundInt h_diff
  simpa [μ, F, F'] using hraw.2.hasDerivWithinAt

lemma pullbackRadauData_hasDerivWithinAt (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (pullbackRadauData K mesh solution j)
      (pullbackRadauTimeDerivativeData K mesh solution j t)
      (Set.Icc (0 : ℝ) T) t := by
  rw [hasDerivWithinAt_pi]
  intro i
  have hend : HasDerivWithinAt (solution.u (cellRight mesh j))
      (solution.ut (cellRight mesh j) t) (Set.Icc (0 : ℝ) T) t :=
    (solution.timeDerivative (cellRight mesh j) (cellRight_mem_unit mesh j) t
      (by constructor <;> linarith [ht.1, ht.2])).hasDerivWithinAt
  have hendMul := hend.mul_const
    (∫ xHat, (Exp2.momentBasis K i).1.eval xHat
      ∂(volume.restrict Exp2.referenceCell))
  have hmoment := solution.pullbackMomentTimeDerivative mesh j
    (Exp2.momentBasis K i).1 t ht
  simpa only [pullbackRadauData, pullbackRadauTimeDerivativeData] using
    hendMul.sub hmoment

def pullbackRadauCoefficientCoordinates (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) :
    Module.Free.ChooseBasisIndex ℝ (Exp2.MomentPoly K) → ℝ :=
  Exp2.radauCoordinateInverse K (pullbackRadauData K mesh solution j t)

def pullbackRadauTimeDerivativeCoefficientCoordinates (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) :
    Module.Free.ChooseBasisIndex ℝ (Exp2.MomentPoly K) → ℝ :=
  Exp2.radauCoordinateInverse K
    (pullbackRadauTimeDerivativeData K mesh solution j t)

lemma pullbackRadauCoefficientCoordinates_hasDerivWithinAt (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (pullbackRadauCoefficientCoordinates K mesh solution j)
      (pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t)
      (Set.Icc (0 : ℝ) T) t := by
  have hdata := pullbackRadauData_hasDerivWithinAt K mesh solution j t ht
  have hlin : HasFDerivAt
      (Exp2.radauCoordinateInverse K).toContinuousLinearMap
      (Exp2.radauCoordinateInverse K).toContinuousLinearMap
      (pullbackRadauData K mesh solution j t) :=
    (Exp2.radauCoordinateInverse K).toContinuousLinearMap.hasFDerivAt
  have hcomp := hlin.comp_hasDerivWithinAt t hdata
  simpa [pullbackRadauCoefficientCoordinates,
    pullbackRadauTimeDerivativeCoefficientCoordinates] using hcomp

def explicitLocalProjectionEval (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t xHat : ℝ) : ℝ :=
  solution.u (cellRight mesh j) t + (xHat - 1) *
    ∑ i, pullbackRadauCoefficientCoordinates K mesh solution j t i *
      (Exp2.momentBasis K i).1.eval xHat

def explicitLocalProjectionTimeDerivativeEval (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t xHat : ℝ) : ℝ :=
  solution.ut (cellRight mesh j) t + (xHat - 1) *
    ∑ i, pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t i *
      (Exp2.momentBasis K i).1.eval xHat

lemma explicitLocalProjectionEval_hasDerivWithinAt (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (xHat : ℝ) :
    HasDerivWithinAt (fun s ↦ explicitLocalProjectionEval K mesh solution j s xHat)
      (explicitLocalProjectionTimeDerivativeEval K mesh solution j t xHat)
      (Set.Icc (0 : ℝ) T) t := by
  have hend : HasDerivWithinAt (solution.u (cellRight mesh j))
      (solution.ut (cellRight mesh j) t) (Set.Icc (0 : ℝ) T) t :=
    (solution.timeDerivative (cellRight mesh j) (cellRight_mem_unit mesh j) t
      (by constructor <;> linarith [ht.1, ht.2])).hasDerivWithinAt
  have hcoords := pullbackRadauCoefficientCoordinates_hasDerivWithinAt
    K mesh solution j t ht
  have hsum : HasDerivWithinAt
      (fun s ↦ ∑ i, pullbackRadauCoefficientCoordinates K mesh solution j s i *
        (Exp2.momentBasis K i).1.eval xHat)
      (∑ i, pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t i *
        (Exp2.momentBasis K i).1.eval xHat)
      (Set.Icc (0 : ℝ) T) t := by
    have hterm : ∀ i ∈ (Finset.univ : Finset
        (Module.Free.ChooseBasisIndex ℝ (Exp2.MomentPoly K))),
        HasDerivWithinAt
          (fun s ↦ pullbackRadauCoefficientCoordinates K mesh solution j s i *
            (Exp2.momentBasis K i).1.eval xHat)
          (pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t i *
            (Exp2.momentBasis K i).1.eval xHat)
          (Set.Icc (0 : ℝ) T) t := by
      intro i hi
      exact (hasDerivWithinAt_pi.mp hcoords i).mul_const _
    have hraw := HasDerivWithinAt.sum hterm
    have hfun :
        (fun s ↦ ∑ i, pullbackRadauCoefficientCoordinates K mesh solution j s i *
          (Exp2.momentBasis K i).1.eval xHat) =
        ∑ i, (fun s ↦ pullbackRadauCoefficientCoordinates K mesh solution j s i *
          (Exp2.momentBasis K i).1.eval xHat) := by
      funext s
      simp
    rw [hfun]
    exact hraw
  simpa only [explicitLocalProjectionEval,
    explicitLocalProjectionTimeDerivativeEval] using
    hend.add (hsum.const_mul (xHat - 1))

/-- The explicit Radau polynomial reconstructed from the differentiable moment
coordinates.  This representation exposes ordinary monomial coefficients, which
is what is needed for the finite-dimensional energy chain rule. -/
def explicitLocalProjectionPolynomial (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) : Exp2.PolyLE K :=
  let r : Exp2.MomentPoly K :=
    (Exp2.momentBasis K).equivFun.symm
      (pullbackRadauCoefficientCoordinates K mesh solution j t)
  ⟨Polynomial.C (solution.u (cellRight mesh j) t) +
      ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * r.1,
    Exp2.radauPolynomial_mem K (solution.u (cellRight mesh j) t) r⟩

def explicitLocalProjectionTimeDerivativePolynomial (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) : Exp2.PolyLE K :=
  let r : Exp2.MomentPoly K :=
    (Exp2.momentBasis K).equivFun.symm
      (pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t)
  ⟨Polynomial.C (solution.ut (cellRight mesh j) t) +
      ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * r.1,
    Exp2.radauPolynomial_mem K (solution.ut (cellRight mesh j) t) r⟩

lemma explicitLocalProjectionPolynomial_eval (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t xHat : ℝ) :
    (explicitLocalProjectionPolynomial K mesh solution j t).1.eval xHat =
      explicitLocalProjectionEval K mesh solution j t xHat := by
  let r : Exp2.MomentPoly K :=
    (Exp2.momentBasis K).equivFun.symm
      (pullbackRadauCoefficientCoordinates K mesh solution j t)
  have hsum := (Exp2.momentBasis K).sum_equivFun r
  have hsum' :
      (∑ i, pullbackRadauCoefficientCoordinates K mesh solution j t i •
        (Exp2.momentBasis K i)) = r := by
    simpa [r] using hsum
  let evalMap : Exp2.MomentPoly K →ₗ[ℝ] ℝ :=
    { toFun := fun q ↦ q.1.eval xHat
      map_add' := by intro q s; simp
      map_smul' := by intro c q; simp [Polynomial.eval_smul] }
  have heval := congrArg evalMap hsum'
  have heval' :
      (∑ i, pullbackRadauCoefficientCoordinates K mesh solution j t i *
        (Exp2.momentBasis K i).1.eval xHat) = r.1.eval xHat := by
    simpa only [map_sum, map_smul, evalMap, smul_eq_mul] using heval
  simp only [explicitLocalProjectionPolynomial, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, explicitLocalProjectionEval]
  rw [← heval']

lemma explicitLocalProjectionTimeDerivativePolynomial_eval (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t xHat : ℝ) :
    (explicitLocalProjectionTimeDerivativePolynomial K mesh solution j t).1.eval xHat =
      explicitLocalProjectionTimeDerivativeEval K mesh solution j t xHat := by
  let r : Exp2.MomentPoly K :=
    (Exp2.momentBasis K).equivFun.symm
      (pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t)
  have hsum := (Exp2.momentBasis K).sum_equivFun r
  have hsum' :
      (∑ i, pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t i •
        (Exp2.momentBasis K i)) = r := by
    simpa [r] using hsum
  let evalMap : Exp2.MomentPoly K →ₗ[ℝ] ℝ :=
    { toFun := fun q ↦ q.1.eval xHat
      map_add' := by intro q s; simp
      map_smul' := by intro c q; simp [Polynomial.eval_smul] }
  have heval := congrArg evalMap hsum'
  have heval' :
      (∑ i, pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t i *
        (Exp2.momentBasis K i).1.eval xHat) = r.1.eval xHat := by
    simpa only [map_sum, map_smul, evalMap, smul_eq_mul] using heval
  simp only [explicitLocalProjectionTimeDerivativePolynomial,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X,
    explicitLocalProjectionTimeDerivativeEval]
  rw [← heval']

lemma explicitLocalProjectionPolynomial_coefficient_hasDerivWithinAt
    (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (i : Fin (K + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (fun s ↦ (Polynomial.degreeLTEquiv ℝ (K + 1))
        (explicitLocalProjectionPolynomial K mesh solution j s) i)
      ((Polynomial.degreeLTEquiv ℝ (K + 1))
        (explicitLocalProjectionTimeDerivativePolynomial K mesh solution j t) i)
      (Set.Icc (0 : ℝ) T) t := by
  change HasDerivWithinAt
    (fun s ↦ (explicitLocalProjectionPolynomial K mesh solution j s).1.coeff i)
    ((explicitLocalProjectionTimeDerivativePolynomial K mesh solution j t).1.coeff i)
    (Set.Icc (0 : ℝ) T) t
  have hend : HasDerivWithinAt (solution.u (cellRight mesh j))
      (solution.ut (cellRight mesh j) t) (Set.Icc (0 : ℝ) T) t :=
    (solution.timeDerivative (cellRight mesh j) (cellRight_mem_unit mesh j) t
      (by constructor <;> linarith [ht.1, ht.2])).hasDerivWithinAt
  have hcoords := pullbackRadauCoefficientCoordinates_hasDerivWithinAt
    K mesh solution j t ht
  have hendCoeff : HasDerivWithinAt
      (fun s ↦ (Polynomial.C (solution.u (cellRight mesh j) s)).coeff i)
      ((Polynomial.C (solution.ut (cellRight mesh j) t)).coeff i)
      (Set.Icc (0 : ℝ) T) t := by
    by_cases hi : (i : ℕ) = 0
    · simpa [hi] using hend
    · simpa [Polynomial.coeff_C, hi] using
        (hasDerivWithinAt_const (x := t) (c := (0 : ℝ)) (s := Set.Icc (0 : ℝ) T))
  have hsum : HasDerivWithinAt
      (fun s ↦ ∑ m, pullbackRadauCoefficientCoordinates K mesh solution j s m *
        (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
          (Exp2.momentBasis K m).1).coeff i)
      (∑ m, pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t m *
        (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
          (Exp2.momentBasis K m).1).coeff i)
      (Set.Icc (0 : ℝ) T) t := by
    have hraw := HasDerivWithinAt.sum (u := Finset.univ)
      (fun m hm ↦ (hasDerivWithinAt_pi.mp hcoords m).mul_const
        ((((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
          (Exp2.momentBasis K m).1).coeff i))
    have hfun :
        (fun s ↦ ∑ m, pullbackRadauCoefficientCoordinates K mesh solution j s m *
          (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
            (Exp2.momentBasis K m).1).coeff i) =
        ∑ m, (fun s ↦ pullbackRadauCoefficientCoordinates K mesh solution j s m *
          (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
            (Exp2.momentBasis K m).1).coeff i) := by
      funext s
      simp
    rw [hfun]
    exact hraw
  have hcoeff (coords : Module.Free.ChooseBasisIndex ℝ (Exp2.MomentPoly K) → ℝ) :
      (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
        ((Exp2.momentBasis K).equivFun.symm coords).1).coeff i =
      ∑ m, coords m * (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) *
        (Exp2.momentBasis K m).1).coeff i := by
    let r : Exp2.MomentPoly K := (Exp2.momentBasis K).equivFun.symm coords
    have hbasis := (Exp2.momentBasis K).sum_equivFun r
    have h := congrArg (fun q : Exp2.MomentPoly K ↦
      (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * q.1).coeff i) hbasis
    simpa [r, Finset.mul_sum] using h
  have hadd := hendCoeff.add hsum
  simpa only [explicitLocalProjectionPolynomial,
    explicitLocalProjectionTimeDerivativePolynomial,
    Polynomial.coeff_add,
    hcoeff] using hadd

lemma pullbackRadauData_eq_dualCoordinates (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pullbackRadauData K mesh solution j t =
      (Exp2.momentBasis K).dualBasis.equivFun
        (Exp2.radauRhs K (solution.uCellPullback mesh j t)) := by
  funext i
  rw [Exp2.dualCoordinates_apply]
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
    simp [cellLength]
  have hend := solution.uCellPullback_eq mesh j t ht 1 hone
  have hend' : solution.uCellPullback mesh j t 1 = solution.u (cellRight mesh j) t := by
    rw [hend]
    simpa [mul_one] using congrArg (fun x ↦ solution.u x t) hright.symm
  have hint :
      (∫ xHat, solution.uCellPullback mesh j t xHat *
          (Exp2.momentBasis K i).1.eval xHat
        ∂(volume.restrict Exp2.referenceCell)) =
      ∫ xHat, solution.u (cellLeft mesh j + cellLength mesh j * xHat) t *
          (Exp2.momentBasis K i).1.eval xHat
        ∂(volume.restrict Exp2.referenceCell) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
    have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
    rw [solution.uCellPullback_eq mesh j t ht xHat hxHat']
  simp only [pullbackRadauData, Exp2.radauRhs, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [hend', hint]

lemma pullbackRadauCoefficientCoordinates_eq (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pullbackRadauCoefficientCoordinates K mesh solution j t =
      (Exp2.momentBasis K).equivFun
        (Exp2.radauCoefficient K (solution.uCellPullback mesh j t)) := by
  rw [pullbackRadauCoefficientCoordinates, pullbackRadauData_eq_dualCoordinates
    K mesh solution j t ht]
  simp [Exp2.radauCoordinateInverse, Exp2.radauCoefficient,
    Exp2.weightedMomentEquiv]

lemma localProjectionValue_eq_explicit (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (xHat : ℝ) :
    localProjectionValue K mesh solution t j
        (cellLeft mesh j + cellLength mesh j * xHat) =
      explicitLocalProjectionEval K mesh solution j t xHat := by
  have hcoord :
      (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
          cellLength mesh j = xHat := by
    rw [add_sub_cancel_left]
    exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
    simp [cellLength]
  have hend : solution.uCellPullback mesh j t 1 = solution.u (cellRight mesh j) t := by
    rw [solution.uCellPullback_eq mesh j t ht 1 hone]
    simpa [mul_one] using congrArg (fun x ↦ solution.u x t) hright.symm
  have hsum := (Exp2.momentBasis K).sum_equivFun
    (Exp2.radauCoefficient K (solution.uCellPullback mesh j t))
  have hsumEval :
      (∑ i, (Exp2.momentBasis K).equivFun
          (Exp2.radauCoefficient K (solution.uCellPullback mesh j t)) i *
          (Exp2.momentBasis K i).1.eval xHat) =
        (Exp2.radauCoefficient K (solution.uCellPullback mesh j t)).1.eval xHat := by
    let evalMap : Exp2.MomentPoly K →ₗ[ℝ] ℝ :=
      { toFun := fun r ↦ r.1.eval xHat
        map_add' := by intro r s; simp
        map_smul' := by intro c r; simp [Polynomial.eval_smul] }
    have h := congrArg evalMap hsum
    simpa only [map_sum, map_smul, evalMap, smul_eq_mul] using h
  simp only [localProjectionValue, hcoord, Exp2.gaussRadau_eq_radauCandidate,
    Exp2.radauCandidate, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    explicitLocalProjectionEval]
  rw [pullbackRadauCoefficientCoordinates_eq K mesh solution j t ht]
  rw [hend]
  rw [hsumEval]

lemma pullbackRadauTimeDerivativeData_eq_dualCoordinates (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pullbackRadauTimeDerivativeData K mesh solution j t =
      (Exp2.momentBasis K).dualBasis.equivFun
        (Exp2.radauRhs K (solution.utCellPullback mesh j t)) := by
  funext i
  rw [Exp2.dualCoordinates_apply]
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
    simp [cellLength]
  have hend := solution.utCellPullback_eq mesh j t ht 1 hone
  have hend' : solution.utCellPullback mesh j t 1 = solution.ut (cellRight mesh j) t := by
    rw [hend]
    simpa [mul_one] using congrArg (fun x ↦ solution.ut x t) hright.symm
  have hint :
      (∫ xHat, solution.utCellPullback mesh j t xHat *
          (Exp2.momentBasis K i).1.eval xHat
        ∂(volume.restrict Exp2.referenceCell)) =
      ∫ xHat, solution.ut (cellLeft mesh j + cellLength mesh j * xHat) t *
          (Exp2.momentBasis K i).1.eval xHat
        ∂(volume.restrict Exp2.referenceCell) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
    have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
    rw [solution.utCellPullback_eq mesh j t ht xHat hxHat']
  simp only [pullbackRadauTimeDerivativeData, Exp2.radauRhs, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [hend', hint]

lemma pullbackRadauTimeDerivativeCoefficientCoordinates_eq (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pullbackRadauTimeDerivativeCoefficientCoordinates K mesh solution j t =
      (Exp2.momentBasis K).equivFun
        (Exp2.radauCoefficient K (solution.utCellPullback mesh j t)) := by
  rw [pullbackRadauTimeDerivativeCoefficientCoordinates,
    pullbackRadauTimeDerivativeData_eq_dualCoordinates K mesh solution j t ht]
  simp [Exp2.radauCoordinateInverse, Exp2.radauCoefficient,
    Exp2.weightedMomentEquiv]

lemma localProjectionTimeDerivativeValue_eq_explicit (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (j : Fin N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (xHat : ℝ) :
    localProjectionTimeDerivativeValue K mesh solution t j
        (cellLeft mesh j + cellLength mesh j * xHat) =
      explicitLocalProjectionTimeDerivativeEval K mesh solution j t xHat := by
  have hcoord :
      (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
          cellLength mesh j = xHat := by
    rw [add_sub_cancel_left]
    exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
    simp [cellLength]
  have hend : solution.utCellPullback mesh j t 1 = solution.ut (cellRight mesh j) t := by
    rw [solution.utCellPullback_eq mesh j t ht 1 hone]
    simpa [mul_one] using congrArg (fun x ↦ solution.ut x t) hright.symm
  have hsum := (Exp2.momentBasis K).sum_equivFun
    (Exp2.radauCoefficient K (solution.utCellPullback mesh j t))
  have hsumEval :
      (∑ i, (Exp2.momentBasis K).equivFun
          (Exp2.radauCoefficient K (solution.utCellPullback mesh j t)) i *
          (Exp2.momentBasis K i).1.eval xHat) =
        (Exp2.radauCoefficient K (solution.utCellPullback mesh j t)).1.eval xHat := by
    let evalMap : Exp2.MomentPoly K →ₗ[ℝ] ℝ :=
      { toFun := fun r ↦ r.1.eval xHat
        map_add' := by intro r s; simp
        map_smul' := by intro c r; simp [Polynomial.eval_smul] }
    have h := congrArg evalMap hsum
    simpa only [map_sum, map_smul, evalMap, smul_eq_mul] using h
  simp only [localProjectionTimeDerivativeValue, hcoord,
    Exp2.gaussRadau_eq_radauCandidate, Exp2.radauCandidate,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X,
    explicitLocalProjectionTimeDerivativeEval]
  rw [pullbackRadauTimeDerivativeCoefficientCoordinates_eq K mesh solution j t ht]
  rw [hend]
  rw [hsumEval]

/-- The canonical projection is a genuinely differentiable curve in the finite-dimensional
DG space; this is derived from the exact solution rather than postulated. -/
def localProjectionTrajectoryRegularity (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T) :
    DGTrajectoryRegularity K mesh T
      (localProjectionValue K mesh solution)
      (localProjectionTimeDerivativeValue K mesh solution) where
  coefficient := fun t j ↦
    Polynomial.degreeLTEquiv ℝ (K + 1)
      (explicitLocalProjectionPolynomial K mesh solution j t)
  timeDerivativeCoefficient := fun t j ↦
    Polynomial.degreeLTEquiv ℝ (K + 1)
      (explicitLocalProjectionTimeDerivativePolynomial K mesh solution j t)
  value_eq := by
    intro t ht j x hx
    let xHat := (x - cellLeft mesh j) / cellLength mesh j
    have hxrepr : cellLeft mesh j + cellLength mesh j * xHat = x := by
      dsimp [xHat]
      field_simp [(cellLength_pos mesh j).ne']
      ring
    rw [← hxrepr, localProjectionValue_eq_explicit K mesh solution j t ht xHat,
      ← explicitLocalProjectionPolynomial_eval]
    have hcoord : cellLength mesh j * xHat / cellLength mesh j = xHat :=
      mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
    rw [add_sub_cancel_left, hcoord]
    simpa [xHat] using Polynomial.eval_eq_sum_degreeLTEquiv
      (explicitLocalProjectionPolynomial K mesh solution j t).2 xHat
  timeDerivativeValue_eq := by
    intro t ht j x hx
    let xHat := (x - cellLeft mesh j) / cellLength mesh j
    have hxrepr : cellLeft mesh j + cellLength mesh j * xHat = x := by
      dsimp [xHat]
      field_simp [(cellLength_pos mesh j).ne']
      ring
    rw [← hxrepr,
      localProjectionTimeDerivativeValue_eq_explicit K mesh solution j t ht xHat,
      ← explicitLocalProjectionTimeDerivativePolynomial_eval]
    have hcoord : cellLength mesh j * xHat / cellLength mesh j = xHat :=
      mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
    rw [add_sub_cancel_left, hcoord]
    simpa [xHat] using Polynomial.eval_eq_sum_degreeLTEquiv
      (explicitLocalProjectionTimeDerivativePolynomial K mesh solution j t).2 xHat
  coefficient_hasDerivWithinAt := by
    intro j i t ht
    exact explicitLocalProjectionPolynomial_coefficient_hasDerivWithinAt
      K mesh solution j i t ht

lemma localProjectionValue_spec (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IsLocalGaussRadauProjection K mesh (fun x ↦ solution.u x t)
      (localProjectionValue K mesh solution t) := by
  classical
  constructor
  · intro j
    refine ⟨Exp2.gaussRadau K (solution.uCellPullback mesh j t), ?_⟩
    intro x hx
    rfl
  · intro j
    constructor
    · intro q hq
      have hmoment := (Exp2.gaussRadau_spec K
        (solution.uCellPullback mesh j t)).1 q hq
      have hlen : cellLength mesh j ≠ 0 := (cellLength_pos mesh j).ne'
      have hcoord : ∀ xHat : ℝ,
          ((cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
            cellLength mesh j) = xHat := by
        intro xHat
        ring_nf
        field_simp
      have heq : (fun xHat ↦
          (solution.u (cellLeft mesh j + cellLength mesh j * xHat) t -
            localProjectionValue K mesh solution t j
              (cellLeft mesh j + cellLength mesh j * xHat)) * q.eval xHat) =ᵐ[
            volume.restrict Exp2.referenceCell]
          (fun xHat ↦ -(((Exp2.gaussRadau K
            (solution.uCellPullback mesh j t)).1.eval xHat -
              solution.uCellPullback mesh j t xHat) * q.eval xHat)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
        have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
        rw [solution.uCellPullback_eq mesh j t ht xHat hxHat']
        simp only [localProjectionValue, hcoord]
        ring
      rw [integral_congr_ae heq, integral_neg, hmoment, neg_zero]
    · have hend := (Exp2.gaussRadau_spec K
        (solution.uCellPullback mesh j t)).2
      have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
        simp [cellLength]
      have hlen : cellLength mesh j ≠ 0 := (cellLength_pos mesh j).ne'
      have hcoord : (cellRight mesh j - cellLeft mesh j) / cellLength mesh j = 1 := by
        rw [hright]
        ring_nf
        field_simp
      change (Exp2.gaussRadau K (solution.uCellPullback mesh j t)).1.eval
        ((cellRight mesh j - cellLeft mesh j) / cellLength mesh j) = _
      rw [hcoord, hend]
      have hright_mem : cellRight mesh j ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · rw [← mesh.left_boundary]
          exact mesh.nodes_strictMono.monotone (Fin.zero_le _)
        · rw [← mesh.right_boundary]
          exact mesh.nodes_strictMono.monotone (Fin.le_last _)
      have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      rw [solution.uCellPullback_eq mesh j t ht 1 hone]
      simpa [mul_one] using congrArg (fun x ↦ solution.u x t) hright.symm

lemma localProjectionTimeDerivativeValue_spec (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IsLocalGaussRadauProjection K mesh (fun x ↦ solution.ut x t)
      (localProjectionTimeDerivativeValue K mesh solution t) := by
  classical
  constructor
  · intro j
    refine ⟨Exp2.gaussRadau K (solution.utCellPullback mesh j t), ?_⟩
    intro x hx
    rfl
  · intro j
    constructor
    · intro q hq
      have hmoment := (Exp2.gaussRadau_spec K
        (solution.utCellPullback mesh j t)).1 q hq
      have hcoord : ∀ xHat : ℝ,
          ((cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
            cellLength mesh j) = xHat := by
        intro xHat
        ring_nf
        field_simp [(cellLength_pos mesh j).ne']
      have heq : (fun xHat ↦
          (solution.ut (cellLeft mesh j + cellLength mesh j * xHat) t -
            localProjectionTimeDerivativeValue K mesh solution t j
              (cellLeft mesh j + cellLength mesh j * xHat)) * q.eval xHat) =ᵐ[
            volume.restrict Exp2.referenceCell]
          (fun xHat ↦ -(((Exp2.gaussRadau K
            (solution.utCellPullback mesh j t)).1.eval xHat -
              solution.utCellPullback mesh j t xHat) * q.eval xHat)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
        have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
        rw [solution.utCellPullback_eq mesh j t ht xHat hxHat']
        simp only [localProjectionTimeDerivativeValue, hcoord]
        ring
      rw [integral_congr_ae heq, integral_neg, hmoment, neg_zero]
    · have hend := (Exp2.gaussRadau_spec K
        (solution.utCellPullback mesh j t)).2
      have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
        simp [cellLength]
      have hcoord : (cellRight mesh j - cellLeft mesh j) / cellLength mesh j = 1 := by
        rw [hright]
        ring_nf
        field_simp [(cellLength_pos mesh j).ne']
      change (Exp2.gaussRadau K (solution.utCellPullback mesh j t)).1.eval
        ((cellRight mesh j - cellLeft mesh j) / cellLength mesh j) = _
      rw [hcoord, hend]
      have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      rw [solution.utCellPullback_eq mesh j t ht 1 hone]
      simpa [mul_one] using congrArg (fun x ↦ solution.ut x t) hright.symm

/-- The local endpoint and moment conditions determine the cell polynomial uniquely. -/
lemma localProjection_unique (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (p : DGField N)
    (hp : IsLocalGaussRadauProjection K mesh (fun x ↦ solution.u x t) p) :
    ∀ j : Fin N, ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
      p j x = localProjectionValue K mesh solution t j x := by
  classical
  intro j x hx
  obtain ⟨r, hr⟩ := hp.1 j
  have hrspec : Exp2.IsGaussRadauAt K (solution.uCellPullback mesh j t) r := by
    constructor
    · intro q hq
      have hmoment := (hp.2 j).1 q hq
      have heq : (fun xHat ↦
          (r.1.eval xHat - solution.uCellPullback mesh j t xHat) * q.eval xHat) =ᵐ[
            volume.restrict Exp2.referenceCell]
          (fun xHat ↦ -((solution.u
              (cellLeft mesh j + cellLength mesh j * xHat) t -
            p j (cellLeft mesh j + cellLength mesh j * xHat)) * q.eval xHat)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
        have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
        have hxphys : cellLeft mesh j + cellLength mesh j * xHat ∈
            Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
          constructor
          · nlinarith [cellLength_pos mesh j, hxHat'.1]
          · have hright : cellRight mesh j =
                cellLeft mesh j + cellLength mesh j := by simp [cellLength]
            rw [hright]
            nlinarith [cellLength_pos mesh j, hxHat'.2]
        rw [solution.uCellPullback_eq mesh j t ht xHat hxHat',
          hr _ hxphys]
        have hcoord :
            (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
                cellLength mesh j = xHat := by
          rw [add_sub_cancel_left]
          exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
        rw [hcoord]
        ring
      rw [integral_congr_ae heq, integral_neg, hmoment, neg_zero]
    · have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
        simp [cellLength]
      have hcoord :
          (cellRight mesh j - cellLeft mesh j) / cellLength mesh j = 1 := by
        rw [hright, add_sub_cancel_left]
        exact div_self (cellLength_pos mesh j).ne'
      have hrepr := hr (cellRight mesh j) ⟨hx.1.trans hx.2, le_rfl⟩
      rw [hcoord] at hrepr
      rw [← hrepr, (hp.2 j).2]
      have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      rw [solution.uCellPullback_eq mesh j t ht 1 hone]
      simpa [mul_one] using congrArg (fun y ↦ solution.u y t) hright
  have hpoly := Exp2.gaussRadauAt_unique K (solution.uCellPullback mesh j t)
    (Exp2.gaussRadau_spec K (solution.uCellPullback mesh j t)) hrspec
  rw [hr x hx]
  simp only [localProjectionValue]
  rw [hpoly]

/-- A polynomial in the affine cell coordinate belongs to every finite `Lᵖ` on the bounded
cell. -/
lemma physicalPolynomial_memLp (p : Polynomial ℝ) {l h : ℝ} (hh : 0 < h) :
    MemLp (fun x ↦ p.eval ((x - l) / h)) 2
      (volume.restrict (Exp2.cell l h : Set ℝ)) := by
  let f : ℝ → ℝ := fun x ↦ p.eval ((x - l) / h)
  have hfcont : Continuous f :=
    (Exp2.polynomial_eval_continuous p).comp
      ((continuous_id.sub continuous_const).div_const h)
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioo l (l + h))) := hfcont.aestronglyMeasurable
  have hscale := Exp2AffineMeasure.eLpNorm_comp_affine_restrict_Ioo
    (p := (2 : ℝ≥0∞)) f hh hfmeas
  have hcomp : (fun x : ℝ ↦ f (l + h * x)) = fun x ↦ p.eval x := by
    funext x
    dsimp [f]
    have hcoord : (l + h * x - l) / h = x := by
      rw [add_sub_cancel_left]
      exact mul_div_cancel_left₀ x hh.ne'
    rw [hcoord]
  rw [hcomp] at hscale
  have href := Exp2.polynomial_eval_memLp_reference p
  have hprod :
      (ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (volume.restrict (Set.Ioo l (l + h))) < ∞ := by
    calc
      _ = eLpNorm (fun x ↦ p.eval x) 2
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
            simpa [smul_eq_mul] using hscale.symm
      _ < ∞ := by simpa [Exp2.referenceCell, Exp2.cell] using href.2
  have hcoef : (ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ 0 := by
    intro hz
    rcases ENNReal.rpow_eq_zero_iff.mp hz with hzero | htop
    · exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hh)).ne' hzero.1
    · exact (ENNReal.ofReal_ne_top).elim htop.1
  have hnorm : eLpNorm f 2 (volume.restrict (Set.Ioo l (l + h))) < ∞ := by
    rcases ENNReal.mul_lt_top_iff.mp hprod with hfinite | hzero | hzero
    · exact hfinite.2
    · exact (hcoef hzero).elim
    · rw [hzero]
      exact ENNReal.zero_lt_top
  exact ⟨by simpa [Exp2.cell] using hfmeas, by simpa [f, Exp2.cell] using hnorm⟩

lemma projectionValue_memLp (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (projection : ProjectionTrajectory K mesh T solution)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : Fin N) :
    MemLp (projection.value t j) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
  have hunique := localProjection_unique K mesh solution t ht
    (projection.value t) (projection.value_spec t ht)
  have heq : projection.value t j =ᵐ[volume.restrict (meshCell mesh j : Set ℝ)]
      Exp2.physicalProjection K (cellLength_pos mesh j) (solution.uCell mesh j t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
      exact ⟨hx.1.le, by simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
    rw [hunique j x hx']
    rfl
  have hbase := physicalPolynomial_memLp
    (l := cellLeft mesh j)
    (Exp2.gaussRadau K (Exp2.affinePullback (cellLength_pos mesh j)
      (solution.uCell mesh j t))).1 (cellLength_pos mesh j)
  refine ⟨hbase.1.congr heq.symm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact hbase.2

lemma solutionValue_memLp (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : Fin N) :
    MemLp (fun x ↦ solution.u x t) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
  have heq : (fun x ↦ solution.u x t) =ᵐ[
      volume.restrict (meshCell mesh j : Set ℝ)] solution.uCell mesh j t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
      exact ⟨hx.1.le, by simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
    exact (solution.uCell_eq mesh j t ht x hx').symm
  have hbase := (solution.uCell mesh j t).toFun_memLp
  refine ⟨hbase.1.congr heq.symm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact hbase.2

lemma localProjectionTimeDerivative_unique (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (p : DGField N)
    (hp : IsLocalGaussRadauProjection K mesh (fun x ↦ solution.ut x t) p) :
    ∀ j : Fin N, ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
      p j x = localProjectionTimeDerivativeValue K mesh solution t j x := by
  classical
  intro j x hx
  obtain ⟨r, hr⟩ := hp.1 j
  have hrspec : Exp2.IsGaussRadauAt K (solution.utCellPullback mesh j t) r := by
    constructor
    · intro q hq
      have hmoment := (hp.2 j).1 q hq
      have heq : (fun xHat ↦
          (r.1.eval xHat - solution.utCellPullback mesh j t xHat) * q.eval xHat) =ᵐ[
            volume.restrict Exp2.referenceCell]
          (fun xHat ↦ -((solution.ut
              (cellLeft mesh j + cellLength mesh j * xHat) t -
            p j (cellLeft mesh j + cellLength mesh j * xHat)) * q.eval xHat)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
        have hxHat' : xHat ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hxHat.1.le, by simpa using hxHat.2.le⟩
        have hxphys : cellLeft mesh j + cellLength mesh j * xHat ∈
            Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
          constructor
          · nlinarith [cellLength_pos mesh j, hxHat'.1]
          · have hright : cellRight mesh j =
                cellLeft mesh j + cellLength mesh j := by simp [cellLength]
            rw [hright]
            nlinarith [cellLength_pos mesh j, hxHat'.2]
        rw [solution.utCellPullback_eq mesh j t ht xHat hxHat', hr _ hxphys]
        have hcoord :
            (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
                cellLength mesh j = xHat := by
          rw [add_sub_cancel_left]
          exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
        rw [hcoord]
        ring
      rw [integral_congr_ae heq, integral_neg, hmoment, neg_zero]
    · have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
        simp [cellLength]
      have hcoord :
          (cellRight mesh j - cellLeft mesh j) / cellLength mesh j = 1 := by
        rw [hright, add_sub_cancel_left]
        exact div_self (cellLength_pos mesh j).ne'
      have hrepr := hr (cellRight mesh j) ⟨hx.1.trans hx.2, le_rfl⟩
      rw [hcoord] at hrepr
      rw [← hrepr, (hp.2 j).2]
      have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      rw [solution.utCellPullback_eq mesh j t ht 1 hone]
      simpa [mul_one] using congrArg (fun y ↦ solution.ut y t) hright
  have hpoly := Exp2.gaussRadauAt_unique K (solution.utCellPullback mesh j t)
    (Exp2.gaussRadau_spec K (solution.utCellPullback mesh j t)) hrspec
  rw [hr x hx]
  simp only [localProjectionTimeDerivativeValue]
  rw [hpoly]

/-- Every trajectory satisfying the two Radau characterizations inherits the canonical
finite-dimensional regularity. -/
def ProjectionTrajectory.regularity (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (projection : ProjectionTrajectory K mesh T solution) :
    DGTrajectoryRegularity K mesh T projection.value projection.timeDerivativeValue := by
  let canonical := localProjectionTrajectoryRegularity K mesh solution
  refine {
    coefficient := canonical.coefficient
    timeDerivativeCoefficient := canonical.timeDerivativeCoefficient
    value_eq := ?_
    timeDerivativeValue_eq := ?_
    coefficient_hasDerivWithinAt := canonical.coefficient_hasDerivWithinAt }
  · intro t ht j x hx
    rw [localProjection_unique K mesh solution t ht
      (projection.value t) (projection.value_spec t ht) j x hx]
    exact canonical.value_eq t ht j x hx
  · intro t ht j x hx
    rw [localProjectionTimeDerivative_unique K mesh solution t ht
      (projection.timeDerivativeValue t) (projection.timeDerivative_spec t ht) j x hx]
    exact canonical.timeDerivativeValue_eq t ht j x hx

lemma projectionTimeDerivativeValue_memLp (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (projection : ProjectionTrajectory K mesh T solution)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : Fin N) :
    MemLp (projection.timeDerivativeValue t j) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
  have hunique := localProjectionTimeDerivative_unique K mesh solution t ht
    (projection.timeDerivativeValue t) (projection.timeDerivative_spec t ht)
  have heq : projection.timeDerivativeValue t j =ᵐ[
      volume.restrict (meshCell mesh j : Set ℝ)]
      Exp2.physicalProjection K (cellLength_pos mesh j) (solution.utCell mesh j t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
      exact ⟨hx.1.le, by simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
    rw [hunique j x hx']
    rfl
  have hbase := physicalPolynomial_memLp
    (l := cellLeft mesh j)
    (Exp2.gaussRadau K (Exp2.affinePullback (cellLength_pos mesh j)
      (solution.utCell mesh j t))).1 (cellLength_pos mesh j)
  refine ⟨hbase.1.congr heq.symm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact hbase.2

lemma solutionTimeDerivativeValue_memLp (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ}
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : Fin N) :
    MemLp (fun x ↦ solution.ut x t) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
  have heq : (fun x ↦ solution.ut x t) =ᵐ[
      volume.restrict (meshCell mesh j : Set ℝ)] solution.utCell mesh j t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
      exact ⟨hx.1.le, by simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
    exact (solution.utCell_eq mesh j t ht x hx').symm
  have hbase := (solution.utCell mesh j t).toFun_memLp
  refine ⟨hbase.1.congr heq.symm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact hbase.2

/-- Smoothness gives a time-dependent local Gauss--Radau projection. -/
theorem projectionTrajectory_exists (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T) :
    Nonempty (ProjectionTrajectory K mesh T solution) := by
  refine ⟨{
    value := localProjectionValue K mesh solution
    timeDerivativeValue := localProjectionTimeDerivativeValue K mesh solution
    value_spec := localProjectionValue_spec K mesh solution
    timeDerivative_spec := localProjectionTimeDerivativeValue_spec K mesh solution
    commutes_with_time_derivative := ?_ }⟩
  intro j x hx t ht
  let xHat := (x - cellLeft mesh j) / cellLength mesh j
  have hxrepr : cellLeft mesh j + cellLength mesh j * xHat = x := by
    dsimp [xHat]
    field_simp [(cellLength_pos mesh j).ne']
    ring
  have hraw := explicitLocalProjectionEval_hasDerivWithinAt
    K mesh solution j t ht xHat
  have hcomm : HasDerivWithinAt
      (fun s ↦ localProjectionValue K mesh solution s j x)
      (explicitLocalProjectionTimeDerivativeEval K mesh solution j t xHat)
      (Set.Icc (0 : ℝ) T) t := by
    apply hraw.congr
    · intro s hs
      rw [← localProjectionValue_eq_explicit K mesh solution j s hs xHat,
        hxrepr]
    · rw [← localProjectionValue_eq_explicit K mesh solution j t ht xHat,
        hxrepr]
  have hdt := localProjectionTimeDerivativeValue_eq_explicit
    K mesh solution j t ht xHat
  rw [hxrepr] at hdt
  rw [hdt]
  exact hcomm

/-- Equations (6)--(7): on mesh families with one fixed quasi-uniformity ratio, the local
Gauss--Radau projection has order `K+1`, with a constant independent of the mesh size. -/
theorem gaussRadau_projection_error_bound (K : ℕ) {a T ρ : ℝ}
    (hT : 0 < T) (_hρ : 1 ≤ ρ)
    (solution : SmoothPeriodicAdvectionSolution K a T) :
    ∃ Cη : ℝ, 0 ≤ Cη ∧
      ∀ {N : ℕ} (mesh : PeriodicMesh N), IsQuasiUniform ρ mesh →
      ∀ projection : ProjectionTrajectory K mesh T solution,
        brokenL2Norm mesh
          (fun j x ↦ solution.u x T - projection.value T j x) ≤
            Cη * mesh.meshSize ^ (K + 1) := by
  obtain ⟨C, hC, href, hphysical⟩ := Exp2.main_theorem K
  obtain ⟨M, hM, hregular⟩ := solution.uniformRegularity
  refine ⟨C * M, mul_nonneg hC hM, ?_⟩
  intro N mesh hmesh projection
  have hTmem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hproj := projection.value_spec T hTmem
  have hunique := localProjection_unique K mesh solution T hTmem
    (projection.value T) hproj
  let A : ℝ := C * mesh.meshSize ^ (K + 1)
  have hA : 0 ≤ A := mul_nonneg hC (pow_nonneg mesh.meshSize_pos.le _)
  have hcell : ∀ j : Fin N,
      Exp2.l2NormOn (meshCell mesh j)
          (fun x ↦ solution.u x T - projection.value T j x) ≤
        A * Exp2.sobolevSeminorm (solution.uCell mesh j T) := by
    intro j
    have hlocal := hphysical (cellLength_pos mesh j) (solution.uCell mesh j T)
    have heq :
        (fun x ↦ solution.u x T - projection.value T j x) =ᵐ[
            volume.restrict (meshCell mesh j : Set ℝ)]
          -(fun x ↦ Exp2.physicalProjection K (cellLength_pos mesh j)
                (solution.uCell mesh j T) x - solution.uCell mesh j T x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx' : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
        exact ⟨hx.1.le, by
          simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
      rw [← solution.uCell_eq mesh j T hTmem x hx', hunique j x hx']
      change (solution.uCell mesh j T) x -
          (Exp2.gaussRadau K (Exp2.affinePullback (cellLength_pos mesh j)
            (solution.uCell mesh j T))).1.eval
              ((x - cellLeft mesh j) / cellLength mesh j) =
        -((Exp2.gaussRadau K (Exp2.affinePullback (cellLength_pos mesh j)
            (solution.uCell mesh j T))).1.eval
              ((x - cellLeft mesh j) / cellLength mesh j) -
          (solution.uCell mesh j T) x)
      ring
    have hnormeq :
        Exp2.l2NormOn (meshCell mesh j)
            (fun x ↦ solution.u x T - projection.value T j x) =
          Exp2.l2NormOn (meshCell mesh j)
            (fun x ↦ Exp2.physicalProjection K (cellLength_pos mesh j)
                (solution.uCell mesh j T) x - solution.uCell mesh j T x) := by
      unfold Exp2.l2NormOn
      rw [eLpNorm_congr_ae heq]
      simpa only using congrArg ENNReal.toReal
        (eLpNorm_neg (fun x ↦ Exp2.physicalProjection K (cellLength_pos mesh j)
          (solution.uCell mesh j T) x - solution.uCell mesh j T x) 2
          (volume.restrict (meshCell mesh j : Set ℝ)))
    rw [hnormeq]
    calc
      Exp2.l2NormOn (meshCell mesh j)
          (fun x ↦ Exp2.physicalProjection K (cellLength_pos mesh j)
              (solution.uCell mesh j T) x - solution.uCell mesh j T x) ≤
          C * cellLength mesh j ^ (K + 1) *
            Exp2.sobolevSeminorm (solution.uCell mesh j T) := hlocal
      _ ≤ C * mesh.meshSize ^ (K + 1) *
            Exp2.sobolevSeminorm (solution.uCell mesh j T) := by
        have hpow : cellLength mesh j ^ (K + 1) ≤
            mesh.meshSize ^ (K + 1) := by
          apply pow_le_pow_left₀ (cellLength_pos mesh j).le
          · simpa [cellLength] using mesh.cellLength_le_meshSize j
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC)
          (Exp2.l2NormOn_nonneg _ _)
      _ = A * Exp2.sobolevSeminorm (solution.uCell mesh j T) := by rfl
  have hsum :
      (∑ j : Fin N, (Exp2.l2NormOn (meshCell mesh j)
          (fun x ↦ solution.u x T - projection.value T j x)) ^ 2) ≤
        A ^ 2 * ∑ j : Fin N,
          (Exp2.sobolevSeminorm (solution.uCell mesh j T)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he := Exp2.l2NormOn_nonneg (meshCell mesh j)
      (fun x ↦ solution.u x T - projection.value T j x)
    have hs : 0 ≤ Exp2.sobolevSeminorm (solution.uCell mesh j T) :=
      Exp2.l2NormOn_nonneg _ _
    nlinarith [hcell j]
  have hseminorm := (hregular mesh T hTmem).1
  unfold brokenL2Norm
  calc
    Real.sqrt (∑ j : Fin N, (Exp2.l2NormOn (meshCell mesh j)
        (fun x ↦ solution.u x T - projection.value T j x)) ^ 2) ≤
        Real.sqrt (A ^ 2 * ∑ j : Fin N,
          (Exp2.sobolevSeminorm (solution.uCell mesh j T)) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = A * Real.sqrt (∑ j : Fin N,
          (Exp2.sobolevSeminorm (solution.uCell mesh j T)) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq_eq_abs, abs_of_nonneg hA]
    _ ≤ A * M := mul_le_mul_of_nonneg_left hseminorm hA
    _ = (C * M) * mesh.meshSize ^ (K + 1) := by
      dsimp [A]
      ring

/-- Uniform-in-time version of (7) for the projection of `u_t`. -/
theorem gaussRadau_timeDerivative_error_bound (K : ℕ) {a T ρ : ℝ}
    (_hρ : 1 ≤ ρ) (solution : SmoothPeriodicAdvectionSolution K a T) :
    ∃ Cηt : ℝ, 0 ≤ Cηt ∧
      ∀ {N : ℕ} (mesh : PeriodicMesh N), IsQuasiUniform ρ mesh →
      ∀ projection : ProjectionTrajectory K mesh T solution,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        brokenL2Norm mesh
          (fun j x ↦ solution.ut x t - projection.timeDerivativeValue t j x) ≤
            Cηt * mesh.meshSize ^ (K + 1) := by
  obtain ⟨C, hC, href, hphysical⟩ := Exp2.main_theorem K
  obtain ⟨M, hM, hregular⟩ := solution.uniformRegularity
  refine ⟨C * M, mul_nonneg hC hM, ?_⟩
  intro N mesh hmesh projection t ht
  have hunique := localProjectionTimeDerivative_unique K mesh solution t ht
    (projection.timeDerivativeValue t) (projection.timeDerivative_spec t ht)
  let A : ℝ := C * mesh.meshSize ^ (K + 1)
  have hA : 0 ≤ A := mul_nonneg hC (pow_nonneg mesh.meshSize_pos.le _)
  have hcell : ∀ j : Fin N,
      Exp2.l2NormOn (meshCell mesh j)
          (fun x ↦ solution.ut x t - projection.timeDerivativeValue t j x) ≤
        A * Exp2.sobolevSeminorm (solution.utCell mesh j t) := by
    intro j
    have hlocal := hphysical (cellLength_pos mesh j) (solution.utCell mesh j t)
    have heq :
        (fun x ↦ solution.ut x t - projection.timeDerivativeValue t j x) =ᵐ[
            volume.restrict (meshCell mesh j : Set ℝ)]
          -(fun x ↦ Exp2.physicalProjection K (cellLength_pos mesh j)
                (solution.utCell mesh j t) x - solution.utCell mesh j t x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx' : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j) := by
        exact ⟨hx.1.le, by
          simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
      rw [← solution.utCell_eq mesh j t ht x hx', hunique j x hx']
      change (solution.utCell mesh j t) x -
          (Exp2.gaussRadau K (Exp2.affinePullback (cellLength_pos mesh j)
            (solution.utCell mesh j t))).1.eval
              ((x - cellLeft mesh j) / cellLength mesh j) =
        -((Exp2.gaussRadau K (Exp2.affinePullback (cellLength_pos mesh j)
            (solution.utCell mesh j t))).1.eval
              ((x - cellLeft mesh j) / cellLength mesh j) -
          (solution.utCell mesh j t) x)
      ring
    have hnormeq :
        Exp2.l2NormOn (meshCell mesh j)
            (fun x ↦ solution.ut x t - projection.timeDerivativeValue t j x) =
          Exp2.l2NormOn (meshCell mesh j)
            (fun x ↦ Exp2.physicalProjection K (cellLength_pos mesh j)
                (solution.utCell mesh j t) x - solution.utCell mesh j t x) := by
      unfold Exp2.l2NormOn
      rw [eLpNorm_congr_ae heq]
      simpa only using congrArg ENNReal.toReal
        (eLpNorm_neg (fun x ↦ Exp2.physicalProjection K (cellLength_pos mesh j)
          (solution.utCell mesh j t) x - solution.utCell mesh j t x) 2
          (volume.restrict (meshCell mesh j : Set ℝ)))
    rw [hnormeq]
    calc
      _ ≤ C * cellLength mesh j ^ (K + 1) *
            Exp2.sobolevSeminorm (solution.utCell mesh j t) := hlocal
      _ ≤ C * mesh.meshSize ^ (K + 1) *
            Exp2.sobolevSeminorm (solution.utCell mesh j t) := by
        have hpow : cellLength mesh j ^ (K + 1) ≤
            mesh.meshSize ^ (K + 1) := by
          apply pow_le_pow_left₀ (cellLength_pos mesh j).le
          simpa [cellLength] using mesh.cellLength_le_meshSize j
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC)
          (Exp2.l2NormOn_nonneg _ _)
      _ = A * Exp2.sobolevSeminorm (solution.utCell mesh j t) := by rfl
  have hsum :
      (∑ j : Fin N, (Exp2.l2NormOn (meshCell mesh j)
          (fun x ↦ solution.ut x t - projection.timeDerivativeValue t j x)) ^ 2) ≤
        A ^ 2 * ∑ j : Fin N,
          (Exp2.sobolevSeminorm (solution.utCell mesh j t)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he := Exp2.l2NormOn_nonneg (meshCell mesh j)
      (fun x ↦ solution.ut x t - projection.timeDerivativeValue t j x)
    have hs : 0 ≤ Exp2.sobolevSeminorm (solution.utCell mesh j t) :=
      Exp2.l2NormOn_nonneg _ _
    nlinarith [hcell j]
  have hseminorm := (hregular mesh t ht).2
  unfold brokenL2Norm
  calc
    Real.sqrt (∑ j : Fin N, (Exp2.l2NormOn (meshCell mesh j)
        (fun x ↦ solution.ut x t - projection.timeDerivativeValue t j x)) ^ 2) ≤
        Real.sqrt (A ^ 2 * ∑ j : Fin N,
          (Exp2.sobolevSeminorm (solution.utCell mesh j t)) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = A * Real.sqrt (∑ j : Fin N,
          (Exp2.sobolevSeminorm (solution.utCell mesh j t)) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq_eq_abs, abs_of_nonneg hA]
    _ ≤ A * M := mul_le_mul_of_nonneg_left hseminorm hA
    _ = (C * M) * mesh.meshSize ^ (K + 1) := by
      dsimp [A]
      ring

end Exp1
