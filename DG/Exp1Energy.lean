import Exp1Differentiation

open scoped ENNReal MeasureTheory Topology Interval BigOperators
open MeasureTheory Set Filter

noncomputable section
namespace Exp1

lemma isDGField_sub {K N : ℕ} (mesh : PeriodicMesh N) {v w : DGField N}
    (hv : IsDGField K mesh v) (hw : IsDGField K mesh w) :
    IsDGField K mesh (fun j x ↦ v j x - w j x) := by
  intro j
  obtain ⟨p, hp⟩ := hv j
  obtain ⟨q, hq⟩ := hw j
  refine ⟨p - q, ?_⟩
  intro x hx
  change v j x - w j x = _
  rw [hp x hx, hq x hx]
  simp

lemma integral_polynomial_mul_derivative (p : Polynomial ℝ) :
    (∫ x in Set.Ioo (0 : ℝ) 1, p.eval x * p.derivative.eval x) =
      (p.eval 1) ^ 2 / 2 - (p.eval 0) ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x ↦ (p.eval x) ^ 2 / 2
  have hf : ∀ x : ℝ, HasDerivAt f (p.eval x * p.derivative.eval x) x := by
    intro x
    have h := ((p.hasDerivAt x).mul (p.hasDerivAt x)).const_mul (1 / 2)
    convert h using 1 <;> simp [f, pow_two] <;> ring
  have hderiv : deriv f = fun x ↦ p.eval x * p.derivative.eval x := by
    funext x
    exact (hf x).deriv
  have hint : IntervalIntegrable (deriv f) volume 0 1 := by
    rw [hderiv]
    exact ((Exp2.polynomial_eval_continuous p).mul
      (Exp2.polynomial_eval_continuous p.derivative)).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_deriv_eq_sub
    (fun x hx ↦ (hf x).differentiableAt) hint
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo, hderiv] at hftc
  simpa [f] using hftc

lemma dgField_deriv_eq {K N : ℕ} (mesh : PeriodicMesh N) (v : DGField N)
    (j : Fin N) (p : Exp2.PolyLE K)
    (hp : ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
      v j x = p.1.eval ((x - cellLeft mesh j) / cellLength mesh j))
    {x : ℝ} (hx : x ∈ Set.Ioo (cellLeft mesh j) (cellRight mesh j)) :
    deriv (v j) x =
      p.1.derivative.eval ((x - cellLeft mesh j) / cellLength mesh j) /
        cellLength mesh j := by
  have hcoord : HasDerivAt
      (fun y ↦ (y - cellLeft mesh j) / cellLength mesh j)
      (1 / cellLength mesh j) x := by
    convert ((hasDerivAt_id x).sub_const (cellLeft mesh j)).div_const
      (cellLength mesh j) using 1 <;> simp
  have hpoly := (p.1.hasDerivAt
    ((x - cellLeft mesh j) / cellLength mesh j)).comp x hcoord
  have heq : v j =ᶠ[nhds x]
      (fun y ↦ p.1.eval ((y - cellLeft mesh j) / cellLength mesh j)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hp y ⟨hy.1.le, hy.2.le⟩
  have h := hpoly.congr_of_eventuallyEq heq
  rw [h.deriv]
  ring

lemma dgField_memLp {K N : ℕ} (mesh : PeriodicMesh N) (v : DGField N)
    (hv : IsDGField K mesh v) (j : Fin N) :
    MemLp (v j) 2 (volume.restrict (meshCell mesh j : Set ℝ)) := by
  obtain ⟨p, hp⟩ := hv j
  have hpoly := physicalPolynomial_memLp (l := cellLeft mesh j)
    p.1 (cellLength_pos mesh j)
  have heq : v j =ᵐ[volume.restrict (meshCell mesh j : Set ℝ)]
      (fun x ↦ p.1.eval ((x - cellLeft mesh j) / cellLength mesh j)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    apply hp x
    exact ⟨hx.1.le, by simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
  refine ⟨hpoly.1.congr heq.symm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact hpoly.2

lemma dgField_deriv_memLp {K N : ℕ} (mesh : PeriodicMesh N) (v : DGField N)
    (hv : IsDGField K mesh v) (j : Fin N) :
    MemLp (deriv (v j)) 2 (volume.restrict (meshCell mesh j : Set ℝ)) := by
  obtain ⟨p, hp⟩ := hv j
  have hpoly0 := physicalPolynomial_memLp (l := cellLeft mesh j)
    p.1.derivative (cellLength_pos mesh j)
  have hpoly := hpoly0.const_smul ((cellLength mesh j)⁻¹)
  have heq : deriv (v j) =ᵐ[volume.restrict (meshCell mesh j : Set ℝ)]
      (fun x ↦ (cellLength mesh j)⁻¹ *
        p.1.derivative.eval ((x - cellLeft mesh j) / cellLength mesh j)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Set.Ioo (cellLeft mesh j) (cellRight mesh j) :=
      ⟨hx.1, by simpa [meshCell, Exp2.cell, cellLength] using hx.2⟩
    rw [dgField_deriv_eq mesh v j p hp hx']
    ring
  refine ⟨hpoly.1.congr heq.symm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  simpa [Pi.smul_apply, smul_eq_mul] using hpoly.2

lemma solutionSpaceDerivativeValue_memLp (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ} (ha : 0 < a)
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (j : Fin N) :
    MemLp (fun x ↦ solution.ux x t) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
  have hbase := (solutionTimeDerivativeValue_memLp K mesh solution t ht j).const_smul
    (-a⁻¹)
  have heq : (fun x ↦ solution.ux x t) =ᵐ[
      volume.restrict (meshCell mesh j : Set ℝ)]
      (fun x ↦ (-a⁻¹) * solution.ut x t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxunit : x ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact (cellLeft_mem_unit mesh j).1.trans_lt hx.1
      · have hxright : x < cellRight mesh j := by
          simpa [meshCell, Exp2.cell, cellLength] using hx.2
        exact hxright.trans_le (cellRight_mem_unit mesh j).2
    have hpde := solution.advectionEquation x hxunit t ht
    field_simp [ha.ne'] at hpde ⊢
    linarith
  have hbase' : MemLp (fun x ↦ (-a⁻¹) * solution.ut x t) 2
      (volume.restrict (meshCell mesh j : Set ℝ)) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase
  refine ⟨hbase'.1.congr heq.symm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  exact hbase'.2

lemma exact_product_integral_eq_boundary {K N : ℕ}
    (mesh : PeriodicMesh N) {a T : ℝ} (ha : 0 < a)
    (solution : SmoothPeriodicAdvectionSolution K a T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (φ : DGField N) (hφ : IsDGField K mesh φ) (j : Fin N) :
    (∫ x, (solution.ux x t * φ j x +
        solution.u x t * deriv (φ j) x)
      ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      solution.u (cellRight mesh j) t * φ j (cellRight mesh j) -
        solution.u (cellLeft mesh j) t * φ j (cellLeft mesh j) := by
  obtain ⟨p, hp⟩ := hφ j
  let F : ℝ → ℝ := fun x ↦ solution.u x t * φ j x
  have hFderiv : ∀ x ∈ Set.Ioo (cellLeft mesh j) (cellRight mesh j),
      HasDerivAt F
        (solution.ux x t * φ j x + solution.u x t * deriv (φ j) x) x := by
    intro x hx
    have hxunit : x ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨(cellLeft_mem_unit mesh j).1.trans_lt hx.1,
        hx.2.trans_le (cellRight_mem_unit mesh j).2⟩
    have hu := solution.spaceDerivative t ht x hxunit
    have hcoord : HasDerivAt
        (fun y ↦ (y - cellLeft mesh j) / cellLength mesh j)
        (1 / cellLength mesh j) x := by
      convert ((hasDerivAt_id x).sub_const (cellLeft mesh j)).div_const
        (cellLength mesh j) using 1 <;> simp
    have hpoly := (p.1.hasDerivAt
      ((x - cellLeft mesh j) / cellLength mesh j)).comp x hcoord
    have heq : Filter.EventuallyEq (nhds x) (φ j)
        (fun y ↦ p.1.eval ((y - cellLeft mesh j) / cellLength mesh j)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hp y ⟨hy.1.le, hy.2.le⟩
    have hφderiv := hpoly.congr_of_eventuallyEq heq
    have hactual := dgField_deriv_eq mesh φ j p hp hx
    have hφactual : HasDerivAt (φ j) (deriv (φ j) x) x := by
      rw [hactual]
      convert hφderiv using 1 <;> ring
    exact hu.mul hφactual
  have htargetInt : Integrable
      (fun x ↦ solution.ux x t * φ j x +
        solution.u x t * deriv (φ j) x)
      (volume.restrict (meshCell mesh j : Set ℝ)) :=
    ((solutionSpaceDerivativeValue_memLp K mesh ha solution t ht j).integrable_mul
      (dgField_memLp mesh φ hφ j)).add
    ((solutionValue_memLp K mesh solution t ht j).integrable_mul
      (dgField_deriv_memLp mesh φ hφ j))
  have hderivAE : deriv F =ᵐ[volume.restrict (meshCell mesh j : Set ℝ)]
      (fun x ↦ solution.ux x t * φ j x +
        solution.u x t * deriv (φ j) x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Set.Ioo (cellLeft mesh j) (cellRight mesh j) := by
      exact ⟨hx.1, by simpa [meshCell, Exp2.cell, cellLength] using hx.2⟩
    exact (hFderiv x hx').deriv
  have hderivInt : Integrable (deriv F)
      (volume.restrict (meshCell mesh j : Set ℝ)) :=
    htargetInt.congr hderivAE.symm
  have hle : cellLeft mesh j ≤ cellRight mesh j :=
    sub_nonneg.mp (cellLength_pos mesh j).le
  have hint : IntervalIntegrable (deriv F) volume
      (cellLeft mesh j) (cellRight mesh j) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle,
      integrableOn_Icc_iff_integrableOn_Ioo]
    simpa [meshCell, Exp2.cell, cellLength] using hderivInt
  have hucont : Continuous (fun x ↦ solution.u x t) := by
    simpa [Function.uncurry] using solution.u_joint_continuous.comp
      (continuous_id.prodMk continuous_const)
  have hcoordcont : Continuous
      (fun x ↦ (x - cellLeft mesh j) / cellLength mesh j) :=
    (continuous_id.sub continuous_const).div_const _
  have hpolycont : Continuous
      (fun x ↦ p.1.eval ((x - cellLeft mesh j) / cellLength mesh j)) :=
    (Exp2.polynomial_eval_continuous p.1).comp hcoordcont
  have hφcont : ContinuousOn (φ j)
      (Set.Icc (cellLeft mesh j) (cellRight mesh j)) :=
    hpolycont.continuousOn.congr (fun x hx ↦ hp x hx)
  have hFcont : ContinuousOn F
      (Set.Icc (cellLeft mesh j) (cellRight mesh j)) := by
    simpa [F] using hucont.continuousOn.mul hφcont
  have hftc := intervalIntegral.integral_deriv_eq_sub_uIoo
    (by simpa [uIcc_of_le hle] using hFcont)
    (fun x hx ↦ (hFderiv x (by simpa [uIoo_of_le hle] using hx)).differentiableAt)
    hint
  rw [intervalIntegral.integral_of_le hle,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at hftc
  calc
    _ = ∫ x, deriv F x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)) :=
      (integral_congr_ae hderivAE).symm
    _ = _ := by simpa [meshCell, Exp2.cell, cellLength, F] using hftc

lemma dgField_integral_mul_deriv {K N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N) (hv : IsDGField K mesh v) (j : Fin N) :
    (∫ x, v j x * deriv (v j) x
      ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      (v j (cellRight mesh j)) ^ 2 / 2 -
        (v j (cellLeft mesh j)) ^ 2 / 2 := by
  obtain ⟨p, hp⟩ := hv j
  let g : ℝ → ℝ := fun x ↦ v j x * deriv (v j) x
  have hscale := Exp2AffineMeasure.setIntegral_comp_affine_Ioo
    (a := cellLeft mesh j) g (cellLength_pos mesh j)
  have href :
      (∫ xHat in Set.Ioo (0 : ℝ) 1,
        g (cellLeft mesh j + cellLength mesh j * xHat)) =
      (cellLength mesh j)⁻¹ *
        ∫ xHat in Set.Ioo (0 : ℝ) 1,
          p.1.eval xHat * p.1.derivative.eval xHat := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
    have hxphys : cellLeft mesh j + cellLength mesh j * xHat ∈
        Set.Ioo (cellLeft mesh j) (cellRight mesh j) := by
      constructor
      · nlinarith [cellLength_pos mesh j, hxHat.1]
      · have hright : cellRight mesh j =
            cellLeft mesh j + cellLength mesh j := by simp [cellLength]
        rw [hright]
        nlinarith [cellLength_pos mesh j, hxHat.2]
    have hcoord :
        (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
            cellLength mesh j = xHat := by
      rw [add_sub_cancel_left]
      exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
    dsimp [g]
    rw [hp _ ⟨hxphys.1.le, hxphys.2.le⟩,
      dgField_deriv_eq mesh v j p hp hxphys, hcoord]
    ring
  have hle : cellLeft mesh j ≤ cellRight mesh j := by
    exact sub_nonneg.mp (cellLength_pos mesh j).le
  have hpRight : v j (cellRight mesh j) = p.1.eval 1 := by
    have hcoord : (cellRight mesh j - cellLeft mesh j) /
        cellLength mesh j = 1 := by
      exact div_self (cellLength_pos mesh j).ne'
    rw [hp (cellRight mesh j) ⟨hle, le_rfl⟩, hcoord]
  have hpLeft : v j (cellLeft mesh j) = p.1.eval 0 := by
    simpa using hp (cellLeft mesh j) ⟨le_rfl, hle⟩
  rw [href, integral_polynomial_mul_derivative] at hscale
  simp only [smul_eq_mul] at hscale
  change (∫ x in Set.Ioo (cellLeft mesh j)
      (cellLeft mesh j + cellLength mesh j), g x) = _
  rw [hpRight, hpLeft]
  have hne := (cellLength_pos mesh j).ne'
  field_simp [hne] at hscale
  linarith

def upwindSpatialForm (a : ℝ) {N : ℕ} (mesh : PeriodicMesh N)
    (v : DGField N) (j : Fin N) : ℝ :=
  -(∫ x, a * v j x * deriv (v j) x
      ∂(volume.restrict (meshCell mesh j : Set ℝ)))
    + a * v j (cellRight mesh j) ^ 2
    - a * v (mesh.previous j) (cellRight mesh (mesh.previous j)) *
        v j (cellLeft mesh j)

lemma upwindSpatialForm_sum_nonneg {K N : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (mesh : PeriodicMesh N) (v : DGField N) (hv : IsDGField K mesh v) :
    0 ≤ ∑ j : Fin N, upwindSpatialForm a mesh v j := by
  let R : Fin N → ℝ := fun j ↦ v j (cellRight mesh j)
  let L : Fin N → ℝ := fun j ↦ v j (cellLeft mesh j)
  have hcell : ∀ j : Fin N,
      upwindSpatialForm a mesh v j =
        a / 2 * (R j) ^ 2 + a / 2 * (L j) ^ 2 -
          a * R (mesh.previous j) * L j := by
    intro j
    unfold upwindSpatialForm
    have hint :
        (∫ x, a * v j x * deriv (v j) x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
        a * ∫ x, v j x * deriv (v j) x
          ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hint, dgField_integral_mul_deriv mesh v hv j]
    dsimp [R, L]
    ring
  have hperm :
      (∑ j : Fin N, a / 2 * (R (mesh.previous j)) ^ 2) =
        ∑ j : Fin N, a / 2 * (R j) ^ 2 := by
    exact mesh.previous_bijective.sum_comp
      (fun j ↦ a / 2 * (R j) ^ 2)
  have heq :
      (∑ j : Fin N, upwindSpatialForm a mesh v j) =
        ∑ j : Fin N, a / 2 * (R (mesh.previous j) - L j) ^ 2 := by
    rw [Finset.sum_congr rfl (fun j hj ↦ hcell j)]
    calc
      (∑ x, (a / 2 * R x ^ 2 + a / 2 * L x ^ 2 -
          a * R (mesh.previous x) * L x)) =
          (∑ x, a / 2 * R x ^ 2) + (∑ x, a / 2 * L x ^ 2) -
            ∑ x, a * R (mesh.previous x) * L x := by
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ x, a / 2 * R (mesh.previous x) ^ 2) +
            (∑ x, a / 2 * L x ^ 2) -
              ∑ x, a * R (mesh.previous x) * L x := by rw [hperm]
      _ = ∑ j, a / 2 * (R (mesh.previous j) - L j) ^ 2 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  rw [heq]
  exact Finset.sum_nonneg fun j hj ↦ mul_nonneg (div_nonneg ha (by norm_num)) (sq_nonneg _)

/-- The exact smooth periodic PDE solution satisfies the semidiscrete DG equation for every
broken polynomial test function.  This is the derived consistency statement used in (9). -/
lemma SmoothPeriodicAdvectionSolution.dgConsistency {K N : ℕ}
    {a T : ℝ} (solution : SmoothPeriodicAdvectionSolution K a T)
    (ha : 0 < a) (mesh : PeriodicMesh N)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (φ : DGField N) (hφ : IsDGField K mesh φ) (j : Fin N) :
    localDGForm a mesh
      (fun s _ x ↦ solution.u x s)
      (fun s _ x ↦ solution.ut x s) φ j t = 0 := by
  have huφ : Integrable (fun x ↦ solution.ux x t * φ j x)
      (volume.restrict (meshCell mesh j : Set ℝ)) :=
    (solutionSpaceDerivativeValue_memLp K mesh ha solution t ht j).integrable_mul
      (dgField_memLp mesh φ hφ j)
  have hudφ : Integrable (fun x ↦ solution.u x t * deriv (φ j) x)
      (volume.restrict (meshCell mesh j : Set ℝ)) :=
    (solutionValue_memLp K mesh solution t ht j).integrable_mul
      (dgField_deriv_memLp mesh φ hφ j)
  have htime :
      (∫ x, solution.ut x t * φ j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      -a * ∫ x, solution.ux x t * φ j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Set.Ioo (cellLeft mesh j) (cellRight mesh j) :=
      ⟨hx.1, by simpa [meshCell, Exp2.cell, cellLength] using hx.2⟩
    have hxunit : x ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨(cellLeft_mem_unit mesh j).1.trans_lt hx'.1,
        hx'.2.trans_le (cellRight_mem_unit mesh j).2⟩
    have hpde := solution.advectionEquation x hxunit t ht
    have hut : solution.ut x t = -a * solution.ux x t := by linarith
    rw [hut]
    ring
  have hspace :
      (∫ x, a * solution.u x t * deriv (φ j) x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      a * ∫ x, solution.u x t * deriv (φ j) x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hproduct := exact_product_integral_eq_boundary
    mesh ha solution t ht φ hφ j
  have htrace :
      solution.u (cellRight mesh (mesh.previous j)) t =
        solution.u (cellLeft mesh j) t := by
    by_cases hj : j.1 = 0
    · have hprev : cellRight mesh (mesh.previous j) = 1 := by
        simpa [cellRight, hj] using mesh.previous_right_endpoint j
      have hleft : cellLeft mesh j = 0 := by
        have hjfin : j.castSucc = (0 : Fin (N + 1)) := Fin.ext (by simpa using hj)
        rw [cellLeft, hjfin, mesh.left_boundary]
      rw [hprev, hleft]
      exact (solution.periodic t ht).symm
    · have hprev : cellRight mesh (mesh.previous j) = cellLeft mesh j := by
        simpa [cellRight, cellLeft, hj] using mesh.previous_right_endpoint j
      rw [hprev]
  unfold localDGForm
  simp only
  rw [integral_add huφ hudφ] at hproduct
  rw [htime, hspace, htrace]
  linear_combination -a * hproduct

lemma projectionError_localDGForm_eq_time {K N : ℕ} {a T : ℝ}
    (mesh : PeriodicMesh N) (solution : SmoothPeriodicAdvectionSolution K a T)
    (projection : ProjectionTrajectory K mesh T solution)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (φ : DGField N) (hφ : IsDGField K mesh φ) (j : Fin N) :
    localDGForm a mesh
        (fun s j x ↦ solution.u x s - projection.value s j x)
        (fun s j x ↦ solution.ut x s - projection.timeDerivativeValue s j x)
        φ j t =
      ∫ x, (solution.ut x t - projection.timeDerivativeValue t j x) * φ j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
  obtain ⟨p, hp⟩ := hφ j
  have hpdeg : p.1.natDegree ≤ K := Exp2.mem_PolyLE_iff.mp p.2
  have hmoment :
      (∫ xHat, (solution.u
          (cellLeft mesh j + cellLength mesh j * xHat) t -
        projection.value t j
          (cellLeft mesh j + cellLength mesh j * xHat)) *
          p.1.derivative.eval xHat
        ∂(volume.restrict Exp2.referenceCell)) = 0 := by
    by_cases hK : K = 0
    · have hp0 : p.1 = Polynomial.C (p.1.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero (by omega)
      rw [hp0]
      simp
    · apply ((projection.value_spec t ht).2 j).1
      calc
        p.1.derivative.natDegree ≤ p.1.natDegree - 1 :=
          Polynomial.natDegree_derivative_le p.1
        _ < K := by omega
  let g : ℝ → ℝ := fun x ↦
    a * (solution.u x t - projection.value t j x) * deriv (φ j) x
  have hscale := Exp2AffineMeasure.setIntegral_comp_affine_Ioo
    (a := cellLeft mesh j) g (cellLength_pos mesh j)
  have href :
      (∫ xHat in Set.Ioo (0 : ℝ) 1,
        g (cellLeft mesh j + cellLength mesh j * xHat)) = 0 := by
    have heq : (fun xHat ↦
        g (cellLeft mesh j + cellLength mesh j * xHat)) =ᵐ[
          volume.restrict Exp2.referenceCell]
        (fun xHat ↦ (a / cellLength mesh j) *
          ((solution.u (cellLeft mesh j + cellLength mesh j * xHat) t -
            projection.value t j
              (cellLeft mesh j + cellLength mesh j * xHat)) *
            p.1.derivative.eval xHat)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with xHat hxHat
      have hxphys : cellLeft mesh j + cellLength mesh j * xHat ∈
          Set.Ioo (cellLeft mesh j) (cellRight mesh j) := by
        constructor
        · nlinarith [cellLength_pos mesh j, hxHat.1]
        · have hright : cellRight mesh j =
              cellLeft mesh j + cellLength mesh j := by simp [cellLength]
          rw [hright]
          nlinarith [cellLength_pos mesh j, hxHat.2]
      have hcoord :
          (cellLeft mesh j + cellLength mesh j * xHat - cellLeft mesh j) /
              cellLength mesh j = xHat := by
        rw [add_sub_cancel_left]
        exact mul_div_cancel_left₀ xHat (cellLength_pos mesh j).ne'
      dsimp [g]
      rw [dgField_deriv_eq mesh φ j p hp hxphys, hcoord]
      ring
    have heq' : (fun xHat ↦
        g (cellLeft mesh j + cellLength mesh j * xHat)) =ᵐ[
          volume.restrict (Set.Ioo (0 : ℝ) 1)]
        (fun xHat ↦ (a / cellLength mesh j) *
          ((solution.u (cellLeft mesh j + cellLength mesh j * xHat) t -
            projection.value t j
              (cellLeft mesh j + cellLength mesh j * xHat)) *
            p.1.derivative.eval xHat)) := by
      simpa [Exp2.referenceCell, Exp2.cell] using heq
    rw [integral_congr_ae heq', integral_const_mul]
    simpa [Exp2.referenceCell, Exp2.cell] using congrArg (fun z ↦
      (a / cellLength mesh j) * z) hmoment
  rw [href] at hscale
  have hvolume :
      (∫ x, g x ∂(volume.restrict (meshCell mesh j : Set ℝ))) = 0 := by
    simp only [smul_eq_mul] at hscale
    have hinv : (cellLength mesh j)⁻¹ ≠ 0 := inv_ne_zero (cellLength_pos mesh j).ne'
    apply (mul_eq_zero.mp hscale.symm).resolve_left hinv
  have hright := ((projection.value_spec t ht).2 j).2
  have hprev := ((projection.value_spec t ht).2 (mesh.previous j)).2
  unfold localDGForm
  simp only
  have htransport :
      (∫ x, a * (solution.u x t - projection.value t j x) * deriv (φ j) x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) = 0 := by
    exact hvolume
  rw [htransport]
  rw [hright, hprev]
  ring

lemma localDGForm_sub {N : ℕ} (a : ℝ) (mesh : PeriodicMesh N)
    (v vt w wt : DGTrajectory N) (φ : DGField N) (j : Fin N) (t : ℝ)
    (hvt : Integrable (fun x ↦ vt t j x * φ j x)
      (volume.restrict (meshCell mesh j : Set ℝ)))
    (hwt : Integrable (fun x ↦ wt t j x * φ j x)
      (volume.restrict (meshCell mesh j : Set ℝ)))
    (hv : Integrable (fun x ↦ a * v t j x * deriv (φ j) x)
      (volume.restrict (meshCell mesh j : Set ℝ)))
    (hw : Integrable (fun x ↦ a * w t j x * deriv (φ j) x)
      (volume.restrict (meshCell mesh j : Set ℝ))) :
    localDGForm a mesh
        (fun s j x ↦ v s j x - w s j x)
        (fun s j x ↦ vt s j x - wt s j x) φ j t =
      localDGForm a mesh v vt φ j t - localDGForm a mesh w wt φ j t := by
  have htime :
      (∫ x, (vt t j x - wt t j x) * φ j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      (∫ x, vt t j x * φ j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) -
      ∫ x, wt t j x * φ j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
    rw [← integral_sub hvt hwt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hspace :
      (∫ x, a * (v t j x - w t j x) * deriv (φ j) x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) =
      (∫ x, a * v t j x * deriv (φ j) x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) -
      ∫ x, a * w t j x * deriv (φ j) x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)) := by
    rw [← integral_sub hv hw]
    apply integral_congr_ae
    filter_upwards with x
    ring
  unfold localDGForm
  simp only
  rw [htime, hspace]
  ring

lemma localDGForm_self_eq_time_add_spatial {N : ℕ} (a : ℝ)
    (mesh : PeriodicMesh N) (v vt : DGTrajectory N) (j : Fin N) (t : ℝ) :
    localDGForm a mesh v vt (v t) j t =
      (∫ x, vt t j x * v t j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))) +
        upwindSpatialForm a mesh (v t) j := by
  unfold localDGForm upwindSpatialForm
  ring

lemma hasDerivWithinAt_Ici_of_Icc {f : ℝ → ℝ} {f' t T : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) T)
    (h : HasDerivWithinAt f f' (Set.Icc (0 : ℝ) T) t) :
    HasDerivWithinAt f f' (Set.Ici t) t := by
  have heq : ((Set.Icc (0 : ℝ) T ∩ Set.Ici t : Set ℝ) : ℝ → Prop) =ᶠ[nhds t]
      (Set.Ici t : ℝ → Prop) := by
    filter_upwards [Iio_mem_nhds ht.2] with z hz
    apply propext
    constructor
    · exact fun hmem ↦ hmem.2
    · intro hmem
      exact ⟨⟨ht.1.trans hmem, hz.le⟩, hmem⟩
  exact HasDerivWithinAt.congr_set heq
    (h.mono Set.inter_subset_left)

lemma broken_integral_mul_abs_le {N : ℕ} (mesh : PeriodicMesh N)
    (f g : DGField N)
    (hf : ∀ j : Fin N, MemLp (f j) 2
      (volume.restrict (meshCell mesh j : Set ℝ)))
    (hg : ∀ j : Fin N, MemLp (g j) 2
      (volume.restrict (meshCell mesh j : Set ℝ))) :
    |∑ j : Fin N, ∫ x, f j x * g j x
      ∂(volume.restrict (meshCell mesh j : Set ℝ))| ≤
      brokenL2Norm mesh f * brokenL2Norm mesh g := by
  let F : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun j ↦ Exp2.l2NormOn (meshCell mesh j) (f j))
  let G : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun j ↦ Exp2.l2NormOn (meshCell mesh j) (g j))
  have hsum :
      |∑ j : Fin N, ∫ x, f j x * g j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ))| ≤
      ∑ j : Fin N, Exp2.l2NormOn (meshCell mesh j) (f j) *
        Exp2.l2NormOn (meshCell mesh j) (g j) := by
    calc
      _ ≤ ∑ j : Fin N, |∫ x, f j x * g j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun j hj ↦
        Exp2.abs_integral_mul_le_l2NormOn (f := f j) (g := g j) (hf j) (hg j)
  have hcs := abs_real_inner_le_norm F G
  have hdot :
      (∑ j : Fin N, Exp2.l2NormOn (meshCell mesh j) (f j) *
        Exp2.l2NormOn (meshCell mesh j) (g j)) ≤ ‖F‖ * ‖G‖ := by
    rw [PiLp.inner_apply] at hcs
    have habs :
        |∑ j : Fin N, Exp2.l2NormOn (meshCell mesh j) (f j) *
          Exp2.l2NormOn (meshCell mesh j) (g j)| ≤ ‖F‖ * ‖G‖ := by
      simpa [F, G, RCLike.inner_apply, mul_comm] using hcs
    exact (le_abs_self _).trans habs
  have hFnorm : ‖F‖ = brokenL2Norm mesh f := by
    rw [EuclideanSpace.norm_eq]
    unfold brokenL2Norm
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [F, Real.norm_eq_abs, abs_of_nonneg (Exp2.l2NormOn_nonneg _ _)]
  have hGnorm : ‖G‖ = brokenL2Norm mesh g := by
    rw [EuclideanSpace.norm_eq]
    unfold brokenL2Norm
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [G, Real.norm_eq_abs, abs_of_nonneg (Exp2.l2NormOn_nonneg _ _)]
  rw [← hFnorm, ← hGnorm]
  exact hsum.trans hdot

/-- The energy identity (9)--(13), periodic jump dissipation, Young's inequality, and
Gronwall's inequality bound the discrete error `Π_h u-u_h` with order `K+1`. -/
theorem discrete_error_bound (K : ℕ) {a T ρ : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hρ : 1 ≤ ρ)
    (solution : SmoothPeriodicAdvectionSolution K a T) :
    ∃ Cξ : ℝ, 0 ≤ Cξ ∧
      ∀ {N : ℕ} (mesh : PeriodicMesh N), IsQuasiUniform ρ mesh →
      ∀ (uh : DGTrajectory N), IsSemiDiscreteUpwindDG K a T mesh uh →
        HasGaussRadauInitialData K mesh solution.u uh →
      ∀ projection : ProjectionTrajectory K mesh T solution,
        brokenL2Norm mesh
          (fun j x ↦ projection.value T j x - uh T j x) ≤
            Cξ * mesh.meshSize ^ (K + 1) := by
  obtain ⟨Cηt, hCηt, hηt⟩ :=
    gaussRadau_timeDerivative_error_bound K hρ solution
  refine ⟨Cηt * Real.sqrt (Real.exp T),
    mul_nonneg hCηt (Real.sqrt_nonneg _), ?_⟩
  intro N mesh hmesh uh huh hinit projection
  obtain ⟨uht, huhRegularity, hscheme⟩ := huh
  let ξ : DGTrajectory N := fun t j x ↦ projection.value t j x - uh t j x
  let ξt : DGTrajectory N := fun t j x ↦
    projection.timeDerivativeValue t j x - uht t j x
  let ηt : DGTrajectory N := fun t j x ↦
    solution.ut x t - projection.timeDerivativeValue t j x
  let Q : ℝ → ℝ := fun t ↦ (brokenL2Norm mesh (ξ t)) ^ 2
  let D : ℝ → ℝ := fun t ↦ 2 * ∑ j : Fin N, ∫ x,
    ξt t j x * ξ t j x
      ∂(volume.restrict (meshCell mesh j : Set ℝ))
  let B : ℝ := Cηt * mesh.meshSize ^ (K + 1)
  let projectionRegularity := projection.regularity K mesh solution
  let ξRegularity := projectionRegularity.sub huhRegularity
  have hB : 0 ≤ B := mul_nonneg hCηt
    (pow_nonneg mesh.meshSize_pos.le _)
  have hQderiv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt Q (D t) (Set.Icc (0 : ℝ) T) t := by
    intro t ht
    have hraw := ξRegularity.energy_hasDerivWithinAt
      (fun s hs j ↦
        (projectionValue_memLp K mesh solution projection s hs j).sub
          (dgField_memLp mesh (uh s)
            (huhRegularity.value_isDGField s hs) j)) t ht
    simpa only [Q, D, ξ, ξt, ξRegularity, projectionRegularity] using hraw
  have hDbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      D t ≤ Q t + B ^ 2 := by
    intro t ht
    have huhDG := huhRegularity.value_isDGField t ht
    have huhtDG := huhRegularity.timeDerivativeValue_isDGField t ht
    have hξDG : IsDGField K mesh (ξ t) :=
      isDGField_sub mesh (projection.value_spec t ht).1 huhDG
    have hξtDG : IsDGField K mesh (ξt t) :=
      isDGField_sub mesh (projection.timeDerivative_spec t ht).1 huhtDG
    have hξmem : ∀ j : Fin N, MemLp (ξ t j) 2
        (volume.restrict (meshCell mesh j : Set ℝ)) := by
      intro j
      exact (projectionValue_memLp K mesh solution projection t ht j).sub
        (dgField_memLp mesh (uh t) huhDG j)
    have hξtmem : ∀ j : Fin N, MemLp (ξt t j) 2
        (volume.restrict (meshCell mesh j : Set ℝ)) := by
      intro j
      exact (projectionTimeDerivativeValue_memLp K mesh solution projection t ht j).sub
        (dgField_memLp mesh (uht t) huhtDG j)
    have hηtmem : ∀ j : Fin N, MemLp (ηt t j) 2
        (volume.restrict (meshCell mesh j : Set ℝ)) := by
      intro j
      exact (solutionTimeDerivativeValue_memLp K mesh solution t ht j).sub
        (projectionTimeDerivativeValue_memLp K mesh solution projection t ht j)
    have hcell : ∀ j : Fin N,
        (∫ x, ξt t j x * ξ t j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))) +
          upwindSpatialForm a mesh (ξ t) j =
        -(∫ x, ηt t j x * ξ t j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))) := by
      intro j
      have hderiv := dgField_deriv_memLp mesh (ξ t) hξDG j
      have huTime : Integrable (fun x ↦ solution.ut x t * ξ t j x)
          (volume.restrict (meshCell mesh j : Set ℝ)) :=
        (solutionTimeDerivativeValue_memLp K mesh solution t ht j).integrable_mul
          (hξmem j)
      have hpTime : Integrable
          (fun x ↦ projection.timeDerivativeValue t j x * ξ t j x)
          (volume.restrict (meshCell mesh j : Set ℝ)) :=
        (projectionTimeDerivativeValue_memLp K mesh solution projection t ht j).integrable_mul
          (hξmem j)
      have huhTime : Integrable (fun x ↦ uht t j x * ξ t j x)
          (volume.restrict (meshCell mesh j : Set ℝ)) :=
        (dgField_memLp mesh (uht t) huhtDG j).integrable_mul (hξmem j)
      have huCoeff : MemLp (fun x ↦ a * solution.u x t) 2
          (volume.restrict (meshCell mesh j : Set ℝ)) := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (solutionValue_memLp K mesh solution t ht j).const_smul a
      have hpCoeff : MemLp
          (fun x ↦ a * projection.value t j x) 2
          (volume.restrict (meshCell mesh j : Set ℝ)) := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (projectionValue_memLp K mesh solution projection t ht j).const_smul a
      have huhCoeff : MemLp (fun x ↦ a * uh t j x) 2
          (volume.restrict (meshCell mesh j : Set ℝ)) := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (dgField_memLp mesh (uh t) huhDG j).const_smul a
      have huSpace : Integrable
          (fun x ↦ a * solution.u x t * deriv (ξ t j) x)
          (volume.restrict (meshCell mesh j : Set ℝ)) :=
        huCoeff.integrable_mul hderiv
      have hpSpace : Integrable
          (fun x ↦ a * projection.value t j x * deriv (ξ t j) x)
          (volume.restrict (meshCell mesh j : Set ℝ)) :=
        hpCoeff.integrable_mul hderiv
      have huhSpace : Integrable
          (fun x ↦ a * uh t j x * deriv (ξ t j) x)
          (volume.restrict (meshCell mesh j : Set ℝ)) :=
        huhCoeff.integrable_mul hderiv
      have hsubExactProjection := localDGForm_sub a mesh
        (fun s _ x ↦ solution.u x s) (fun s _ x ↦ solution.ut x s)
        projection.value projection.timeDerivativeValue (ξ t) j t
        huTime hpTime huSpace hpSpace
      have hprojectionError := projectionError_localDGForm_eq_time
        mesh solution projection t ht (ξ t) hξDG j
      have hexact := solution.dgConsistency ha mesh t ht (ξ t) hξDG j
      have hprojectionForm :
          localDGForm a mesh projection.value projection.timeDerivativeValue
              (ξ t) j t =
            -(∫ x, ηt t j x * ξ t j x
              ∂(volume.restrict (meshCell mesh j : Set ℝ))) := by
        rw [hsubExactProjection, hexact] at hprojectionError
        simp only [ηt]
        simp only [zero_sub] at hprojectionError
        linarith
      have hsubProjectionUh := localDGForm_sub a mesh
        projection.value projection.timeDerivativeValue uh uht (ξ t) j t
        hpTime huhTime hpSpace huhSpace
      have huhForm := hscheme t ht (ξ t) hξDG j
      have hξForm : localDGForm a mesh ξ ξt (ξ t) j t =
          -(∫ x, ηt t j x * ξ t j x
            ∂(volume.restrict (meshCell mesh j : Set ℝ))) := by
        simpa only [ξ, ξt] using
          hsubProjectionUh.trans (by rw [hprojectionForm, huhForm, sub_zero])
      rw [localDGForm_self_eq_time_add_spatial] at hξForm
      exact hξForm
    have hsumEq :
        (∑ j : Fin N, ∫ x, ξt t j x * ξ t j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))) +
          (∑ j : Fin N, upwindSpatialForm a mesh (ξ t) j) =
        -(∑ j : Fin N, ∫ x, ηt t j x * ξ t j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))) := by
      calc
        _ = ∑ j : Fin N,
            ((∫ x, ξt t j x * ξ t j x
              ∂(volume.restrict (meshCell mesh j : Set ℝ))) +
              upwindSpatialForm a mesh (ξ t) j) :=
            Finset.sum_add_distrib.symm
        _ = ∑ j : Fin N,
            -(∫ x, ηt t j x * ξ t j x
              ∂(volume.restrict (meshCell mesh j : Set ℝ))) :=
            Finset.sum_congr rfl (fun j hj ↦ hcell j)
        _ = _ := by rw [Finset.sum_neg_distrib]
    have hspatial := upwindSpatialForm_sum_nonneg a ha.le mesh (ξ t) hξDG
    have htimeLe :
        (∑ j : Fin N, ∫ x, ξt t j x * ξ t j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))) ≤
        |∑ j : Fin N, ∫ x, ηt t j x * ξ t j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))| := by
      nlinarith [neg_le_abs (∑ j : Fin N, ∫ x, ηt t j x * ξ t j x
        ∂(volume.restrict (meshCell mesh j : Set ℝ)))]
    have hcs := broken_integral_mul_abs_le mesh (ηt t) (ξ t) hηtmem hξmem
    have hηbound : brokenL2Norm mesh (ηt t) ≤ B := by
      simpa only [ηt, B] using hηt mesh hmesh projection t ht
    have hηnonneg : 0 ≤ brokenL2Norm mesh (ηt t) := Real.sqrt_nonneg _
    have hξnonneg : 0 ≤ brokenL2Norm mesh (ξ t) := Real.sqrt_nonneg _
    have hyoung : 2 * (brokenL2Norm mesh (ηt t) * brokenL2Norm mesh (ξ t)) ≤
        (brokenL2Norm mesh (ηt t)) ^ 2 + (brokenL2Norm mesh (ξ t)) ^ 2 := by
      nlinarith [sq_nonneg (brokenL2Norm mesh (ηt t) - brokenL2Norm mesh (ξ t))]
    calc
      D t ≤ 2 * |∑ j : Fin N, ∫ x, ηt t j x * ξ t j x
          ∂(volume.restrict (meshCell mesh j : Set ℝ))| := by
        dsimp only [D]
        exact mul_le_mul_of_nonneg_left htimeLe (by norm_num)
      _ ≤ 2 * (brokenL2Norm mesh (ηt t) * brokenL2Norm mesh (ξ t)) :=
        mul_le_mul_of_nonneg_left hcs (by norm_num)
      _ ≤ (brokenL2Norm mesh (ηt t)) ^ 2 +
          (brokenL2Norm mesh (ξ t)) ^ 2 := hyoung
      _ ≤ B ^ 2 + (brokenL2Norm mesh (ξ t)) ^ 2 := by
        nlinarith
      _ = Q t + B ^ 2 := by
        dsimp only [Q]
        ring
  have hQcontinuous : ContinuousOn Q (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hQderiv t ht).continuousWithinAt
  have hright : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ r : ℝ, D t < r →
      ∃ᶠ z in nhdsWithin t (Set.Ioi t),
        (z - t)⁻¹ * (Q z - Q t) < r := by
    intro t ht r hr
    have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    simpa only [slope] using
      (hasDerivWithinAt_Ici_of_Icc ht (hQderiv t ht')).liminf_right_slope_le hr
  have hzero : Q 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hprojUnique := localProjection_unique K mesh solution 0 h0
      (projection.value 0) (projection.value_spec 0 h0)
    have huhUnique := localProjection_unique K mesh solution 0 h0
      (uh 0) hinit
    have hcellZero : ∀ j : Fin N, Exp2.l2NormOn (meshCell mesh j) (ξ 0 j) = 0 := by
      intro j
      have heq : ξ 0 j =ᵐ[volume.restrict (meshCell mesh j : Set ℝ)]
          (fun _ ↦ (0 : ℝ)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        have hx' : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j) :=
          ⟨hx.1.le, by simpa [meshCell, Exp2.cell, cellLength] using hx.2.le⟩
        simp only [ξ]
        rw [hprojUnique j x hx', huhUnique j x hx']
        simp
      unfold Exp2.l2NormOn
      rw [eLpNorm_congr_ae heq]
      simp
    dsimp only [Q, brokenL2Norm]
    have hsumZero :
        (∑ j : Fin N, (Exp2.l2NormOn (meshCell mesh j) (ξ 0 j)) ^ 2) = 0 := by
      simp [hcellZero]
    rw [hsumZero]
    norm_num
  have hgronwall := le_gronwallBound_of_liminf_deriv_right_le
    (f := Q) (f' := D) (δ := 0) (K := 1) (ε := B ^ 2)
    (a := 0) (b := T) hQcontinuous hright (by linarith) (by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
      have := hDbound t ht'
      linarith) T ⟨hT.le, le_rfl⟩
  have hQT : Q T ≤ B ^ 2 * (Real.exp T - 1) := by
    simpa [gronwallBound] using hgronwall
  have hQTexp : Q T ≤ B ^ 2 * Real.exp T := by
    calc
      Q T ≤ B ^ 2 * (Real.exp T - 1) := hQT
      _ ≤ B ^ 2 * Real.exp T := by nlinarith [sq_nonneg B]
  have hsqrt := Real.sqrt_le_sqrt hQTexp
  calc
    brokenL2Norm mesh
        (fun j x ↦ projection.value T j x - uh T j x) =
        Real.sqrt (Q T) := by
      have hnormNonneg : 0 ≤ brokenL2Norm mesh
          (fun j x ↦ projection.value T j x - uh T j x) := Real.sqrt_nonneg _
      dsimp only [Q, ξ]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnormNonneg]
    _ ≤ Real.sqrt (B ^ 2 * Real.exp T) := hsqrt
    _ = B * Real.sqrt (Real.exp T) := by
      rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hB]
    _ = (Cηt * Real.sqrt (Real.exp T)) * mesh.meshSize ^ (K + 1) := by
      dsimp only [B]
      ring

end Exp1
