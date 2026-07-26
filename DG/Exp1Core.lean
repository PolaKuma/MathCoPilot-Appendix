import Exp2
import Mathlib.Analysis.ODE.Gronwall

open scoped ENNReal MeasureTheory Topology Interval BigOperators
open MeasureTheory Set Filter

noncomputable section
namespace Exp1

/-- A periodic one-dimensional mesh with `N` cells and nodes
`0 = x_{1/2} < ... < x_{N+1/2} = 1`.  The stored predecessor records the periodic
upwind neighbour of every cell. -/
structure PeriodicMesh (N : ℕ) where
  nodes : Fin (N + 1) → ℝ
  cellCount_pos : 0 < N
  nodes_strictMono : StrictMono nodes
  left_boundary : nodes 0 = 0
  right_boundary : nodes (Fin.last N) = 1
  previous : Fin N → Fin N
  previous_right_endpoint : ∀ j : Fin N,
    nodes (previous j).succ = if j.1 = 0 then 1 else nodes j.castSucc
  previous_bijective : Function.Bijective previous
  meshSize : ℝ
  meshSize_pos : 0 < meshSize
  cellLength_le_meshSize : ∀ j : Fin N,
    nodes j.succ - nodes j.castSucc ≤ meshSize
  meshSize_attained : ∃ j : Fin N,
    nodes j.succ - nodes j.castSucc = meshSize

/-- Left endpoint of a mesh cell. -/
def cellLeft {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) : ℝ :=
  mesh.nodes j.castSucc

/-- Right endpoint of a mesh cell. -/
def cellRight {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) : ℝ :=
  mesh.nodes j.succ

/-- Length of a mesh cell. -/
def cellLength {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) : ℝ :=
  cellRight mesh j - cellLeft mesh j

lemma cellLength_pos {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) :
    0 < cellLength mesh j := by
  exact sub_pos.mpr (mesh.nodes_strictMono (by
    change j.1 < j.1 + 1
    omega))

/-- The open interior of a mesh cell, reusing the interval representation from Exp.2. -/
abbrev meshCell {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) :
    TopologicalSpace.Opens ℝ :=
  Exp2.cell (cellLeft mesh j) (cellLength mesh j)

/-- Quasi-uniformity with one fixed ratio `ρ`, uniformly across a mesh family. -/
def IsQuasiUniform {N : ℕ} (ρ : ℝ) (mesh : PeriodicMesh N) : Prop :=
  1 ≤ ρ ∧ ∀ j : Fin N, mesh.meshSize ≤ ρ * cellLength mesh j

/-- A broken spatial field, with one representative on each cell. -/
abbrev DGField (N : ℕ) := Fin N → ℝ → ℝ

/-- A time-dependent broken field. -/
abbrev DGTrajectory (N : ℕ) := ℝ → DGField N

/-- The discontinuous finite element space `U_h^K`: degree at most `K` on each cell. -/
def IsDGField (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N) (v : DGField N) : Prop :=
  ∀ j : Fin N, ∃ p : Exp2.PolyLE K,
    ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
      v j x = p.1.eval ((x - cellLeft mesh j) / cellLength mesh j)

/-- The cellwise decomposition of the standard `L²(0,1)` norm.  Interface values have
measure zero, so this is the `L²` norm of a broken field on the whole periodic domain. -/
def brokenL2Norm {N : ℕ} (mesh : PeriodicMesh N) (v : DGField N) : ℝ :=
  Real.sqrt (∑ j : Fin N, (Exp2.l2NormOn (meshCell mesh j) (v j)) ^ 2)

/-- The local Gauss--Radau conditions (4)--(5), with moments against all polynomials of
degree at most `K-1` and matching of the trace at the right endpoint. -/
def IsLocalGaussRadauProjection (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    (u : ℝ → ℝ) (p : DGField N) : Prop :=
  IsDGField K mesh p ∧
  ∀ j : Fin N,
    (∀ q : Polynomial ℝ, q.natDegree < K →
      (∫ xHat, (u (cellLeft mesh j + cellLength mesh j * xHat) -
          p j (cellLeft mesh j + cellLength mesh j * xHat)) * q.eval xHat
        ∂(volume.restrict Exp2.referenceCell)) = 0) ∧
    p j (cellRight mesh j) = u (cellRight mesh j)

/-- The cell form with the time derivative supplied explicitly.  This is equivalent to (1)
for a differentiable trajectory and avoids choosing an ambient derivative at the endpoints of
the finite time interval. -/
def localDGForm (a : ℝ) {N : ℕ} (mesh : PeriodicMesh N)
    (v vt : DGTrajectory N) (φ : DGField N) (j : Fin N) (t : ℝ) : ℝ :=
  (∫ x, vt t j x * φ j x
      ∂(volume.restrict (meshCell mesh j : Set ℝ)))
    - (∫ x, a * v t j x * deriv (φ j) x
      ∂(volume.restrict (meshCell mesh j : Set ℝ)))
    + a * v t j (cellRight mesh j) * φ j (cellRight mesh j)
    - a * v t (mesh.previous j) (cellRight mesh (mesh.previous j)) *
        φ j (cellLeft mesh j)

/-- A sufficiently smooth exact solution on `[0,T]`.  The open time collar is the precise
formal meaning of smoothness up to the two time endpoints; it is used only to justify
differentiation under the spatial integral.  DG consistency and projection identities are not
fields of this structure: they are derived from these data. -/
structure SmoothPeriodicAdvectionSolution (K : ℕ) (a T : ℝ) where
  u : ℝ → ℝ → ℝ
  ut : ℝ → ℝ → ℝ
  ux : ℝ → ℝ → ℝ
  u_joint_continuous : Continuous (Function.uncurry u)
  ut_joint_continuous : Continuous (Function.uncurry ut)
  timeDerivative : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    ∀ t ∈ Set.Ioo (-1 : ℝ) (T + 1),
    HasDerivAt (u x) (ut x t) t
  spaceDerivative : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
    HasDerivAt (fun y ↦ u y t) (ux x t) x
  advectionEquation : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) T,
    ut x t + a * ux x t = 0
  periodic : ∀ t ∈ Set.Icc (0 : ℝ) T, u 0 t = u 1 t
  uCell : ∀ {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) (t : ℝ),
    Exp2.SobolevMapOn (K + 1) (meshCell mesh j)
  utCell : ∀ {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N) (t : ℝ),
    Exp2.SobolevMapOn (K + 1) (meshCell mesh j)
  uCell_eq : ∀ {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N)
    (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
        uCell mesh j t x = u x t
  utCell_eq : ∀ {N : ℕ} (mesh : PeriodicMesh N) (j : Fin N)
    (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
        utCell mesh j t x = ut x t
  uniformRegularity : ∃ M : ℝ, 0 ≤ M ∧
    ∀ {N : ℕ} (mesh : PeriodicMesh N) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      Real.sqrt (∑ j : Fin N,
        (Exp2.sobolevSeminorm (uCell mesh j t)) ^ 2) ≤ M ∧
      Real.sqrt (∑ j : Fin N,
        (Exp2.sobolevSeminorm (utCell mesh j t)) ^ 2) ≤ M

/-- The reference pullback of the exact solution on one physical mesh cell. -/
def SmoothPeriodicAdvectionSolution.uCellPullback
    (solution : SmoothPeriodicAdvectionSolution K a T) {N : ℕ}
    (mesh : PeriodicMesh N) (j : Fin N) (t : ℝ) :
    Exp2.SobolevMapOn (K + 1) Exp2.referenceCell :=
  Exp2.affinePullback (cellLength_pos mesh j) (solution.uCell mesh j t)

/-- The reference pullback of the time derivative on one physical mesh cell. -/
def SmoothPeriodicAdvectionSolution.utCellPullback
    (solution : SmoothPeriodicAdvectionSolution K a T) {N : ℕ}
    (mesh : PeriodicMesh N) (j : Fin N) (t : ℝ) :
    Exp2.SobolevMapOn (K + 1) Exp2.referenceCell :=
  Exp2.affinePullback (cellLength_pos mesh j) (solution.utCell mesh j t)

lemma SmoothPeriodicAdvectionSolution.uCellPullback_eq
    (solution : SmoothPeriodicAdvectionSolution K a T) {N : ℕ}
    (mesh : PeriodicMesh N) (j : Fin N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (xHat : ℝ)
    (hxHat : xHat ∈ Set.Icc (0 : ℝ) 1) :
    solution.uCellPullback mesh j t xHat =
      solution.u (cellLeft mesh j + cellLength mesh j * xHat) t := by
  have h0 := Exp2.affinePullback_spec (cellLength_pos mesh j)
    (solution.uCell mesh j t) 0 (Nat.zero_le (K + 1))
  have h0x := congrFun h0 xHat
  rw [(Exp2.affinePullback (cellLength_pos mesh j)
      (solution.uCell mesh j t)).derivative_zero,
    (solution.uCell mesh j t).derivative_zero] at h0x
  simp only [pow_zero, one_mul] at h0x
  change Exp2.affinePullback (cellLength_pos mesh j)
    (solution.uCell mesh j t) xHat = _
  rw [h0x]
  apply solution.uCell_eq mesh j t ht
  constructor
  · nlinarith [cellLength_pos mesh j, hxHat.1]
  · have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
      simp [cellLength]
    rw [hright]
    nlinarith [cellLength_pos mesh j, hxHat.2]

lemma SmoothPeriodicAdvectionSolution.utCellPullback_eq
    (solution : SmoothPeriodicAdvectionSolution K a T) {N : ℕ}
    (mesh : PeriodicMesh N) (j : Fin N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) (xHat : ℝ)
    (hxHat : xHat ∈ Set.Icc (0 : ℝ) 1) :
    solution.utCellPullback mesh j t xHat =
      solution.ut (cellLeft mesh j + cellLength mesh j * xHat) t := by
  have h0 := Exp2.affinePullback_spec (cellLength_pos mesh j)
    (solution.utCell mesh j t) 0 (Nat.zero_le (K + 1))
  have h0x := congrFun h0 xHat
  rw [(Exp2.affinePullback (cellLength_pos mesh j)
      (solution.utCell mesh j t)).derivative_zero,
    (solution.utCell mesh j t).derivative_zero] at h0x
  simp only [pow_zero, one_mul] at h0x
  change Exp2.affinePullback (cellLength_pos mesh j)
    (solution.utCell mesh j t) xHat = _
  rw [h0x]
  apply solution.utCell_eq mesh j t ht
  constructor
  · nlinarith [cellLength_pos mesh j, hxHat.1]
  · have hright : cellRight mesh j = cellLeft mesh j + cellLength mesh j := by
      simp [cellLength]
    rw [hright]
    nlinarith [cellLength_pos mesh j, hxHat.2]

/-- Monomial coefficients of a degree-at-most-`K` broken polynomial. -/
abbrev DGCoefficients (K N : ℕ) := Fin N → Fin (K + 1) → ℝ

/-- Concrete finite-dimensional `C¹` regularity of a polynomial trajectory.  This records the
standard coefficient ODE meaning of `v_t`; it does not assume an energy identity. -/
structure DGTrajectoryRegularity (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N) (T : ℝ)
    (v vt : DGTrajectory N) where
  coefficient : ℝ → DGCoefficients K N
  timeDerivativeCoefficient : ℝ → DGCoefficients K N
  value_eq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j : Fin N,
    ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
      v t j x = ∑ i : Fin (K + 1), coefficient t j i *
        ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ)
  timeDerivativeValue_eq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j : Fin N,
    ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
      vt t j x = ∑ i : Fin (K + 1), timeDerivativeCoefficient t j i *
        ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ)
  coefficient_hasDerivWithinAt : ∀ j : Fin N, ∀ i : Fin (K + 1),
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s ↦ coefficient s j i)
        (timeDerivativeCoefficient t j i) (Set.Icc (0 : ℝ) T) t

/-- The canonical polynomial reconstructed from the monomial coordinates. -/
def DGTrajectoryRegularity.coefficientPolynomial
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (regularity : DGTrajectoryRegularity K mesh T v vt) (t : ℝ) (j : Fin N) :
    Exp2.PolyLE K :=
  (Polynomial.degreeLTEquiv ℝ (K + 1)).symm (regularity.coefficient t j)

/-- The derivative polynomial reconstructed from the derivative coordinates. -/
def DGTrajectoryRegularity.timeDerivativeCoefficientPolynomial
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (regularity : DGTrajectoryRegularity K mesh T v vt) (t : ℝ) (j : Fin N) :
    Exp2.PolyLE K :=
  (Polynomial.degreeLTEquiv ℝ (K + 1)).symm
    (regularity.timeDerivativeCoefficient t j)

theorem DGTrajectoryRegularity.value_isDGField
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (regularity : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : IsDGField K mesh (v t) := by
  intro j
  refine ⟨regularity.coefficientPolynomial t j, ?_⟩
  intro x hx
  rw [regularity.value_eq t ht j x hx]
  symm
  simpa [DGTrajectoryRegularity.coefficientPolynomial] using
    Polynomial.eval_eq_sum_degreeLTEquiv
      (regularity.coefficientPolynomial t j).2
      ((x - cellLeft mesh j) / cellLength mesh j)

theorem DGTrajectoryRegularity.timeDerivativeValue_isDGField
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (regularity : DGTrajectoryRegularity K mesh T v vt)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : IsDGField K mesh (vt t) := by
  intro j
  refine ⟨regularity.timeDerivativeCoefficientPolynomial t j, ?_⟩
  intro x hx
  rw [regularity.timeDerivativeValue_eq t ht j x hx]
  symm
  simpa [DGTrajectoryRegularity.timeDerivativeCoefficientPolynomial] using
    Polynomial.eval_eq_sum_degreeLTEquiv
      (regularity.timeDerivativeCoefficientPolynomial t j).2
      ((x - cellLeft mesh j) / cellLength mesh j)

theorem DGTrajectoryRegularity.hasDerivWithinAt
    {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ} {v vt : DGTrajectory N}
    (regularity : DGTrajectoryRegularity K mesh T v vt)
    (j : Fin N) (x : ℝ)
    (hx : x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s ↦ v s j x) (vt t j x)
      (Set.Icc (0 : ℝ) T) t := by
  have hsum : HasDerivWithinAt
      (fun s ↦ ∑ i : Fin (K + 1), regularity.coefficient s j i *
        ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ))
      (∑ i : Fin (K + 1), regularity.timeDerivativeCoefficient t j i *
        ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ))
      (Set.Icc (0 : ℝ) T) t := by
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (K + 1))),
        HasDerivWithinAt
          (fun s ↦ regularity.coefficient s j i *
            ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ))
          (regularity.timeDerivativeCoefficient t j i *
            ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ))
          (Set.Icc (0 : ℝ) T) t := by
      intro i hi
      exact (regularity.coefficient_hasDerivWithinAt j i t ht).mul_const _
    have hraw := HasDerivWithinAt.sum hterm
    have hfun :
        (fun s ↦ ∑ i : Fin (K + 1), regularity.coefficient s j i *
          ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ)) =
        ∑ i : Fin (K + 1), (fun s ↦ regularity.coefficient s j i *
          ((x - cellLeft mesh j) / cellLength mesh j) ^ (i : ℕ)) := by
      funext s
      simp
    rw [hfun]
    exact hraw
  rw [regularity.timeDerivativeValue_eq t ht j x hx]
  apply hsum.congr
  · intro s hs
    exact regularity.value_eq s hs j x hx
  · exact regularity.value_eq t ht j x hx

/-- The semidiscrete upwind DG method (2), with the usual finite-dimensional `C¹` coefficient
trajectory made explicit. -/
def IsSemiDiscreteUpwindDG (K : ℕ) (a T : ℝ) {N : ℕ}
    (mesh : PeriodicMesh N) (uh : DGTrajectory N) : Prop :=
  ∃ uht : DGTrajectory N,
    ∃ _regularity : DGTrajectoryRegularity K mesh T uh uht,
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ φ : DGField N, IsDGField K mesh φ → ∀ j : Fin N,
        localDGForm a mesh uh uht φ j t = 0

/-- The projected initial-data condition `u_h(·,0) = Π_h u(·,0)`. -/
def HasGaussRadauInitialData (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    (u : ℝ → ℝ → ℝ) (uh : DGTrajectory N) : Prop :=
  IsLocalGaussRadauProjection K mesh (fun x ↦ u x 0) (uh 0)

/-- A time-dependent local Gauss--Radau projection of both `u` and its time derivative. -/
structure ProjectionTrajectory (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N)
    (T : ℝ) (solution : SmoothPeriodicAdvectionSolution K a T) where
  value : DGTrajectory N
  timeDerivativeValue : DGTrajectory N
  value_spec : ∀ t ∈ Set.Icc (0 : ℝ) T,
    IsLocalGaussRadauProjection K mesh (fun x ↦ solution.u x t) (value t)
  timeDerivative_spec : ∀ t ∈ Set.Icc (0 : ℝ) T,
    IsLocalGaussRadauProjection K mesh (fun x ↦ solution.ut x t)
      (timeDerivativeValue t)
  commutes_with_time_derivative : ∀ j : Fin N,
    ∀ x ∈ Set.Icc (cellLeft mesh j) (cellRight mesh j),
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s ↦ value s j x) (timeDerivativeValue t j x)
        (Set.Icc (0 : ℝ) T) t

end Exp1
