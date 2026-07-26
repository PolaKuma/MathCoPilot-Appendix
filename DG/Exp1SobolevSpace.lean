import Exp1GlobalL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos

open scoped ENNReal MeasureTheory Topology Interval BigOperators
open MeasureTheory Set Filter

noncomputable section

namespace Exp2

/-- Regard a test function supported in a smaller open set as a test function
in a larger open set.  The underlying smooth compactly supported function is
unchanged. -/
def testFunctionMonoOpen {Ω₁ Ω₂ : TopologicalSpace.Opens ℝ}
    (hΩ : (Ω₁ : Set ℝ) ⊆ (Ω₂ : Set ℝ))
    (φ : TestFunction Ω₁ ℝ ⊤) : TestFunction Ω₂ ℝ ⊤ where
  toFun := φ
  contDiff' := φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport
  tsupport_subset' := φ.tsupport_subset.trans hΩ

@[simp] theorem testFunctionMonoOpen_apply
    {Ω₁ Ω₂ : TopologicalSpace.Opens ℝ}
    (hΩ : (Ω₁ : Set ℝ) ⊆ (Ω₂ : Set ℝ))
    (φ : TestFunction Ω₁ ℝ ⊤) (x : ℝ) :
    testFunctionMonoOpen hΩ φ x = φ x := rfl

/-- An integral whose integrand is supported in a smaller open set is
unchanged when the ambient restricted measure is enlarged. -/
theorem integral_restrict_eq_of_tsupport_subset
    {Ω₁ Ω₂ : TopologicalSpace.Opens ℝ}
    (hΩ : (Ω₁ : Set ℝ) ⊆ (Ω₂ : Set ℝ))
    {F : ℝ → ℝ} (hF : Function.support F ⊆ (Ω₁ : Set ℝ)) :
    (∫ x, F x ∂(volume.restrict (Ω₁ : Set ℝ))) =
      ∫ x, F x ∂(volume.restrict (Ω₂ : Set ℝ)) := by
  calc
    _ = ∫ x, (Ω₁ : Set ℝ).indicator F x ∂volume :=
      (integral_indicator (μ := volume) Ω₁.2.measurableSet).symm
    _ = ∫ x, (Ω₂ : Set ℝ).indicator F x ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx₁ : x ∈ (Ω₁ : Set ℝ)
      · have hx₂ := hΩ hx₁
        simp [hx₁, hx₂]
      · have hFx : F x = 0 := by
          by_contra hne
          exact hx₁ (hF hne)
        by_cases hx₂ : x ∈ (Ω₂ : Set ℝ)
        · simp [Set.indicator, hx₁, hx₂, hFx]
        · simp [Set.indicator, hx₁, hx₂]
    _ = _ := integral_indicator (μ := volume) Ω₂.2.measurableSet

/-- Distributional weak derivatives are local: restriction from a larger
open interval to a smaller one preserves the weak-derivative relation. -/
theorem WeakDerivativeOn.mono_open
    {Ω₁ Ω₂ : TopologicalSpace.Opens ℝ}
    (hΩ : (Ω₁ : Set ℝ) ⊆ (Ω₂ : Set ℝ))
    {f g : ℝ → ℝ} (hfg : WeakDerivativeOn Ω₂ f g) :
    WeakDerivativeOn Ω₁ f g := by
  intro φ
  let ψ : TestFunction Ω₂ ℝ ⊤ := testFunctionMonoOpen hΩ φ
  have hweak := hfg ψ
  have hleftSupport :
      Function.support (fun x ↦ f x * deriv φ x) ⊆ (Ω₁ : Set ℝ) := by
    intro x hx
    have hderiv : deriv φ x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    exact φ.tsupport_subset (support_deriv_subset hderiv)
  have hrightSupport :
      Function.support (fun x ↦ g x * φ x) ⊆ (Ω₁ : Set ℝ) := by
    intro x hx
    have hφ : φ x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  have hleft := integral_restrict_eq_of_tsupport_subset hΩ hleftSupport
  have hright := integral_restrict_eq_of_tsupport_subset hΩ hrightSupport
  simpa [ψ, WeakDerivativeOn, hleft, hright] using hweak

/-- Weak derivatives on an arbitrary open set are invariant under changing
both representatives almost everywhere. -/
theorem WeakDerivativeOn.congr_ae {Ω : TopologicalSpace.Opens ℝ}
    {f f' g g' : ℝ → ℝ} (hfg : WeakDerivativeOn Ω f g)
    (hff' : f =ᵐ[volume.restrict (Ω : Set ℝ)] f')
    (hgg' : g =ᵐ[volume.restrict (Ω : Set ℝ)] g') :
    WeakDerivativeOn Ω f' g' := by
  intro φ
  calc
    (∫ x, f' x * deriv φ x ∂(volume.restrict (Ω : Set ℝ))) =
        ∫ x, f x * deriv φ x ∂(volume.restrict (Ω : Set ℝ)) := by
          apply integral_congr_ae
          filter_upwards [hff'] with x hx
          rw [hx]
    _ = -(∫ x, g x * φ x ∂(volume.restrict (Ω : Set ℝ))) := hfg φ
    _ = -(∫ x, g' x * φ x ∂(volume.restrict (Ω : Set ℝ))) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hgg'] with x hx
          rw [hx]

end Exp2

namespace Exp1

/-- The complete global integer-order Sobolev space `Hⁿ(0,1)`, represented
by Mathlib `L²` equivalence classes and distributional weak derivatives. -/
abbrev GlobalSobolev (n : ℕ) := Exp2.StandardSobolevOnReference n

/-- The complete broken Sobolev space on a periodic mesh:
one standard Sobolev class on every open cell, with no continuity imposed
across interfaces. -/
abbrev BrokenSobolev {N : ℕ} (n : ℕ) (mesh : PeriodicMesh N) :=
  ∀ j : Fin N,
    Exp2.StandardSobolevOnCell n (cellLeft mesh j) (cellLength mesh j)

/-- The complete discontinuous finite-element space `U_h^K`, packaged as a
type rather than an ambient function plus a side predicate. -/
def DGSpace (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N) :=
  {v : DGField N // IsDGField K mesh v}

/-- A semidiscrete trajectory whose values on the physical time interval are
elements of the complete DG space.  No condition is imposed outside `[0,T]`,
matching the interval-local regularity in the PDF and in
`DGTrajectoryRegularity`. -/
def DGSpaceTrajectory (K : ℕ) {N : ℕ} (mesh : PeriodicMesh N) (T : ℝ) :=
  {uh : DGTrajectory N //
    ∀ t ∈ Set.Icc (0 : ℝ) T, IsDGField K mesh (uh t)}

/-- Evaluate a typed DG trajectory at a time in `[0,T]`. -/
def DGSpaceTrajectory.at {K N : ℕ} {mesh : PeriodicMesh N} {T : ℝ}
    (uh : DGSpaceTrajectory K mesh T) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) : DGSpace K mesh :=
  ⟨uh.1 t, uh.2 t ht⟩

/-- The upwind scheme as a predicate on trajectories valued in the complete
DG space on `[0,T]`. -/
def IsSemiDiscreteUpwindDGSpace (K : ℕ) (a T : ℝ) {N : ℕ}
    (mesh : PeriodicMesh N) (uh : DGSpaceTrajectory K mesh T) : Prop :=
  IsSemiDiscreteUpwindDG K a T mesh uh.1

/-- The projected initial condition as a predicate on a typed DG trajectory. -/
def HasGaussRadauInitialDataSpace (K : ℕ) {N : ℕ}
    (mesh : PeriodicMesh N) {T : ℝ} (u : ℝ → ℝ → ℝ)
    (uh : DGSpaceTrajectory K mesh T) : Prop :=
  HasGaussRadauInitialData K mesh u uh.1

theorem isSemiDiscreteUpwindDGSpace_iff
    {K N : ℕ} {a T : ℝ} {mesh : PeriodicMesh N}
    (uh : DGSpaceTrajectory K mesh T) :
    IsSemiDiscreteUpwindDGSpace K a T mesh uh ↔
      IsSemiDiscreteUpwindDG K a T mesh uh.1 :=
  Iff.rfl

/-- The old ambient-function presentation and the complete-type presentation
describe exactly the same semidiscrete solutions. -/
theorem isSemiDiscreteUpwindDG_iff_exists_DGSpaceTrajectory
    {K N : ℕ} {a T : ℝ} {mesh : PeriodicMesh N}
    (uh : DGTrajectory N) :
    IsSemiDiscreteUpwindDG K a T mesh uh ↔
      ∃ uhSpace : DGSpaceTrajectory K mesh T,
        uhSpace.1 = uh ∧
          IsSemiDiscreteUpwindDGSpace K a T mesh uhSpace := by
  constructor
  · rintro ⟨uht, regularity, hscheme⟩
    let uhSpace : DGSpaceTrajectory K mesh T :=
      ⟨uh, fun t ht ↦ regularity.value_isDGField t ht⟩
    exact ⟨uhSpace, rfl, ⟨uht, regularity, hscheme⟩⟩
  · rintro ⟨uhSpace, hvalue, hscheme⟩
    rw [← hvalue]
    exact hscheme

/-- Every discrete DG function is canonically an element of the complete
broken `L² = H⁰` space used by the energy estimate. -/
def DGSpace.toBrokenL2 {K N : ℕ} {mesh : PeriodicMesh N}
    (v : DGSpace K mesh) : BrokenSobolev 0 mesh :=
  fun j ↦
    { derivative := fun _ ↦
        (dgField_memLp mesh v.1 v.2 j).toLp (v.1 j)
      weakDerivative_succ := by
        intro r hr
        omega }

theorem DGSpace.toBrokenL2_zero_ae {K N : ℕ}
    {mesh : PeriodicMesh N} (v : DGSpace K mesh) (j : Fin N) :
    ((v.toBrokenL2 j).derivative ⟨0, by omega⟩ : ℝ → ℝ)
      =ᵐ[volume.restrict (meshCell mesh j : Set ℝ)] v.1 j :=
  (dgField_memLp mesh v.1 v.2 j).coeFn_toLp

theorem meshCell_subset_reference {N : ℕ} (mesh : PeriodicMesh N)
    (j : Fin N) :
    (meshCell mesh j : Set ℝ) ⊆ (Exp2.referenceCell : Set ℝ) :=
  by
    simpa [Exp2.referenceCell, Exp2.cell] using meshCell_subset_unit mesh j

/-- Restrict a global Sobolev class to one mesh cell. -/
def GlobalSobolev.restrictCell {n N : ℕ} (w : GlobalSobolev n)
    (mesh : PeriodicMesh N) (j : Fin N) :
    Exp2.StandardSobolevOnCell n (cellLeft mesh j) (cellLength mesh j) where
  derivative := fun r ↦
    let f : ℝ → ℝ := w.derivativeFn r
    let hf : MemLp f 2 (volume.restrict (Exp2.referenceCell : Set ℝ)) :=
      w.derivativeFn_memLp (by omega)
    let hμ :
        volume.restrict (meshCell mesh j : Set ℝ) ≤
          volume.restrict (Exp2.referenceCell : Set ℝ) :=
      Measure.restrict_mono_set volume (meshCell_subset_reference mesh j)
    (hf.mono_measure hμ).toLp f
  weakDerivative_succ := by
    intro r hr
    dsimp
    apply ((w.derivativeFn_weakDerivative_succ hr).mono_open
      (meshCell_subset_reference mesh j)).congr_ae
    · exact
        (w.derivativeFn_memLp (j := r) (Nat.le_of_lt hr)
          |>.mono_measure
            (Measure.restrict_mono_set volume
              (meshCell_subset_reference mesh j))).coeFn_toLp.symm
    · exact
        (w.derivativeFn_memLp (j := r + 1) (Nat.succ_le_of_lt hr)
          |>.mono_measure
            (Measure.restrict_mono_set volume
              (meshCell_subset_reference mesh j))).coeFn_toLp.symm

/-- Restriction to every cell gives the canonical embedding from the global
Sobolev space into the complete broken Sobolev space. -/
def GlobalSobolev.toBroken {n N : ℕ} (w : GlobalSobolev n)
    (mesh : PeriodicMesh N) : BrokenSobolev n mesh :=
  fun j ↦ w.restrictCell mesh j

/-- The sum of the cell-restricted Lebesgue measures is dominated by the
global measure on `(0,1)`.  No mesh-covering assumption is hidden here:
pairwise disjointness and cell inclusion are sufficient. -/
theorem sum_cell_restrict_le_reference {N : ℕ} (mesh : PeriodicMesh N) :
    (∑ j : Fin N, volume.restrict (meshCell mesh j : Set ℝ)) ≤
      volume.restrict (Exp2.referenceCell : Set ℝ) := by
  classical
  let U : Set ℝ := ⋃ j : Fin N, (meshCell mesh j : Set ℝ)
  have hrestrict :
      volume.restrict U =
        Measure.sum fun j : Fin N ↦
          volume.restrict (meshCell mesh j : Set ℝ) := by
    exact Measure.restrict_iUnion (meshCells_pairwiseDisjoint mesh)
      (fun j ↦ (meshCell mesh j).2.measurableSet)
  have hU : U ⊆ (Exp2.referenceCell : Set ℝ) := by
    intro x hx
    simp only [U, Set.mem_iUnion] at hx
    obtain ⟨j, hxj⟩ := hx
    exact meshCell_subset_reference mesh j hxj
  calc
    (∑ j : Fin N, volume.restrict (meshCell mesh j : Set ℝ)) =
        Measure.sum fun j : Fin N ↦
          volume.restrict (meshCell mesh j : Set ℝ) := by
      rw [Measure.sum_fintype]
    _ = volume.restrict U := hrestrict.symm
    _ ≤ volume.restrict (Exp2.referenceCell : Set ℝ) :=
      Measure.restrict_mono_set volume hU

theorem GlobalSobolev.restrictCell_seminorm_eq {n N : ℕ}
    (w : GlobalSobolev n) (mesh : PeriodicMesh N) (j : Fin N) :
    (w.restrictCell mesh j).seminorm =
      Exp2.l2NormOn (meshCell mesh j) (w.derivativeFn n) := by
  let f : ℝ → ℝ := w.derivativeFn n
  let hf : MemLp f 2 (volume.restrict (Exp2.referenceCell : Set ℝ)) :=
    w.derivativeFn_memLp le_rfl
  let hμ :
      volume.restrict (meshCell mesh j : Set ℝ) ≤
        volume.restrict (Exp2.referenceCell : Set ℝ) :=
    Measure.restrict_mono_set volume (meshCell_subset_reference mesh j)
  change ‖(hf.mono_measure hμ).toLp f‖ =
    (eLpNorm f 2 (volume.restrict (meshCell mesh j : Set ℝ))).toReal
  exact Lp.norm_toLp f (hf.mono_measure hμ)

/-- Exact analytic control needed by DG: the broken top-order seminorm of
the restrictions is bounded by the global Sobolev seminorm. -/
theorem GlobalSobolev.broken_seminorm_le {n N : ℕ}
    (w : GlobalSobolev n) (mesh : PeriodicMesh N) :
    Real.sqrt
        (∑ j : Fin N, ((w.restrictCell mesh j).seminorm) ^ 2) ≤
      ‖w.derivative ⟨n, by omega⟩‖ := by
  classical
  let f : ℝ → ℝ := w.derivativeFn n
  let μ : Measure ℝ := volume.restrict (Exp2.referenceCell : Set ℝ)
  let μcell : Fin N → Measure ℝ :=
    fun j ↦ volume.restrict (meshCell mesh j : Set ℝ)
  have hf : MemLp f 2 μ := w.derivativeFn_memLp le_rfl
  have hfInt : Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hfCell : ∀ j : Fin N, MemLp f 2 (μcell j) := by
    intro j
    exact hf.mono_measure
      (Measure.restrict_mono_set volume (meshCell_subset_reference mesh j))
  have hfCellInt : ∀ j : Fin N, Integrable (fun x ↦ ‖f x‖ ^ 2) (μcell j) := by
    intro j
    exact
      (memLp_two_iff_integrable_sq_norm (hfCell j).aestronglyMeasurable).1
        (hfCell j)
  have hmeasure : (∑ j : Fin N, μcell j) ≤ μ := by
    exact sum_cell_restrict_le_reference mesh
  have hmono :
      (∫ x, ‖f x‖ ^ 2 ∂(∑ j : Fin N, μcell j)) ≤
        ∫ x, ‖f x‖ ^ 2 ∂μ :=
    integral_mono_measure hmeasure
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖f x‖) hfInt
  have hsum :
      (∫ x, ‖f x‖ ^ 2 ∂(∑ j : Fin N, μcell j)) =
        ∑ j : Fin N, ∫ x, ‖f x‖ ^ 2 ∂(μcell j) := by
    simpa using
      (integral_finset_sum_measure
        (s := (Finset.univ : Finset (Fin N)))
        (fun j _ ↦ hfCellInt j))
  rw [hsum] at hmono
  have hcellSq : ∀ j : Fin N,
      ((w.restrictCell mesh j).seminorm) ^ 2 =
        ∫ x, ‖f x‖ ^ 2 ∂(μcell j) := by
    intro j
    rw [w.restrictCell_seminorm_eq mesh j,
      Exp2.l2NormOn_eq_sqrt_integral_sq (hfCell j)]
    exact Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg ‖f x‖)
  have hglobalSq :
      ‖w.derivative ⟨n, by omega⟩‖ ^ 2 =
        ∫ x, ‖f x‖ ^ 2 ∂μ := by
    have hfn :
        f = (w.derivative ⟨n, by omega⟩ : ℝ → ℝ) :=
      w.derivativeFn_eq le_rfl
    rw [Lp.norm_def]
    change (eLpNorm (w.derivative ⟨n, by omega⟩ : ℝ → ℝ) 2 μ).toReal ^ 2 =
      _
    rw [← hfn]
    have hnorm :
        (eLpNorm f 2 μ).toReal =
          Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
      simpa [μ, Exp2.l2NormOn] using
        (Exp2.l2NormOn_eq_sqrt_integral_sq hf)
    rw [hnorm]
    exact Real.sq_sqrt (integral_nonneg fun x ↦ sq_nonneg ‖f x‖)
  have hsquares :
      (∑ j : Fin N, ((w.restrictCell mesh j).seminorm) ^ 2) ≤
        ‖w.derivative ⟨n, by omega⟩‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ ↦ hcellSq j), hglobalSq]
    exact hmono
  calc
    Real.sqrt (∑ j : Fin N, ((w.restrictCell mesh j).seminorm) ^ 2) ≤
        Real.sqrt (‖w.derivative ⟨n, by omega⟩‖ ^ 2) :=
      Real.sqrt_le_sqrt hsquares
    _ = ‖w.derivative ⟨n, by omega⟩‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- A continuous representative of the zeroth global Sobolev class induces
a concrete Sobolev representative on every cell.  Higher derivatives are
not assumed pointwise: they remain the original `L²` representatives. -/
def GlobalSobolev.toConcreteCell {n N : ℕ} (w : GlobalSobolev n)
    (mesh : PeriodicMesh N) (j : Fin N) (f : ℝ → ℝ)
    (hfcont : ContinuousOn f
      (Set.Icc (cellLeft mesh j) (cellRight mesh j)))
    (hfae : w.derivativeFn 0
      =ᵐ[volume.restrict (Exp2.referenceCell : Set ℝ)] f) :
    Exp2.SobolevMapOn n (meshCell mesh j) where
  toFun := f
  derivative := fun r ↦ if r = 0 then f else w.derivativeFn r
  derivative_zero := by simp
  continuousOn := by
    have hlt : cellLeft mesh j < cellRight mesh j :=
      sub_pos.mp (cellLength_pos mesh j)
    change ContinuousOn f
      (closure (Set.Ioo (cellLeft mesh j)
        (cellLeft mesh j + cellLength mesh j)))
    have heq :
        cellLeft mesh j + cellLength mesh j = cellRight mesh j := by
      simp [cellLength]
    rw [heq, closure_Ioo hlt.ne]
    exact hfcont
  memLp_derivative := by
    intro r hr
    have hμ :
        volume.restrict (meshCell mesh j : Set ℝ) ≤
          volume.restrict (Exp2.referenceCell : Set ℝ) :=
      Measure.restrict_mono_set volume (meshCell_subset_reference mesh j)
    have hbase := (w.derivativeFn_memLp hr).mono_measure hμ
    by_cases hzero : r = 0
    · subst r
      simp only [if_pos]
      exact MemLp.ae_eq
        (ae_restrict_of_ae_restrict_of_subset
          (meshCell_subset_reference mesh j) hfae) hbase
    · simp [hzero]
      exact hbase
  weakDerivative_succ := by
    intro r hr
    have hraw :=
      (w.derivativeFn_weakDerivative_succ hr).mono_open
        (meshCell_subset_reference mesh j)
    by_cases hzero : r = 0
    · subst r
      simp only [if_pos, Nat.zero_add, Nat.one_ne_zero, if_false]
      exact hraw.congr_ae
        (ae_restrict_of_ae_restrict_of_subset
          (meshCell_subset_reference mesh j) hfae)
        Filter.EventuallyEq.rfl
    · have hsucc : r + 1 ≠ 0 := by omega
      simpa [hzero, hsucc] using hraw

theorem GlobalSobolev.toConcreteCell_apply {n N : ℕ}
    (w : GlobalSobolev n) (mesh : PeriodicMesh N) (j : Fin N)
    (f : ℝ → ℝ)
    (hfcont : ContinuousOn f
      (Set.Icc (cellLeft mesh j) (cellRight mesh j)))
    (hfae : w.derivativeFn 0
      =ᵐ[volume.restrict (Exp2.referenceCell : Set ℝ)] f)
    (x : ℝ) :
    w.toConcreteCell mesh j f hfcont hfae x = f x := rfl

theorem GlobalSobolev.toConcreteCell_seminorm_eq {n N : ℕ}
    (hn : 0 < n) (w : GlobalSobolev n)
    (mesh : PeriodicMesh N) (j : Fin N) (f : ℝ → ℝ)
    (hfcont : ContinuousOn f
      (Set.Icc (cellLeft mesh j) (cellRight mesh j)))
    (hfae : w.derivativeFn 0
      =ᵐ[volume.restrict (Exp2.referenceCell : Set ℝ)] f) :
    Exp2.sobolevSeminorm
        (w.toConcreteCell mesh j f hfcont hfae) =
      (w.restrictCell mesh j).seminorm := by
  rw [Exp2.sobolevSeminorm, w.restrictCell_seminorm_eq mesh j]
  unfold Exp2.l2NormOn
  change
    (eLpNorm (if n = 0 then f else w.derivativeFn n) 2
      (volume.restrict (meshCell mesh j : Set ℝ))).toReal =
      (eLpNorm (w.derivativeFn n) 2
        (volume.restrict (meshCell mesh j : Set ℝ))).toReal
  simp [hn.ne']

/-- The original theorem's “sufficiently smooth periodic solution”, now
stated with one global standard Sobolev class at each time.  In contrast with
`SmoothPeriodicAdvectionSolution`, this structure contains no mesh, cell,
local representative, projection estimate, or broken-norm assumption.

The classical derivative fields express the PDF's smooth PDE solution.
The two global `H^(K+1)` trajectories are exactly the spatial regularity used
for the Gauss--Radau estimates for `u` and `u_t`. -/
structure SobolevPeriodicAdvectionSolution (K : ℕ) (a T : ℝ) where
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
  uSobolev : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
    GlobalSobolev (K + 1)
  utSobolev : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
    GlobalSobolev (K + 1)
  uSobolev_zero_ae : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T),
    (uSobolev t ht).derivativeFn 0
      =ᵐ[volume.restrict (Exp2.referenceCell : Set ℝ)] fun x ↦ u x t
  utSobolev_zero_ae : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T),
    (utSobolev t ht).derivativeFn 0
      =ᵐ[volume.restrict (Exp2.referenceCell : Set ℝ)] fun x ↦ ut x t
  uniformSobolevRegularity : ∃ M : ℝ, 0 ≤ M ∧
    ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T),
      ‖(uSobolev t ht).derivative
        ⟨K + 1, by omega⟩‖ ≤ M ∧
      ‖(utSobolev t ht).derivative
        ⟨K + 1, by omega⟩‖ ≤ M

namespace SobolevPeriodicAdvectionSolution

theorem u_continuous (solution : SobolevPeriodicAdvectionSolution K a T)
    (t : ℝ) : Continuous (fun x ↦ solution.u x t) := by
  simpa [Function.uncurry] using solution.u_joint_continuous.comp
    (continuous_id.prodMk continuous_const)

theorem ut_continuous (solution : SobolevPeriodicAdvectionSolution K a T)
    (t : ℝ) : Continuous (fun x ↦ solution.ut x t) := by
  simpa [Function.uncurry] using solution.ut_joint_continuous.comp
    (continuous_id.prodMk continuous_const)

/-- Derive the former mesh-indexed implementation record from the standard
global Sobolev assumptions.  This theorem is the semantic bridge: all local
Sobolev data and all mesh-uniform bounds are proved rather than assumed. -/
def toConcreteSolution
    (solution : SobolevPeriodicAdvectionSolution K a T) :
    SmoothPeriodicAdvectionSolution K a T where
  u := solution.u
  ut := solution.ut
  ux := solution.ux
  u_joint_continuous := solution.u_joint_continuous
  ut_joint_continuous := solution.ut_joint_continuous
  timeDerivative := solution.timeDerivative
  spaceDerivative := solution.spaceDerivative
  advectionEquation := solution.advectionEquation
  periodic := solution.periodic
  uCell := fun mesh j t ↦
    if ht : t ∈ Set.Icc (0 : ℝ) T then
      (solution.uSobolev t ht).toConcreteCell mesh j
        (fun x ↦ solution.u x t)
        (solution.u_continuous t).continuousOn
        (solution.uSobolev_zero_ae t ht)
    else 0
  utCell := fun mesh j t ↦
    if ht : t ∈ Set.Icc (0 : ℝ) T then
      (solution.utSobolev t ht).toConcreteCell mesh j
        (fun x ↦ solution.ut x t)
        (solution.ut_continuous t).continuousOn
        (solution.utSobolev_zero_ae t ht)
    else 0
  uCell_eq := by
    intro N mesh j t ht x hx
    simp only [ht, ↓reduceDIte]
    rfl
  utCell_eq := by
    intro N mesh j t ht x hx
    simp only [ht, ↓reduceDIte]
    rfl
  uniformRegularity := by
    obtain ⟨M, hM, hreg⟩ := solution.uniformSobolevRegularity
    refine ⟨M, hM, ?_⟩
    intro N mesh t ht
    constructor
    · simp only [ht, ↓reduceDIte]
      calc
        Real.sqrt (∑ j : Fin N,
            (Exp2.sobolevSeminorm
              ((solution.uSobolev t ht).toConcreteCell mesh j
                (fun x ↦ solution.u x t)
                (solution.u_continuous t).continuousOn
                (solution.uSobolev_zero_ae t ht))) ^ 2) =
            Real.sqrt (∑ j : Fin N,
              (((solution.uSobolev t ht).restrictCell mesh j).seminorm) ^ 2) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [GlobalSobolev.toConcreteCell_seminorm_eq
            (Nat.succ_pos K) (solution.uSobolev t ht)]
        _ ≤ ‖(solution.uSobolev t ht).derivative ⟨K + 1, by omega⟩‖ :=
          (solution.uSobolev t ht).broken_seminorm_le mesh
        _ ≤ M := (hreg t ht).1
    · simp only [ht, ↓reduceDIte]
      calc
        Real.sqrt (∑ j : Fin N,
            (Exp2.sobolevSeminorm
              ((solution.utSobolev t ht).toConcreteCell mesh j
                (fun x ↦ solution.ut x t)
                (solution.ut_continuous t).continuousOn
                (solution.utSobolev_zero_ae t ht))) ^ 2) =
            Real.sqrt (∑ j : Fin N,
              (((solution.utSobolev t ht).restrictCell mesh j).seminorm) ^ 2) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [GlobalSobolev.toConcreteCell_seminorm_eq
            (Nat.succ_pos K) (solution.utSobolev t ht)]
        _ ≤ ‖(solution.utSobolev t ht).derivative ⟨K + 1, by omega⟩‖ :=
          (solution.utSobolev t ht).broken_seminorm_le mesh
        _ ≤ M := (hreg t ht).2

end SobolevPeriodicAdvectionSolution

/-- Exp.1 exactly over the complete global Sobolev space, with no
mesh-indexed regularity assumptions. -/
theorem sobolev_global_main_theorem (K : ℕ) {a ρ : ℝ}
    (ha : 0 < a) (hρ : 1 ≤ ρ) :
    ∀ T : ℝ, 0 < T →
      ∀ solution : SobolevPeriodicAdvectionSolution K a T,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ {N : ℕ} (mesh : PeriodicMesh N), IsQuasiUniform ρ mesh →
          ∀ uh : DGTrajectory N,
            IsSemiDiscreteUpwindDG K a T mesh uh →
            HasGaussRadauInitialData K mesh solution.u uh →
            Exp2.l2NormOn Exp2.referenceCell
                (assembleGlobal mesh
                  (fun j x ↦ solution.u x T - uh T j x)) ≤
              C * mesh.meshSize ^ (K + 1) := by
  intro T hT solution
  simpa [SobolevPeriodicAdvectionSolution.toConcreteSolution] using
    (global_main_theorem K ha hρ T hT solution.toConcreteSolution)

/-- Exp.1 with the semidiscrete unknown quantified as a trajectory in the
complete DG space, rather than as an ambient broken function plus a side
predicate.  This is equivalent to `sobolev_global_main_theorem`. -/
theorem sobolev_global_main_theorem_DGSpace (K : ℕ) {a ρ : ℝ}
    (ha : 0 < a) (hρ : 1 ≤ ρ) :
    ∀ T : ℝ, ∀ hT : 0 < T,
      ∀ solution : SobolevPeriodicAdvectionSolution K a T,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ {N : ℕ} (mesh : PeriodicMesh N), IsQuasiUniform ρ mesh →
          ∀ uh : DGSpaceTrajectory K mesh T,
            IsSemiDiscreteUpwindDGSpace K a T mesh uh →
            HasGaussRadauInitialDataSpace K mesh solution.u uh →
            Exp2.l2NormOn Exp2.referenceCell
                (assembleGlobal mesh
                  (fun j x ↦ solution.u x T -
                    (uh.at T ⟨hT.le, le_rfl⟩).1 j x)) ≤
              C * mesh.meshSize ^ (K + 1) := by
  intro T hT solution
  obtain ⟨C, hC, hestimate⟩ :=
    sobolev_global_main_theorem K ha hρ T hT solution
  refine ⟨C, hC, ?_⟩
  intro N mesh hmesh uh huh hinitial
  simpa [DGSpaceTrajectory.at] using
    hestimate mesh hmesh uh.1 huh hinitial

end Exp1
