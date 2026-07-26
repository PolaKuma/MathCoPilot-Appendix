import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Exp2AffineMeasure

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set Filter

noncomputable section

namespace Exp2

/-- The open physical cell `(a, a + h)`.  The reference cell is `cell 0 1`. -/
def cell (a h : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo a (a + h), isOpen_Ioo⟩

/-- The reference interval `I-hat = (0,1)`. -/
abbrev referenceCell : TopologicalSpace.Opens ℝ := cell 0 1

/-- `g` is the distributional derivative of `f` on `Ω`, tested against smooth compactly
supported real-valued functions on `Ω`. -/
def WeakDerivativeOn (Ω : TopologicalSpace.Opens ℝ) (f g : ℝ → ℝ) : Prop :=
  ∀ φ : TestFunction Ω ℝ ⊤,
    (∫ x, f x * deriv φ x ∂(volume.restrict (Ω : Set ℝ))) =
      -(∫ x, g x * φ x ∂(volume.restrict (Ω : Set ℝ)))

/-- A concrete representative of an integer-order real Sobolev function on `Ω`.
The zeroth derivative is required to be continuous on `closure Ω`, fixing the endpoint trace
representative used by the Gauss--Radau condition. -/
structure SobolevMapOn (n : ℕ) (Ω : TopologicalSpace.Opens ℝ) where
  toFun : ℝ → ℝ
  derivative : ℕ → ℝ → ℝ
  derivative_zero : derivative 0 = toFun
  continuousOn : ContinuousOn toFun (closure (Ω : Set ℝ))
  memLp_derivative : ∀ j ≤ n, MemLp (derivative j) 2 (volume.restrict (Ω : Set ℝ))
  weakDerivative_succ : ∀ j < n, WeakDerivativeOn Ω (derivative j) (derivative (j + 1))

/- These two closure lemmas isolate the only analytic input needed to make the concrete
Sobolev representative type linear: sums and constant scalar multiples of weak derivatives are
weak derivatives.  Their proofs use `MemLp`/Hölder and linearity of the Bochner integral. -/
theorem WeakDerivativeOn.add_of_memLp
    {Ω : TopologicalSpace.Opens ℝ} {f₁ g₁ f₂ g₂ : ℝ → ℝ}
    (h₁ : WeakDerivativeOn Ω f₁ g₁) (h₂ : WeakDerivativeOn Ω f₂ g₂)
    (hf₁ : MemLp f₁ 2 (volume.restrict (Ω : Set ℝ)))
    (hg₁ : MemLp g₁ 2 (volume.restrict (Ω : Set ℝ)))
    (hf₂ : MemLp f₂ 2 (volume.restrict (Ω : Set ℝ)))
    (hg₂ : MemLp g₂ 2 (volume.restrict (Ω : Set ℝ))) :
    WeakDerivativeOn Ω (f₁ + f₂) (g₁ + g₂) := by
  intro φ
  let μ := volume.restrict (Ω : Set ℝ)
  have hφ : MemLp (φ : ℝ → ℝ) 2 μ :=
    φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hderivφ : MemLp (deriv φ) 2 μ :=
    (φ.contDiff.continuous_deriv (by simp)).memLp_of_hasCompactSupport
      φ.hasCompactSupport.deriv
  have hf₁φ : Integrable (f₁ * deriv φ) μ := hf₁.integrable_mul hderivφ
  have hf₂φ : Integrable (f₂ * deriv φ) μ := hf₂.integrable_mul hderivφ
  have hg₁φ : Integrable (g₁ * (φ : ℝ → ℝ)) μ := hg₁.integrable_mul hφ
  have hg₂φ : Integrable (g₂ * (φ : ℝ → ℝ)) μ := hg₂.integrable_mul hφ
  have hleft :
      (∫ x, f₁ x * deriv φ x + f₂ x * deriv φ x ∂μ) =
        (∫ x, f₁ x * deriv φ x ∂μ) + (∫ x, f₂ x * deriv φ x ∂μ) := by
    simpa only [Pi.add_apply, Pi.mul_apply] using integral_add hf₁φ hf₂φ
  have hright :
      (∫ x, g₁ x * φ x + g₂ x * φ x ∂μ) =
        (∫ x, g₁ x * φ x ∂μ) + (∫ x, g₂ x * φ x ∂μ) := by
    simpa only [Pi.add_apply, Pi.mul_apply] using integral_add hg₁φ hg₂φ
  change (∫ x, (f₁ x + f₂ x) * deriv φ x ∂μ) =
    -(∫ x, (g₁ x + g₂ x) * φ x ∂μ)
  simp_rw [add_mul]
  rw [hleft, hright, h₁ φ, h₂ φ]
  ring

theorem WeakDerivativeOn.const_smul
    {Ω : TopologicalSpace.Opens ℝ} (c : ℝ) {f g : ℝ → ℝ}
    (h : WeakDerivativeOn Ω f g) :
    WeakDerivativeOn Ω (c • f) (c • g) := by
  intro φ
  let μ := volume.restrict (Ω : Set ℝ)
  change (∫ x, (c * f x) * deriv φ x ∂μ) =
    -(∫ x, (c * g x) * φ x ∂μ)
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul, h φ]
  ring

instance {n : ℕ} {Ω : TopologicalSpace.Opens ℝ} :
    CoeFun (SobolevMapOn n Ω) (fun _ ↦ ℝ → ℝ) :=
  ⟨SobolevMapOn.toFun⟩

instance {n : ℕ} {Ω : TopologicalSpace.Opens ℝ} : Zero (SobolevMapOn n Ω) where
  zero :=
    { toFun := 0
      derivative := 0
      derivative_zero := by funext x; simp
      continuousOn := continuousOn_const
      memLp_derivative := by
        intro j hj
        exact MemLp.zero
      weakDerivative_succ := by
        intro j hj φ
        simp }

instance {n : ℕ} {Ω : TopologicalSpace.Opens ℝ} : Add (SobolevMapOn n Ω) where
  add u v :=
    { toFun := u.toFun + v.toFun
      derivative := u.derivative + v.derivative
      derivative_zero := by
        funext x
        simp [u.derivative_zero, v.derivative_zero]
      continuousOn := u.continuousOn.add v.continuousOn
      memLp_derivative := by
        intro j hj
        exact MemLp.add (u.memLp_derivative j hj) (v.memLp_derivative j hj)
      weakDerivative_succ := by
        intro j hj
        exact WeakDerivativeOn.add_of_memLp
          (u.weakDerivative_succ j hj) (v.weakDerivative_succ j hj)
          (u.memLp_derivative j (Nat.le_of_lt hj))
          (u.memLp_derivative (j + 1) (Nat.succ_le_of_lt hj))
          (v.memLp_derivative j (Nat.le_of_lt hj))
          (v.memLp_derivative (j + 1) (Nat.succ_le_of_lt hj)) }

instance {n : ℕ} {Ω : TopologicalSpace.Opens ℝ} : Neg (SobolevMapOn n Ω) where
  neg u :=
    { toFun := -u.toFun
      derivative := -u.derivative
      derivative_zero := by
        funext x
        simp [u.derivative_zero]
      continuousOn := u.continuousOn.neg
      memLp_derivative := by
        intro j hj
        have h := (u.memLp_derivative j hj).const_smul (-1)
        change MemLp (fun x ↦ -u.derivative j x) 2 (volume.restrict (Ω : Set ℝ))
        simpa using h
      weakDerivative_succ := by
        intro j hj
        have h := WeakDerivativeOn.const_smul (-1) (u.weakDerivative_succ j hj)
        change WeakDerivativeOn Ω (fun x ↦ -u.derivative j x)
          (fun x ↦ -u.derivative (j + 1) x)
        simpa using h }

instance {n : ℕ} {Ω : TopologicalSpace.Opens ℝ} : SMul ℝ (SobolevMapOn n Ω) where
  smul c u :=
    { toFun := c • u.toFun
      derivative := c • u.derivative
      derivative_zero := by
        funext x
        simp [u.derivative_zero]
      continuousOn := u.continuousOn.const_smul c
      memLp_derivative := by
        intro j hj
        exact (u.memLp_derivative j hj).const_smul c
      weakDerivative_succ := by
        intro j hj
        exact WeakDerivativeOn.const_smul c (u.weakDerivative_succ j hj) }

@[ext] theorem SobolevMapOn.ext {n : ℕ} {Ω : TopologicalSpace.Opens ℝ}
    {u v : SobolevMapOn n Ω}
    (hFun : u.toFun = v.toFun) (hDeriv : u.derivative = v.derivative) : u = v := by
  cases u
  cases v
  simp_all

instance {n : ℕ} {Ω : TopologicalSpace.Opens ℝ} : AddCommGroup (SobolevMapOn n Ω) where
  add := (· + ·)
  add_assoc := by
    intro u v w
    apply SobolevMapOn.ext
    · funext x
      change (u.toFun x + v.toFun x) + w.toFun x = u.toFun x + (v.toFun x + w.toFun x)
      ring
    · funext j x
      change (u.derivative j x + v.derivative j x) + w.derivative j x =
        u.derivative j x + (v.derivative j x + w.derivative j x)
      ring
  zero := 0
  zero_add := by
    intro u
    apply SobolevMapOn.ext
    · funext x
      change (0 : ℝ) + u.toFun x = u.toFun x
      ring
    · funext j x
      change (0 : ℝ) + u.derivative j x = u.derivative j x
      ring
  add_zero := by
    intro u
    apply SobolevMapOn.ext
    · funext x
      change u.toFun x + (0 : ℝ) = u.toFun x
      ring
    · funext j x
      change u.derivative j x + (0 : ℝ) = u.derivative j x
      ring
  neg := Neg.neg
  neg_add_cancel := by
    intro u
    apply SobolevMapOn.ext
    · funext x
      change -u.toFun x + u.toFun x = 0
      ring
    · funext j x
      change -u.derivative j x + u.derivative j x = 0
      ring
  add_comm := by
    intro u v
    apply SobolevMapOn.ext
    · funext x
      change u.toFun x + v.toFun x = v.toFun x + u.toFun x
      ring
    · funext j x
      change u.derivative j x + v.derivative j x = v.derivative j x + u.derivative j x
      ring
  nsmul := nsmulRec
  nsmul_zero := by intro u; rfl
  nsmul_succ := by intro n u; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro u; rfl
  zsmul_succ' := by intro n u; rfl
  zsmul_neg' := by intro n u; rfl

instance {n : ℕ} {Ω : TopologicalSpace.Opens ℝ} : Module ℝ (SobolevMapOn n Ω) where
  one_smul := by
    intro u
    apply SobolevMapOn.ext
    · funext x
      change (1 : ℝ) • u.toFun x = u.toFun x
      simp
    · funext j x
      change (1 : ℝ) • u.derivative j x = u.derivative j x
      simp
  mul_smul := by
    intro a b u
    apply SobolevMapOn.ext
    · funext x
      change (a * b) • u.toFun x = a • b • u.toFun x
      simp only [smul_eq_mul]
      ring
    · funext j x
      change (a * b) • u.derivative j x = a • b • u.derivative j x
      simp only [smul_eq_mul]
      ring
  smul_zero := by
    intro c
    apply SobolevMapOn.ext
    · funext x
      change c • (0 : ℝ) = 0
      simp
    · funext j x
      change c • (0 : ℝ) = 0
      simp
  smul_add := by
    intro c u v
    apply SobolevMapOn.ext
    · funext x
      change c • (u.toFun x + v.toFun x) = c • u.toFun x + c • v.toFun x
      simp only [smul_eq_mul]
      ring
    · funext j x
      change c • (u.derivative j x + v.derivative j x) =
        c • u.derivative j x + c • v.derivative j x
      simp only [smul_eq_mul]
      ring
  add_smul := by
    intro a b u
    apply SobolevMapOn.ext
    · funext x
      change (a + b) • u.toFun x = a • u.toFun x + b • u.toFun x
      simp only [smul_eq_mul]
      ring
    · funext j x
      change (a + b) • u.derivative j x =
        a • u.derivative j x + b • u.derivative j x
      simp only [smul_eq_mul]
      ring
  zero_smul := by
    intro u
    apply SobolevMapOn.ext
    · funext x
      change (0 : ℝ) • u.toFun x = 0
      simp
    · funext j x
      change (0 : ℝ) • u.derivative j x = 0
      simp

/-- The real `L²(Ω)` norm, expressed through Mathlib's `eLpNorm`. -/
def l2NormOn (Ω : TopologicalSpace.Opens ℝ) (f : ℝ → ℝ) : ℝ :=
  (eLpNorm f 2 (volume.restrict (Ω : Set ℝ))).toReal

/-- The order-`n` Sobolev seminorm: the `L²` norm of the top weak derivative. -/
def sobolevSeminorm {n : ℕ} {Ω : TopologicalSpace.Opens ℝ}
    (w : SobolevMapOn n Ω) : ℝ :=
  l2NormOn Ω (w.derivative n)

/-- The standard integer-order `Hⁿ` norm, used only in the bounded-functional step. -/
def sobolevNorm {n : ℕ} {Ω : TopologicalSpace.Opens ℝ}
    (w : SobolevMapOn n Ω) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (n + 1), (l2NormOn Ω (w.derivative j)) ^ 2)

/-- Real polynomials of degree at most `k`, represented by Mathlib's linear submodule of
polynomials of degree strictly less than `k + 1`.  The equivalence with the original predicate
`natDegree p ≤ k` is `Polynomial.degreeLT_succ_eq_degreeLE`. -/
abbrev PolyLE (k : ℕ) := Polynomial.degreeLT ℝ (k + 1)

/-- Membership in the linear polynomial submodule is exactly the original degree bound. -/
theorem mem_PolyLE_iff {k : ℕ} {p : Polynomial ℝ} :
    p ∈ PolyLE k ↔ p.natDegree ≤ k := by
  change p ∈ Polynomial.degreeLT ℝ (k + 1) ↔ p.natDegree ≤ k
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE,
    Polynomial.natDegree_le_iff_degree_le]

/-- Evaluation of a real polynomial is continuous as a function of the evaluation point. -/
theorem polynomial_eval_continuous (p : Polynomial ℝ) :
    Continuous (fun x : ℝ ↦ p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa using hp.add hq
  | monomial n a =>
      simpa [Polynomial.eval_monomial] using
        (continuous_const.mul (continuous_id.pow n) :
          Continuous (fun x : ℝ ↦ a * x ^ n))

/-- Polynomial evaluation is integrable on the bounded reference interval. -/
theorem polynomial_eval_integrable_reference (p : Polynomial ℝ) :
    Integrable (fun x : ℝ ↦ p.eval x) (volume.restrict referenceCell) := by
  have hIcc : IntegrableOn (fun x : ℝ ↦ p.eval x) (Set.Icc 0 1) volume :=
    (polynomial_eval_continuous p).integrableOn_Icc
  apply hIcc.mono_set
  intro x hx
  exact ⟨le_of_lt hx.1, le_of_lt (by simpa using hx.2)⟩

/-- Equality on the open reference interval determines the right endpoint trace, because both
representatives are continuous up to the endpoint. -/
theorem SobolevMapOn.eq_eval_one_of_eqOn_reference {n : ℕ}
    (w : SobolevMapOn n referenceCell) (p : Polynomial ℝ)
    (hEq : ∀ x ∈ referenceCell, w x = p.eval x) : w 1 = p.eval 1 := by
  let x : ℕ → ℝ := fun m ↦ 1 - ((m : ℝ) + 2)⁻¹
  have hden : Tendsto (fun m : ℕ ↦ (m : ℝ) + 2) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hx : Tendsto x atTop (nhds 1) := by
    simpa [x] using tendsto_const_nhds.sub hinv
  have hxmem : ∀ m, x m ∈ referenceCell := by
    intro m
    change 0 < x m ∧ x m < 0 + 1
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hm : (1 : ℝ) < (m : ℝ) + 2 := by linarith
    have hdenpos : 0 < (m : ℝ) + 2 := by linarith
    have hinvlt : ((m : ℝ) + 2)⁻¹ < 1 := (inv_lt_one₀ hdenpos).2 hm
    have hinvpos : 0 < ((m : ℝ) + 2)⁻¹ := by positivity
    dsimp [x]
    constructor <;> norm_num <;> linarith
  have hclosure : closure (referenceCell : Set ℝ) = Set.Icc 0 1 := by
    change closure (Set.Ioo 0 (0 + 1)) = Set.Icc 0 1
    norm_num only [zero_add]
    exact closure_Ioo (by norm_num)
  have hxwithin : Tendsto x atTop (nhdsWithin 1 (closure (referenceCell : Set ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hx, Filter.Eventually.of_forall fun m ↦ by
      rw [hclosure]
      exact ⟨le_of_lt (hxmem m).1, by simpa using le_of_lt (hxmem m).2⟩⟩
  have hwAt : ContinuousWithinAt w.toFun (closure (referenceCell : Set ℝ)) 1 :=
    w.continuousOn 1 (by rw [hclosure]; exact ⟨zero_le_one, le_rfl⟩)
  have hw : Tendsto (fun m ↦ w (x m)) atTop (nhds (w 1)) :=
    hwAt.tendsto.comp hxwithin
  have hp : Tendsto (fun m ↦ p.eval (x m)) atTop (nhds (p.eval 1)) :=
    (polynomial_eval_continuous p).continuousAt.tendsto.comp hx
  have hw' : Tendsto (fun m ↦ w (x m)) atTop (nhds (p.eval 1)) := by
    convert hp using 1
    ext m
    exact hEq (x m) (hxmem m)
  exact tendsto_nhds_unique hw hw'

/-- The weighted square form used in the Radau moment system is strictly positive on every
nonzero polynomial. -/
theorem polynomial_weighted_sq_integral_pos {q : Polynomial ℝ} (hq : q ≠ 0) :
    0 < ∫ x, (1 - x) * (q.eval x) ^ 2 ∂(volume.restrict referenceCell) := by
  let roots : Set ℝ := {x | x ∈ q.roots}
  have hroots : roots.Finite := Multiset.finite_toSet q.roots
  have hdiff : (Set.Ioo (0 : ℝ) 1 \ roots).Infinite :=
    Set.Infinite.diff (Set.Ioo_infinite (by norm_num)) hroots
  obtain ⟨x, hxIoo, hxroot⟩ := hdiff.nonempty
  have hqx : q.eval x ≠ 0 := by
    intro hzero
    apply hxroot
    change x ∈ q.roots
    exact (Polynomial.mem_roots hq).2 hzero
  let f : ℝ → ℝ := fun y ↦ (1 - y) * (q.eval y) ^ 2
  have hfcont : Continuous f := by
    exact (continuous_const.sub continuous_id).mul ((polynomial_eval_continuous q).pow 2)
  have hfint : Integrable f (volume.restrict referenceCell) := by
    have hIcc : IntegrableOn f (Set.Icc 0 1) volume := hfcont.integrableOn_Icc
    apply hIcc.mono_set
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt (by simpa using hy.2)⟩
  have hfnonneg : 0 ≤ᵐ[volume.restrict (referenceCell : Set ℝ)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    dsimp [f]
    have hy1 : 0 ≤ 1 - y := sub_nonneg.mpr (le_of_lt (by simpa using hy.2))
    positivity
  rw [integral_pos_iff_support_of_nonneg_ae hfnonneg hfint]
  have hfx : f x ≠ 0 := by
    dsimp [f]
    exact mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hxIoo.2)) (pow_ne_zero 2 hqx)
  have hopen : IsOpen (Function.support f ∩ Set.Ioo (0 : ℝ) 1) :=
    hfcont.isOpen_support.inter isOpen_Ioo
  have hne : (Function.support f ∩ Set.Ioo (0 : ℝ) 1).Nonempty :=
    ⟨x, hfx, hxIoo⟩
  have hvol : 0 < volume (Function.support f ∩ Set.Ioo (0 : ℝ) 1) :=
    hopen.measure_pos volume hne
  have href : (referenceCell : Set ℝ) = Set.Ioo (0 : ℝ) 1 := by
    change Set.Ioo 0 (0 + 1) = Set.Ioo 0 1
    norm_num
  rw [href]
  rw [Measure.restrict_apply hfcont.isOpen_support.measurableSet]
  exact hvol

/-- Polynomials of degree strictly less than `k`, the moment-test space. -/
abbrev MomentPoly (k : ℕ) := Polynomial.degreeLT ℝ k

theorem polynomial_weighted_product_integrable (p q : Polynomial ℝ) :
    Integrable (fun x : ℝ ↦ (1 - x) * p.eval x * q.eval x)
      (volume.restrict referenceCell) := by
  have hc : Continuous (fun x : ℝ ↦ (1 - x) * p.eval x * q.eval x) :=
    ((continuous_const.sub continuous_id).mul (polynomial_eval_continuous p)).mul
      (polynomial_eval_continuous q)
  have hIcc : IntegrableOn (fun x : ℝ ↦ (1 - x) * p.eval x * q.eval x)
      (Set.Icc 0 1) volume := hc.integrableOn_Icc
  apply hIcc.mono_set
  intro x hx
  exact ⟨le_of_lt hx.1, le_of_lt (by simpa using hx.2)⟩

theorem polynomial_eval_memLp_reference (p : Polynomial ℝ) :
    MemLp (fun x : ℝ ↦ p.eval x) 2 (volume.restrict referenceCell) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ p.eval x)
      (volume.restrict referenceCell) :=
    (polynomial_eval_continuous p).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hc : Continuous (fun x : ℝ ↦ ‖p.eval x‖ ^ 2) :=
    (polynomial_eval_continuous p).norm.pow 2
  have hIcc : IntegrableOn (fun x : ℝ ↦ ‖p.eval x‖ ^ 2) (Set.Icc 0 1) volume :=
    hc.integrableOn_Icc
  apply hIcc.mono_set
  intro x hx
  exact ⟨le_of_lt hx.1, le_of_lt (by simpa using hx.2)⟩

/-- The finite-dimensional weighted moment map `r ↦ (v ↦ ∫(1-x)rv)`. -/
noncomputable def weightedMomentMap (k : ℕ) :
    MomentPoly k →ₗ[ℝ] Module.Dual ℝ (MomentPoly k) :=
  LinearMap.mk₂ ℝ
    (fun r v ↦ ∫ x, (1 - x) * r.1.eval x * v.1.eval x
      ∂(volume.restrict referenceCell))
    (by
      intro r s v
      have hr := polynomial_weighted_product_integrable r.1 v.1
      have hs := polynomial_weighted_product_integrable s.1 v.1
      rw [← integral_add hr hs]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Submodule.coe_add, Polynomial.eval_add]
      ring)
    (by
      intro c r v
      change (∫ x, (1 - x) * (c • r.1).eval x * v.1.eval x
        ∂(volume.restrict referenceCell)) = c •
          (∫ x, (1 - x) * r.1.eval x * v.1.eval x
            ∂(volume.restrict referenceCell))
      rw [show c • (∫ x, (1 - x) * r.1.eval x * v.1.eval x
          ∂(volume.restrict referenceCell)) =
          ∫ x, c * ((1 - x) * r.1.eval x * v.1.eval x)
            ∂(volume.restrict referenceCell) by
        simpa using (integral_const_mul c
          (fun x ↦ (1 - x) * r.1.eval x * v.1.eval x)
          (μ := volume.restrict referenceCell)).symm]
      apply integral_congr_ae
      filter_upwards with x
      simp [Polynomial.eval_smul]
      ring)
    (by
      intro r v s
      have hv := polynomial_weighted_product_integrable r.1 v.1
      have hs := polynomial_weighted_product_integrable r.1 s.1
      rw [← integral_add hv hs]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Submodule.coe_add, Polynomial.eval_add]
      ring)
    (by
      intro c r v
      change (∫ x, (1 - x) * r.1.eval x * (c • v.1).eval x
        ∂(volume.restrict referenceCell)) = c •
          (∫ x, (1 - x) * r.1.eval x * v.1.eval x
            ∂(volume.restrict referenceCell))
      rw [show c • (∫ x, (1 - x) * r.1.eval x * v.1.eval x
          ∂(volume.restrict referenceCell)) =
          ∫ x, c * ((1 - x) * r.1.eval x * v.1.eval x)
            ∂(volume.restrict referenceCell) by
        simpa using (integral_const_mul c
          (fun x ↦ (1 - x) * r.1.eval x * v.1.eval x)
          (μ := volume.restrict referenceCell)).symm]
      apply integral_congr_ae
      filter_upwards with x
      simp [Polynomial.eval_smul]
      ring)

theorem weightedMomentMap_injective (k : ℕ) :
    Function.Injective (weightedMomentMap k) := by
  intro r s hrs
  apply Subtype.ext
  by_contra hne
  have hdiff : (r.1 - s.1) ≠ 0 := by
    intro hzero
    apply hne
    exact sub_eq_zero.mp hzero
  have hpos := polynomial_weighted_sq_integral_pos hdiff
  have hout : weightedMomentMap k (r - s) = 0 := by
    rw [map_sub, hrs, sub_self]
  have hzero : weightedMomentMap k (r - s) (r - s) = 0 := by
    exact LinearMap.congr_fun hout (r - s)
  have heval : weightedMomentMap k (r - s) (r - s) =
      ∫ x, (1 - x) * ((r.1 - s.1).eval x) ^ 2
        ∂(volume.restrict referenceCell) := by
    apply integral_congr_ae
    filter_upwards with x
    simp
    ring
  rw [heval] at hzero
  linarith

theorem weightedMomentMap_surjective (k : ℕ) :
    Function.Surjective (weightedMomentMap k) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℝ (MomentPoly k) =
        Module.finrank ℝ (Module.Dual ℝ (MomentPoly k)) by
      symm
      exact Subspace.dual_finrank_eq)).1
  exact weightedMomentMap_injective k

theorem SobolevMapOn.toFun_memLp {n : ℕ} {Ω : TopologicalSpace.Opens ℝ}
    (w : SobolevMapOn n Ω) :
    MemLp w.toFun 2 (volume.restrict (Ω : Set ℝ)) := by
  have h := w.memLp_derivative 0 (Nat.zero_le n)
  rw [w.derivative_zero] at h
  exact h

/-- The right-hand side of the weighted moment system for the Radau polynomial. -/
noncomputable def radauRhs (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) : Module.Dual ℝ (MomentPoly k) where
  toFun v := w 1 * (∫ x, v.1.eval x ∂(volume.restrict referenceCell)) -
    ∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell)
  map_add' v s := by
    have hv := polynomial_eval_integrable_reference v.1
    have hs := polynomial_eval_integrable_reference s.1
    have hw := w.toFun_memLp
    have hwv : Integrable (w.toFun * fun x ↦ v.1.eval x)
        (volume.restrict referenceCell) :=
      hw.integrable_mul (polynomial_eval_memLp_reference v.1)
    have hws : Integrable (w.toFun * fun x ↦ s.1.eval x)
        (volume.restrict referenceCell) :=
      hw.integrable_mul (polynomial_eval_memLp_reference s.1)
    have hpoly : (∫ x, (v + s).1.eval x ∂(volume.restrict referenceCell)) =
        (∫ x, v.1.eval x ∂(volume.restrict referenceCell)) +
          ∫ x, s.1.eval x ∂(volume.restrict referenceCell) := by
      simpa only [Submodule.coe_add, Polynomial.eval_add] using integral_add hv hs
    have hprod : (∫ x, w x * (v + s).1.eval x
          ∂(volume.restrict referenceCell)) =
        (∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell)) +
          ∫ x, w x * s.1.eval x ∂(volume.restrict referenceCell) := by
      simpa only [Submodule.coe_add, Polynomial.eval_add, mul_add, Pi.mul_apply] using
        integral_add hwv hws
    rw [hpoly, hprod]
    ring
  map_smul' c v := by
    have hpoly : (∫ x, (c • v).1.eval x ∂(volume.restrict referenceCell)) =
        c * ∫ x, v.1.eval x ∂(volume.restrict referenceCell) := by
      simpa [Polynomial.eval_smul] using
        (integral_const_mul c (fun x ↦ v.1.eval x)
          (μ := volume.restrict referenceCell))
    have hprod : (∫ x, w x * (c • v).1.eval x
          ∂(volume.restrict referenceCell)) =
        c * ∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell) := by
      rw [show (fun x ↦ w x * (c • v).1.eval x) =
          fun x ↦ c * (w x * v.1.eval x) by
        funext x
        simp [Polynomial.eval_smul]
        ring]
      exact integral_const_mul c (fun x ↦ w x * v.1.eval x)
    rw [hpoly, hprod]
    change w 1 * (c * ∫ x, v.1.eval x ∂(volume.restrict referenceCell)) -
        c * (∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell)) =
      c * (w 1 * (∫ x, v.1.eval x ∂(volume.restrict referenceCell)) -
        ∫ x, w x * v.1.eval x ∂(volume.restrict referenceCell))
    ring

theorem radauPolynomial_mem (k : ℕ) (c : ℝ) (r : MomentPoly k) :
    Polynomial.C c + ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * r.1 ∈
      PolyLE k := by
  rw [mem_PolyLE_iff]
  by_cases hr : r.1 = 0
  · simp [hr]
  have hrdeg : r.1.natDegree < k :=
    (Polynomial.natDegree_lt_iff_degree_lt hr).2 ((Polynomial.mem_degreeLT).1 r.2)
  apply le_trans (Polynomial.natDegree_add_le _ _)
  rw [max_le_iff]
  constructor
  · simp
  · calc
      (((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * r.1).natDegree ≤
          ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1).natDegree +
            r.1.natDegree := Polynomial.natDegree_mul_le
      _ = 1 + r.1.natDegree := by rw [Polynomial.natDegree_X_sub_C]
      _ ≤ k := by omega

theorem mem_MomentPoly_of_natDegree_lt {k : ℕ} {v : Polynomial ℝ}
    (hv : v.natDegree < k) : v ∈ MomentPoly k := by
  rw [Polynomial.mem_degreeLT]
  by_cases hzero : v = 0
  · subst v
    simp
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).1 hv

/-- The Radau conditions for one fixed Sobolev input. -/
def IsGaussRadauAt (k : ℕ) (w : SobolevMapOn (k + 1) referenceCell)
    (p : PolyLE k) : Prop :=
  (∀ v : Polynomial ℝ, v.natDegree < k →
      (∫ x, (p.1.eval x - w x) * v.eval x
        ∂(volume.restrict referenceCell)) = 0) ∧
    p.1.eval 1 = w 1

theorem gaussRadauAt_exists (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) :
    ∃ p : PolyLE k, IsGaussRadauAt k w p := by
  obtain ⟨r, hr⟩ := weightedMomentMap_surjective k (radauRhs k w)
  let p : PolyLE k :=
    ⟨Polynomial.C (w 1) +
      ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * r.1,
      radauPolynomial_mem k (w 1) r⟩
  refine ⟨p, ?_, ?_⟩
  · intro v hv
    let vsub : MomentPoly k := ⟨v, mem_MomentPoly_of_natDegree_lt hv⟩
    have hrv := LinearMap.congr_fun hr vsub
    change (∫ x, (1 - x) * r.1.eval x * v.eval x
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
    have hbInt := polynomial_weighted_product_integrable r.1 v
    have houter :
        (∫ x, (w 1 * v.eval x - w x * v.eval x) -
            (1 - x) * r.1.eval x * v.eval x
            ∂(volume.restrict referenceCell)) =
          (∫ x, w 1 * v.eval x - w x * v.eval x
              ∂(volume.restrict referenceCell)) -
            ∫ x, (1 - x) * r.1.eval x * v.eval x
              ∂(volume.restrict referenceCell) := by
      simpa only [Pi.sub_apply] using integral_sub (hcInt.sub hwvInt) hbInt
    have hinner :
        (∫ x, w 1 * v.eval x - w x * v.eval x
            ∂(volume.restrict referenceCell)) =
          (∫ x, w 1 * v.eval x ∂(volume.restrict referenceCell)) -
            ∫ x, w x * v.eval x ∂(volume.restrict referenceCell) := by
      simpa only [Pi.sub_apply] using integral_sub hcInt hwvInt
    calc
      (∫ x, (p.1.eval x - w x) * v.eval x
          ∂(volume.restrict referenceCell)) =
          ∫ x, ((w 1 * v.eval x - w x * v.eval x) -
            (1 - x) * r.1.eval x * v.eval x)
            ∂(volume.restrict referenceCell) := by
              apply integral_congr_ae
              filter_upwards with x
              dsimp [p]
              simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
                Polynomial.eval_sub, Polynomial.eval_X]
              ring
      _ = ((∫ x, w 1 * v.eval x ∂(volume.restrict referenceCell)) -
            ∫ x, w x * v.eval x ∂(volume.restrict referenceCell)) -
          ∫ x, (1 - x) * r.1.eval x * v.eval x
            ∂(volume.restrict referenceCell) := by
              rw [houter, hinner]
      _ = (w 1 * (∫ x, v.eval x ∂(volume.restrict referenceCell)) -
            ∫ x, w x * v.eval x ∂(volume.restrict referenceCell)) -
          ∫ x, (1 - x) * r.1.eval x * v.eval x
            ∂(volume.restrict referenceCell) := by
              rw [integral_const_mul]
      _ = 0 := by rw [← hrv]; ring
  · dsimp [p]
    simp

/-- Quotient by the endpoint factor `X - 1`. -/
def endpointQuotient (d : Polynomial ℝ) : Polynomial ℝ :=
  d /ₘ ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1)

theorem endpointQuotient_mem {k : ℕ} {d : Polynomial ℝ}
    (hdeg : d.natDegree ≤ k) : endpointQuotient d ∈ MomentPoly k := by
  rw [Polynomial.mem_degreeLT]
  by_cases hd : d = 0
  · simp [endpointQuotient, hd]
  · have hlt := Polynomial.degree_divByMonic_lt d
      (Polynomial.monic_X_sub_C 1) hd (by
        rw [Polynomial.degree_X_sub_C]
        norm_num)
    exact hlt.trans_le ((Polynomial.natDegree_le_iff_degree_le).1 hdeg)

theorem endpoint_decomposition {d : Polynomial ℝ} (heval : d.eval 1 = 0) :
    ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * endpointQuotient d = d := by
  have h := Polynomial.modByMonic_add_div d (Polynomial.monic_X_sub_C 1)
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, heval] at h
  simpa [endpointQuotient] using h

theorem gaussRadauAt_unique (k : ℕ)
    (w : SobolevMapOn (k + 1) referenceCell) {p q : PolyLE k}
    (hp : IsGaussRadauAt k w p) (hq : IsGaussRadauAt k w q) : p = q := by
  let d : Polynomial ℝ := p.1 - q.1
  have hpdeg : p.1.natDegree ≤ k := (mem_PolyLE_iff).1 p.2
  have hqdeg : q.1.natDegree ≤ k := (mem_PolyLE_iff).1 q.2
  have hddeg : d.natDegree ≤ k := by
    dsimp [d]
    exact (Polynomial.natDegree_sub_le p.1 q.1).trans (max_le hpdeg hqdeg)
  let s : MomentPoly k := ⟨endpointQuotient d, endpointQuotient_mem hddeg⟩
  have hdEval : d.eval 1 = 0 := by
    dsimp [d]
    rw [Polynomial.eval_sub, hp.2, hq.2]
    ring
  have hdDecomp :
      ((Polynomial.X : Polynomial ℝ) - Polynomial.C 1) * s.1 = d := by
    exact endpoint_decomposition hdEval
  by_cases hs : s.1 = 0
  · apply Subtype.ext
    have hd : d = 0 := by simpa [hs] using hdDecomp.symm
    exact sub_eq_zero.mp hd
  · have hsNat : s.1.natDegree < k :=
      (Polynomial.natDegree_lt_iff_degree_lt hs).2
        ((Polynomial.mem_degreeLT).1 s.2)
    have hpMom := hp.1 s.1 hsNat
    have hqMom := hq.1 s.1 hsNat
    have hsLp := polynomial_eval_memLp_reference s.1
    have hwLp := w.toFun_memLp
    have hwsInt : Integrable (fun x ↦ w x * s.1.eval x)
        (volume.restrict referenceCell) := hwLp.integrable_mul hsLp
    have hpsInt : Integrable (fun x ↦ p.1.eval x * s.1.eval x)
        (volume.restrict referenceCell) := by
      simpa only [Polynomial.eval_mul] using
        polynomial_eval_integrable_reference (p.1 * s.1)
    have hqsInt : Integrable (fun x ↦ q.1.eval x * s.1.eval x)
        (volume.restrict referenceCell) := by
      simpa only [Polynomial.eval_mul] using
        polynomial_eval_integrable_reference (q.1 * s.1)
    have hpwInt : Integrable (fun x ↦ (p.1.eval x - w x) * s.1.eval x)
        (volume.restrict referenceCell) := by
      simpa only [Pi.sub_apply, sub_mul] using hpsInt.sub hwsInt
    have hqwInt : Integrable (fun x ↦ (q.1.eval x - w x) * s.1.eval x)
        (volume.restrict referenceCell) := by
      simpa only [Pi.sub_apply, sub_mul] using hqsInt.sub hwsInt
    have hmomentD :
        (∫ x, d.eval x * s.1.eval x ∂(volume.restrict referenceCell)) = 0 := by
      calc
        (∫ x, d.eval x * s.1.eval x ∂(volume.restrict referenceCell)) =
            ∫ x, ((p.1.eval x - w x) * s.1.eval x -
              (q.1.eval x - w x) * s.1.eval x)
              ∂(volume.restrict referenceCell) := by
                apply integral_congr_ae
                filter_upwards with x
                dsimp [d]
                rw [Polynomial.eval_sub]
                ring
        _ = (∫ x, (p.1.eval x - w x) * s.1.eval x
                ∂(volume.restrict referenceCell)) -
              ∫ x, (q.1.eval x - w x) * s.1.eval x
                ∂(volume.restrict referenceCell) := by
                  simpa only [Pi.sub_apply] using integral_sub hpwInt hqwInt
        _ = 0 := by rw [hpMom, hqMom]; ring
    have hweighted :
        (∫ x, d.eval x * s.1.eval x ∂(volume.restrict referenceCell)) =
          -(∫ x, (1 - x) * (s.1.eval x) ^ 2
              ∂(volume.restrict referenceCell)) := by
      calc
        (∫ x, d.eval x * s.1.eval x ∂(volume.restrict referenceCell)) =
            ∫ x, -((1 - x) * (s.1.eval x) ^ 2)
              ∂(volume.restrict referenceCell) := by
                apply integral_congr_ae
                filter_upwards with x
                rw [← hdDecomp, Polynomial.eval_mul, Polynomial.eval_sub,
                  Polynomial.eval_X, Polynomial.eval_C]
                ring
        _ = -(∫ x, (1 - x) * (s.1.eval x) ^ 2
              ∂(volume.restrict referenceCell)) := by rw [integral_neg]
    have hzero :
        (∫ x, (1 - x) * (s.1.eval x) ^ 2
          ∂(volume.restrict referenceCell)) = 0 := by
      linarith
    have hpos := polynomial_weighted_sq_integral_pos hs
    linarith

/-- A candidate reference-cell projection into polynomials of degree at most `k`. -/
abbrev Projection (k : ℕ) := SobolevMapOn (k + 1) referenceCell → PolyLE k

/-- Equations (14)--(15): moments against every polynomial of degree `< k`, followed by
the right-endpoint trace condition.  Using degree `< k` also gives the standard vacuous moment
condition when `k = 0`, without adding the unstated assumption `1 ≤ k`. -/
def IsGaussRadau (k : ℕ) (proj : Projection k) : Prop :=
  ∀ w : SobolevMapOn (k + 1) referenceCell,
    (∀ v : Polynomial ℝ, v.natDegree < k →
      (∫ x, ((proj w).1.eval x - w x) * v.eval x
        ∂(volume.restrict referenceCell)) = 0) ∧
    (proj w).1.eval 1 = w 1

/-- The moment and endpoint conditions determine a unique Gauss--Radau projection. -/
theorem gaussRadau_existsUnique (k : ℕ) :
    ∃! proj : Projection k, IsGaussRadau k proj := by
  let proj : Projection k := fun w ↦ Classical.choose (gaussRadauAt_exists k w)
  have hproj : ∀ w, IsGaussRadauAt k w (proj w) := fun w ↦
    Classical.choose_spec (gaussRadauAt_exists k w)
  refine ⟨proj, ?_, ?_⟩
  · intro w
    exact hproj w
  · intro other hother
    funext w
    exact gaussRadauAt_unique k w (hother w) (hproj w)

/-- The Gauss--Radau projection selected from its existence-and-uniqueness theorem. -/
def gaussRadau (k : ℕ) : Projection k :=
  Classical.choose (ExistsUnique.exists (gaussRadau_existsUnique k))

/-- The selected projection satisfies equations (14)--(15). -/
theorem gaussRadau_spec (k : ℕ) : IsGaussRadau k (gaussRadau k) :=
  (Classical.choose_spec (ExistsUnique.exists (gaussRadau_existsUnique k)))

/-- The reference-cell projection error. -/
def referenceError (k : ℕ) (w : SobolevMapOn (k + 1) referenceCell) : ℝ → ℝ :=
  fun x ↦ (gaussRadau k w).1.eval x - w x

/-- The dual functional `F_z(w) = ∫ (Πw-w)z` used in the source proof. -/
def errorFunctional (k : ℕ) (w : SobolevMapOn (k + 1) referenceCell)
    (z : ℝ → ℝ) : ℝ :=
  ∫ x, referenceError k w x * z x ∂(volume.restrict referenceCell)

/-- The source proof's boundedness step for `F_z`, with a constant independent of `w` and `z`
on the `L²` unit ball. -/
def ErrorFunctionalBounded (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (w : SobolevMapOn (k + 1) referenceCell) (z : ℝ → ℝ),
      MemLp z 2 (volume.restrict referenceCell) → l2NormOn referenceCell z ≤ 1 →
      |errorFunctional k w z| ≤ C * sobolevNorm w

/-- The source proof's polynomial-reproduction step: `F_z` vanishes whenever `w` agrees on the
reference cell with a polynomial of degree at most `k`. -/
def ErrorFunctionalAnnihilatesPolynomials (k : ℕ) : Prop :=
  ∀ (w : SobolevMapOn (k + 1) referenceCell) (z : ℝ → ℝ),
    (∃ p : Polynomial ℝ, p.natDegree ≤ k ∧ ∀ x ∈ referenceCell, w x = p.eval x) →
    errorFunctional k w z = 0

end Exp2
