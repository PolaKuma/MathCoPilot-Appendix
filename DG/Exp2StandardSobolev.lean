import Exp2
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set Filter

noncomputable section

namespace Exp2

/-- The standard real `L²` space on the reference interval, with equality modulo almost
everywhere equality supplied by Mathlib's `Lp` quotient. -/
abbrev ReferenceL2 := Lp ℝ 2 (volume.restrict (referenceCell : Set ℝ))

/-- The standard integer-order Sobolev graph space on `(0,1)`: an element consists of its
`L²` equivalence classes of weak derivatives through order `n`.  Unlike `SobolevMapOn`, all
stored functions here are genuine `Lp` quotient elements. -/
structure StandardSobolevOnReference (n : ℕ) where
  derivative : Fin (n + 1) → ReferenceL2
  weakDerivative_succ : ∀ (j : ℕ) (hj : j < n),
    WeakDerivativeOn referenceCell
      (derivative ⟨j, Nat.lt_succ_iff.mpr (Nat.le_of_lt hj)⟩ : ℝ → ℝ)
      (derivative ⟨j + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hj)⟩ : ℝ → ℝ)

namespace StandardSobolevOnReference

/-- A total function-valued representative of the `j`th `Lp` derivative class.  Values above
the Sobolev order are set to zero and are never part of the public semantics. -/
def derivativeFn {n : ℕ} (w : StandardSobolevOnReference n) (j : ℕ) : ℝ → ℝ :=
  if h : j ≤ n then
    (w.derivative ⟨j, by omega⟩ : ℝ → ℝ)
  else
    0

@[simp] theorem derivativeFn_eq {n : ℕ} (w : StandardSobolevOnReference n)
    {j : ℕ} (hj : j ≤ n) :
    w.derivativeFn j = (w.derivative ⟨j, by omega⟩ : ℝ → ℝ) := by
  simp [derivativeFn, hj]

theorem derivativeFn_memLp {n : ℕ} (w : StandardSobolevOnReference n)
    {j : ℕ} (hj : j ≤ n) :
    MemLp (w.derivativeFn j) 2 (volume.restrict referenceCell) := by
  rw [w.derivativeFn_eq hj]
  exact Lp.memLp _

theorem derivativeFn_weakDerivative_succ {n : ℕ}
    (w : StandardSobolevOnReference n) {j : ℕ} (hj : j < n) :
    WeakDerivativeOn referenceCell (w.derivativeFn j) (w.derivativeFn (j + 1)) := by
  rw [w.derivativeFn_eq (Nat.le_of_lt hj),
    w.derivativeFn_eq (Nat.succ_le_of_lt hj)]
  exact w.weakDerivative_succ j hj

end StandardSobolevOnReference

/-- Distributional weak derivatives are invariant when both representatives are changed on
null sets. -/
theorem WeakDerivativeOn.congr_ae_reference {f f' g g' : ℝ → ℝ}
    (hfg : WeakDerivativeOn referenceCell f g)
    (hff' : f =ᵐ[volume.restrict referenceCell] f')
    (hgg' : g =ᵐ[volume.restrict referenceCell] g') :
    WeakDerivativeOn referenceCell f' g' := by
  intro φ
  calc
    (∫ x, f' x * deriv φ x ∂(volume.restrict referenceCell)) =
        ∫ x, f x * deriv φ x ∂(volume.restrict referenceCell) := by
          apply integral_congr_ae
          filter_upwards [hff'] with x hx
          rw [hx]
    _ = -(∫ x, g x * φ x ∂(volume.restrict referenceCell)) := hfg φ
    _ = -(∫ x, g' x * φ x ∂(volume.restrict referenceCell)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hgg'] with x hx
          rw [hx]

/-- Forgetting the chosen continuous representative sends the concrete project model to the
standard `Lp` quotient model. -/
def SobolevMapOn.toStandardReference {n : ℕ}
    (w : SobolevMapOn n referenceCell) : StandardSobolevOnReference n where
  derivative := fun j ↦
    (w.memLp_derivative j (by omega)).toLp (w.derivative j)
  weakDerivative_succ := by
    intro j hj
    apply (w.weakDerivative_succ j hj).congr_ae_reference
    · exact (w.memLp_derivative j (by omega)).coeFn_toLp.symm
    · exact (w.memLp_derivative (j + 1) (by omega)).coeFn_toLp.symm

/-- Every standard `Lp` Sobolev class on `(0,1)` has a continuous zeroth representative with
a concrete weak-derivative chain.  All derivatives of that representative remain in the
original `Lp` classes.  This is the one-dimensional representative/trace bridge missing from
the original project model. -/
theorem StandardSobolevOnReference.exists_concreteRepresentative (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) :
    ∃ u : SobolevMapOn (k + 1) referenceCell,
      ∀ j ≤ k + 1,
        u.derivative j =ᵐ[volume.restrict referenceCell] w.derivativeFn j := by
  let f : ℕ → ℝ → ℝ := w.derivativeFn
  have hfLp : ∀ j ≤ k + 1,
      MemLp (f j) 2 (volume.restrict referenceCell) := by
    intro j hj
    exact w.derivativeFn_memLp hj
  have hfWeak : ∀ j < k + 1,
      WeakDerivativeOn referenceCell (f j) (f (j + 1)) := by
    intro j hj
    exact w.derivativeFn_weakDerivative_succ hj
  let g : ℝ → ℝ := f (k + 1)
  have hg : MemLp g 2 (volume.restrict referenceCell) := hfLp (k + 1) le_rfl
  let v : SobolevMapOn (k + 1) referenceCell := primitiveSobolev k g hg
  let d : ℕ → ℝ → ℝ := fun j ↦ f j - v.derivative j
  have hdLp : ∀ j ≤ k + 1,
      MemLp (d j) 2 (volume.restrict referenceCell) := by
    intro j hj
    exact (hfLp j hj).sub (v.memLp_derivative j hj)
  have hdWeak : ∀ j < k + 1,
      WeakDerivativeOn referenceCell (d j) (d (j + 1)) := by
    intro j hj
    exact (hfWeak j hj).sub_of_memLp (v.weakDerivative_succ j hj)
      (hfLp j (Nat.le_of_lt hj))
      (hfLp (j + 1) (Nat.succ_le_of_lt hj))
      (v.memLp_derivative j (Nat.le_of_lt hj))
      (v.memLp_derivative (j + 1) (Nat.succ_le_of_lt hj))
  have hdTop : d (k + 1) = 0 := by
    funext x
    simp [d, v, g, primitiveSobolev, iteratedWeakPrimitive]
  obtain ⟨p, hpdeg, hpae⟩ :=
    weakDerivative_chain_ae_polynomial (k + 1) d hdLp hdWeak hdTop
  let continuousRep : ℝ → ℝ := fun x ↦ p.eval x + v x
  have hf0ae : f 0 =ᵐ[volume.restrict referenceCell] continuousRep := by
    filter_upwards [hpae] with x hx
    dsimp only [d, Pi.sub_apply] at hx
    rw [v.derivative_zero] at hx
    dsimp only [continuousRep]
    linarith
  let derivativeRep : ℕ → ℝ → ℝ :=
    fun j ↦ if j = 0 then continuousRep else f j
  have hderivZero : derivativeRep 0 = continuousRep := by
    simp [derivativeRep]
  have hcont : ContinuousOn continuousRep (closure (referenceCell : Set ℝ)) := by
    exact (polynomial_eval_continuous p).continuousOn.add v.continuousOn
  have hrepLp : ∀ j ≤ k + 1,
      MemLp (derivativeRep j) 2 (volume.restrict referenceCell) := by
    intro j hj
    by_cases hzero : j = 0
    · subst j
      rw [hderivZero]
      exact MemLp.ae_eq hf0ae (hfLp 0 (by omega))
    · simp [derivativeRep, hzero]
      exact hfLp j hj
  have hrepWeak : ∀ j < k + 1,
      WeakDerivativeOn referenceCell (derivativeRep j) (derivativeRep (j + 1)) := by
    intro j hj
    by_cases hzero : j = 0
    · subst j
      simp only [derivativeRep, if_pos]
      have hright :
          f (0 + 1) =ᵐ[volume.restrict referenceCell]
            (if 0 + 1 = 0 then continuousRep else f (0 + 1)) := by
        simp
      exact (hfWeak 0 (by omega)).congr_ae_reference hf0ae hright
    · have hsucc : j + 1 ≠ 0 := by omega
      simp only [derivativeRep, if_neg hzero, if_neg hsucc]
      exact hfWeak j hj
  let u : SobolevMapOn (k + 1) referenceCell :=
    { toFun := continuousRep
      derivative := derivativeRep
      derivative_zero := hderivZero
      continuousOn := hcont
      memLp_derivative := hrepLp
      weakDerivative_succ := hrepWeak }
  refine ⟨u, ?_⟩
  intro j hj
  by_cases hzero : j = 0
  · subst j
    change continuousRep =ᵐ[volume.restrict referenceCell] f 0
    exact hf0ae.symm
  · change derivativeRep j =ᵐ[volume.restrict referenceCell] f j
    simp [derivativeRep, hzero]

/-- The canonical continuous representative selected from the preceding existence theorem. -/
def StandardSobolevOnReference.continuousRepresentative (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) :
    SobolevMapOn (k + 1) referenceCell :=
  Classical.choose (w.exists_concreteRepresentative k)

theorem StandardSobolevOnReference.continuousRepresentative_ae (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) (j : ℕ) (hj : j ≤ k + 1) :
    (w.continuousRepresentative k).derivative j
      =ᵐ[volume.restrict referenceCell] w.derivativeFn j :=
  Classical.choose_spec (w.exists_concreteRepresentative k) j hj

/-- The standard Sobolev seminorm, defined directly on the top `Lp` derivative class. -/
def StandardSobolevOnReference.seminorm (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) : ℝ :=
  ‖w.derivative ⟨k + 1, by omega⟩‖

theorem StandardSobolevOnReference.concrete_seminorm_eq (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) :
    sobolevSeminorm (w.continuousRepresentative k) = w.seminorm k := by
  rw [seminorm, sobolevSeminorm, l2NormOn, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  have hfun :
      w.derivativeFn (k + 1) =
        (w.derivative ⟨k + 1, by omega⟩ : ℝ → ℝ) :=
    w.derivativeFn_eq le_rfl
  exact (w.continuousRepresentative_ae k (k + 1) le_rfl).trans
    (Filter.Eventually.of_forall fun x ↦ congrFun hfun x)

/-- The Gauss--Radau projection of a standard Sobolev equivalence class, defined through its
canonical one-dimensional continuous representative. -/
def standardGaussRadau (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) : PolyLE k :=
  gaussRadau k (w.continuousRepresentative k)

/-- The projection error as a genuine element of the standard `L²` quotient space. -/
def standardReferenceError (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) : ReferenceL2 :=
  (referenceError_memLp k (w.continuousRepresentative k)).toLp
    (referenceError k (w.continuousRepresentative k))

theorem standardReferenceError_norm_eq (k : ℕ)
    (w : StandardSobolevOnReference (k + 1)) :
    ‖standardReferenceError k w‖ =
      l2NormOn referenceCell (referenceError k (w.continuousRepresentative k)) := by
  exact Lp.norm_toLp _ _

/-- The PDF's reference-cell theorem on the standard `H^(k+1)(0,1)` graph space of `Lp`
equivalence classes. -/
theorem standard_reference_cell_estimate (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ w : StandardSobolevOnReference (k + 1),
        ‖standardReferenceError k w‖ ≤ C * w.seminorm k := by
  obtain ⟨C, hC, href⟩ := reference_cell_estimate k
  refine ⟨C, hC, ?_⟩
  intro w
  rw [standardReferenceError_norm_eq, ← w.concrete_seminorm_eq k]
  exact href (w.continuousRepresentative k)

/-- The standard real `L²` quotient space on a physical cell. -/
abbrev CellL2 (a h : ℝ) := Lp ℝ 2 (volume.restrict (cell a h : Set ℝ))

/-- Standard integer-order Sobolev data on a physical cell, expressed entirely through
Mathlib `Lp` equivalence classes and distributional weak derivatives. -/
structure StandardSobolevOnCell (n : ℕ) (a h : ℝ) where
  derivative : Fin (n + 1) → CellL2 a h
  weakDerivative_succ : ∀ (j : ℕ) (hj : j < n),
    WeakDerivativeOn (cell a h)
      (derivative ⟨j, Nat.lt_succ_iff.mpr (Nat.le_of_lt hj)⟩ : ℝ → ℝ)
      (derivative ⟨j + 1, Nat.lt_succ_iff.mpr (Nat.succ_le_of_lt hj)⟩ : ℝ → ℝ)

namespace StandardSobolevOnCell

/-- The affine pullback of a physical Sobolev class.  The `j`th weak derivative is represented
by `h^j w^(j)(a+h*x)`, exactly as in the PDF scaling argument. -/
def pullback {n : ℕ} {a h : ℝ} (hh : 0 < h)
    (w : StandardSobolevOnCell n a h) : StandardSobolevOnReference n where
  derivative := fun j ↦
    let f : ℝ → ℝ := (w.derivative j : ℝ → ℝ)
    let hf : MemLp f 2 (volume.restrict (cell a h : Set ℝ)) := Lp.memLp _
    let hcomp : MemLp (fun x ↦ f (a + h * x)) 2
        (volume.restrict (referenceCell : Set ℝ)) :=
      Exp2.MemLp.affine_comp hh hf
    (hcomp.const_smul (h ^ (j : ℕ))).toLp
      (fun x ↦ h ^ (j : ℕ) * f (a + h * x))
  weakDerivative_succ := by
    intro j hj
    let f : ℝ → ℝ := (w.derivative ⟨j, by omega⟩ : ℝ → ℝ)
    let g : ℝ → ℝ := (w.derivative ⟨j + 1, by omega⟩ : ℝ → ℝ)
    have hf : MemLp f 2 (volume.restrict (cell a h : Set ℝ)) := Lp.memLp _
    have hg : MemLp g 2 (volume.restrict (cell a h : Set ℝ)) := Lp.memLp _
    have hfcomp := Exp2.MemLp.affine_comp hh hf
    have hgcomp := Exp2.MemLp.affine_comp hh hg
    have hscaled : WeakDerivativeOn referenceCell
        (fun x ↦ h ^ j * f (a + h * x))
        (fun x ↦ h ^ (j + 1) * g (a + h * x)) := by
      have hraw := (w.weakDerivative_succ j hj).affine_comp hh (c := h ^ j)
      simpa [f, g, pow_succ] using hraw
    dsimp
    apply hscaled.congr_ae_reference
    · exact (hfcomp.const_smul (h ^ j)).coeFn_toLp.symm
    · exact (hgcomp.const_smul (h ^ (j + 1))).coeFn_toLp.symm

theorem pullback_derivative_ae {n : ℕ} {a h : ℝ} (hh : 0 < h)
    (w : StandardSobolevOnCell n a h) (j : ℕ) (hj : j ≤ n) :
    (w.pullback hh).derivativeFn j =ᵐ[volume.restrict referenceCell]
      fun x ↦ h ^ j * (w.derivative ⟨j, by omega⟩ : ℝ → ℝ) (a + h * x) := by
  rw [(w.pullback hh).derivativeFn_eq hj]
  dsimp [pullback]
  exact (Exp2.MemLp.affine_comp hh (Lp.memLp (w.derivative ⟨j, by omega⟩))
    |>.const_smul (h ^ j)).coeFn_toLp

/-- The physical-cell top-order Sobolev seminorm, intrinsically defined on the `Lp` class. -/
def seminorm {n : ℕ} {a h : ℝ} (w : StandardSobolevOnCell n a h) : ℝ :=
  ‖w.derivative ⟨n, by omega⟩‖

/-- Exact top-order seminorm scaling for standard `Lp` Sobolev classes. -/
theorem pullback_seminorm_scaling (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : StandardSobolevOnCell (k + 1) a h) :
    Real.sqrt h * (w.pullback hh).seminorm k =
      h ^ (k + 1) * w.seminorm := by
  let n : ℕ := k + 1
  let f : ℝ → ℝ := (w.derivative ⟨n, by omega⟩ : ℝ → ℝ)
  have hf : MemLp f 2 (volume.restrict (cell a h : Set ℝ)) := Lp.memLp _
  have hscale := Exp2AffineMeasure.eLpNorm_comp_affine_restrict_Ioo
    (p := (2 : ℝ≥0∞)) f hh hf.aestronglyMeasurable
  have hconst := eLpNorm_const_smul (h ^ n : ℝ)
    (fun x ↦ f (a + h * x)) (2 : ℝ≥0∞)
    (volume.restrict (Set.Ioo (0 : ℝ) 1))
  have hcombined :
      eLpNorm (fun x ↦ h ^ n * f (a + h * x)) 2
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
        ‖(h ^ n : ℝ)‖ₑ *
          ((ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal •
            eLpNorm f 2 (volume.restrict (Set.Ioo a (a + h)))) := by
    have hfun : (fun x ↦ h ^ n * f (a + h * x)) =
        (h ^ n : ℝ) • (fun x ↦ f (a + h * x)) := by
      funext x
      simp [smul_eq_mul]
    rw [hfun, hconst, hscale]
  have hpb :
      (w.pullback hh).seminorm k =
        (eLpNorm (fun x ↦ h ^ n * f (a + h * x)) 2
          (volume.restrict (referenceCell : Set ℝ))).toReal := by
    dsimp only [StandardSobolevOnReference.seminorm]
    rw [Lp.norm_def]
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_ae
    have hae := pullback_derivative_ae hh w n (by simp [n])
    simpa [n, f] using hae
  have hw :
      w.seminorm =
        (eLpNorm f 2 (volume.restrict (Set.Ioo a (a + h)))).toReal := by
    dsimp only [seminorm]
    rw [Lp.norm_def]
    rfl
  have hcombined' :
      eLpNorm (fun x ↦ h ^ n * f (a + h * x)) 2
          (volume.restrict (referenceCell : Set ℝ)) =
        ‖(h ^ n : ℝ)‖ₑ *
          ((ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal •
            eLpNorm f 2 (volume.restrict (Set.Ioo a (a + h)))) := by
    simpa [referenceCell, cell] using hcombined
  have hto := congrArg ENNReal.toReal hcombined'
  rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul] at hto
  have hcoef : (‖(h ^ n : ℝ)‖ₑ).toReal = h ^ n := by
    simp [Real.norm_eq_abs, abs_of_pos hh]
  rw [hcoef] at hto
  have hinv : (ENNReal.ofReal h⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal).toReal =
      (Real.sqrt h)⁻¹ := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (inv_nonneg.mpr hh.le)]
    rw [Real.sqrt_eq_rpow]
    norm_num
    exact Real.inv_rpow hh.le _
  rw [hinv] at hto
  rw [hpb, hw]
  have hsqrt : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hmul := congrArg (fun t : ℝ ↦ Real.sqrt h * t) hto
  field_simp [ne_of_gt hsqrt] at hmul
  simpa [n, pow_succ] using hmul

end StandardSobolevOnCell

/-- An affine-coordinate polynomial belongs to physical-cell `L²`. -/
theorem affinePolynomial_memLp (p : Polynomial ℝ) {a h : ℝ} (hh : 0 < h) :
    MemLp (fun x ↦ p.eval ((x - a) / h)) 2
      (volume.restrict (cell a h : Set ℝ)) := by
  let f : ℝ → ℝ := fun x ↦ p.eval ((x - a) / h)
  have hfcont : Continuous f :=
    (polynomial_eval_continuous p).comp
      ((continuous_id.sub continuous_const).div_const h)
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Set.Ioo a (a + h))) := hfcont.aestronglyMeasurable
  have hscale := Exp2AffineMeasure.eLpNorm_comp_affine_restrict_Ioo
    (p := (2 : ℝ≥0∞)) f hh hfmeas
  have hcomp : (fun x : ℝ ↦ f (a + h * x)) = fun x ↦ p.eval x := by
    funext x
    dsimp [f]
    have hcoord : (a + h * x - a) / h = x := by
      rw [add_sub_cancel_left]
      exact mul_div_cancel_left₀ x hh.ne'
    rw [hcoord]
  rw [hcomp] at hscale
  have href := polynomial_eval_memLp_reference p
  have hprod :
      (ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (volume.restrict (Set.Ioo a (a + h))) < ∞ := by
    calc
      _ = eLpNorm (fun x ↦ p.eval x) 2
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
            simpa [smul_eq_mul] using hscale.symm
      _ < ∞ := by simpa [referenceCell, cell] using href.2
  have hcoef : (ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ 0 := by
    intro hz
    rcases ENNReal.rpow_eq_zero_iff.mp hz with hzero | htop
    · exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hh)).ne' hzero.1
    · exact (ENNReal.ofReal_ne_top).elim htop.1
  have hnorm : eLpNorm f 2 (volume.restrict (Set.Ioo a (a + h))) < ∞ := by
    rcases ENNReal.mul_lt_top_iff.mp hprod with hfinite | hzero | hzero
    · exact hfinite.2
    · exact (hcoef hzero).elim
    · rw [hzero]
      exact ENNReal.zero_lt_top
  exact ⟨by simpa [cell] using hfmeas, by simpa [f, cell] using hnorm⟩

/-- The physical Gauss--Radau projection of a standard Sobolev class. -/
def standardPhysicalProjection (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : StandardSobolevOnCell (k + 1) a h) : ℝ → ℝ :=
  fun x ↦ (standardGaussRadau k (w.pullback hh)).1.eval ((x - a) / h)

/-- The physical projection error as an element of the standard physical-cell `L²` quotient. -/
def standardPhysicalError (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : StandardSobolevOnCell (k + 1) a h) : CellL2 a h :=
  let f : ℝ → ℝ :=
    fun x ↦ standardPhysicalProjection k hh w x -
      (w.derivative ⟨0, by omega⟩ : ℝ → ℝ) x
  let hf : MemLp f 2 (volume.restrict (cell a h : Set ℝ)) :=
    (affinePolynomial_memLp (standardGaussRadau k (w.pullback hh)).1 hh).sub
      (Lp.memLp _)
  hf.toLp f

theorem standardPhysicalError_norm_eq (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : StandardSobolevOnCell (k + 1) a h) :
    ‖standardPhysicalError k hh w‖ =
      l2NormOn (cell a h)
        (fun x ↦ standardPhysicalProjection k hh w x -
          (w.derivative ⟨0, by omega⟩ : ℝ → ℝ) x) := by
  let f : ℝ → ℝ :=
    fun x ↦ standardPhysicalProjection k hh w x -
      (w.derivative ⟨0, by omega⟩ : ℝ → ℝ) x
  let hf : MemLp f 2 (volume.restrict (cell a h : Set ℝ)) :=
    (affinePolynomial_memLp (standardGaussRadau k (w.pullback hh)).1 hh).sub
      (Lp.memLp _)
  change ‖hf.toLp f‖ = (eLpNorm f 2 (volume.restrict (cell a h : Set ℝ))).toReal
  exact Lp.norm_toLp f hf

theorem StandardSobolevOnCell.continuousRepresentative_zero_ae (k : ℕ)
    {a h : ℝ} (hh : 0 < h) (w : StandardSobolevOnCell (k + 1) a h) :
    ((w.pullback hh).continuousRepresentative k : ℝ → ℝ)
      =ᵐ[volume.restrict referenceCell]
        fun x ↦ (w.derivative ⟨0, by omega⟩ : ℝ → ℝ) (a + h * x) := by
  have hrep :=
    (w.pullback hh).continuousRepresentative_ae k 0 (by omega)
  have hpull := w.pullback_derivative_ae hh 0 (by omega)
  have hchain := hrep.trans hpull
  simpa [(w.pullback hh).continuousRepresentative k |>.derivative_zero] using hchain

/-- Exact physical/reference `L²` scaling for the standard quotient-space projection error. -/
theorem standardPhysicalError_scaling (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : StandardSobolevOnCell (k + 1) a h) :
    ‖standardPhysicalError k hh w‖ =
      Real.sqrt h * ‖standardReferenceError k (w.pullback hh)‖ := by
  let f : ℝ → ℝ :=
    fun x ↦ standardPhysicalProjection k hh w x -
      (w.derivative ⟨0, by omega⟩ : ℝ → ℝ) x
  have hf : MemLp f 2 (volume.restrict (cell a h : Set ℝ)) :=
    (affinePolynomial_memLp (standardGaussRadau k (w.pullback hh)).1 hh).sub
      (Lp.memLp _)
  have hscale := Exp2AffineMeasure.eLpNorm_comp_affine_restrict_Ioo
    (p := (2 : ℝ≥0∞)) f hh hf.aestronglyMeasurable
  have hzero := w.continuousRepresentative_zero_ae k hh
  have hcomp :
      (fun x ↦ f (a + h * x))
        =ᵐ[volume.restrict referenceCell]
          referenceError k ((w.pullback hh).continuousRepresentative k) := by
    filter_upwards [hzero] with x hx
    dsimp [f, standardPhysicalProjection, standardGaussRadau, referenceError]
    have hcoord : (a + h * x - a) / h = x := by
      rw [add_sub_cancel_left]
      exact mul_div_cancel_left₀ x hh.ne'
    rw [hcoord, hx]
    have hfin :
        (0 : Fin (k + 1 + 1)) = ⟨0, by omega⟩ := Fin.ext rfl
    rw [hfin]
  have hscale' :
      eLpNorm (referenceError k ((w.pullback hh).continuousRepresentative k)) 2
          (volume.restrict referenceCell) =
        (ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal •
          eLpNorm f 2 (volume.restrict (cell a h : Set ℝ)) := by
    calc
      _ = eLpNorm (fun x ↦ f (a + h * x)) 2
          (volume.restrict referenceCell) :=
            (eLpNorm_congr_ae hcomp).symm
      _ = _ := by simpa [referenceCell, cell] using hscale
  have hto := congrArg ENNReal.toReal hscale'
  rw [smul_eq_mul, ENNReal.toReal_mul] at hto
  have hinv : (ENNReal.ofReal h⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal).toReal =
      (Real.sqrt h)⁻¹ := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (inv_nonneg.mpr hh.le)]
    rw [Real.sqrt_eq_rpow]
    norm_num
    exact Real.inv_rpow hh.le _
  rw [hinv] at hto
  rw [standardPhysicalError_norm_eq, standardReferenceError_norm_eq]
  change (eLpNorm f 2 (volume.restrict (cell a h : Set ℝ))).toReal =
    Real.sqrt h *
      (eLpNorm (referenceError k ((w.pullback hh).continuousRepresentative k)) 2
        (volume.restrict referenceCell)).toReal
  have hsqrt : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hmul := congrArg (fun t : ℝ ↦ Real.sqrt h * t) hto
  field_simp [ne_of_gt hsqrt] at hmul
  simpa [mul_comm] using hmul.symm

/-- The physical-cell estimate for the standard Sobolev quotient model. -/
theorem standard_physical_cell_estimate (k : ℕ) (C : ℝ)
    (href : ∀ w : StandardSobolevOnReference (k + 1),
      ‖standardReferenceError k w‖ ≤ C * w.seminorm k) :
    ∀ {a h : ℝ} (hh : 0 < h) (w : StandardSobolevOnCell (k + 1) a h),
      ‖standardPhysicalError k hh w‖ ≤
        C * h ^ (k + 1) * w.seminorm := by
  intro a h hh w
  rw [standardPhysicalError_scaling]
  calc
    Real.sqrt h * ‖standardReferenceError k (w.pullback hh)‖ ≤
        Real.sqrt h * (C * (w.pullback hh).seminorm k) :=
      mul_le_mul_of_nonneg_left (href (w.pullback hh)) (Real.sqrt_nonneg h)
    _ = C * (Real.sqrt h * (w.pullback hh).seminorm k) := by ring
    _ = C * (h ^ (k + 1) * w.seminorm) := by
      rw [w.pullback_seminorm_scaling k hh]
    _ = C * h ^ (k + 1) * w.seminorm := by ring

/-- Full Exp.2 theorem on standard `Lp` Sobolev equivalence classes. -/
theorem standard_main_theorem (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ w : StandardSobolevOnReference (k + 1),
        ‖standardReferenceError k w‖ ≤ C * w.seminorm k) ∧
      (∀ {a h : ℝ} (hh : 0 < h) (w : StandardSobolevOnCell (k + 1) a h),
        ‖standardPhysicalError k hh w‖ ≤
          C * h ^ (k + 1) * w.seminorm) := by
  obtain ⟨C, hC, href⟩ := standard_reference_cell_estimate k
  exact ⟨C, hC, href, standard_physical_cell_estimate k C href⟩

end Exp2
