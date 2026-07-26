import Exp2BHProbe

open scoped ENNReal MeasureTheory Topology Interval
open MeasureTheory Set Filter

noncomputable section
namespace Exp2

/-- Continuity of the Gauss--Radau coefficients (moments plus endpoint trace) makes `F_z` bounded. -/
theorem gaussRadau_errorFunctional_bounded (k : ℕ) : ErrorFunctionalBounded k := by
  exact gaussRadau_errorFunctional_bounded_complete k

/-- Uniqueness of the Gauss--Radau equations implies exact reproduction of `P_k`. -/
theorem gaussRadau_errorFunctional_annihilates (k : ℕ) :
    ErrorFunctionalAnnihilatesPolynomials k := by
  classical
  intro w z hwpoly
  obtain ⟨p, hpdeg, hEq⟩ := hwpoly
  let psub : PolyLE k := ⟨p, (mem_PolyLE_iff).2 hpdeg⟩
  let alt : Projection k := fun w' => if h : w' = w then psub else gaussRadau k w'
  have halt : IsGaussRadau k alt := by
    intro w'
    by_cases hw' : w' = w
    · subst w'
      constructor
      · intro v hv
        have hz : ∀ x ∈ referenceCell, p.eval x - w x = 0 := by
          intro x hx
          rw [hEq x hx]
          ring
        simp only [alt, dif_pos rfl]
        change (∫ x, (p.eval x - w x) * v.eval x
          ∂(volume.restrict referenceCell)) = 0
        have hAE : (fun x : ℝ ↦ (p.eval x - w x) * v.eval x) =ᵐ[
            volume.restrict (referenceCell : Set ℝ)] (fun _ ↦ (0 : ℝ)) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
          rw [hz x hx]
          simp
        have hInt := integral_congr_ae hAE
        simpa using hInt
      · simp only [alt, dif_pos rfl]
        exact (SobolevMapOn.eq_eval_one_of_eqOn_reference w p hEq).symm
    · simpa [alt, hw'] using (gaussRadau_spec k w')
  have heq : alt = gaussRadau k :=
    ((gaussRadau_existsUnique k).unique (gaussRadau_spec k) halt).symm
  have hpoint : alt w = gaussRadau k w := congrFun heq w
  have hzero : ∀ x ∈ referenceCell, referenceError k w x = 0 := by
    intro x hx
    have hpw : (gaussRadau k w).1 = p := by
      have h : (alt w).1 = p := by simp [alt, psub]
      rw [hpoint] at h
      exact h
    dsimp [referenceError]
    rw [hpw]
    exact sub_eq_zero.mpr (hEq x hx).symm
  change (∫ x, referenceError k w x * z x ∂(volume.restrict referenceCell)) = 0
  have hAE : (fun x : ℝ ↦ referenceError k w x * z x) =ᵐ[
      volume.restrict (referenceCell : Set ℝ)] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hzero x hx]
    simp
  have hInt := integral_congr_ae hAE
  simpa using hInt

/-- Bramble--Hilbert plus `L²` duality converts boundedness and polynomial annihilation into the
reference-cell seminorm estimate. -/
theorem brambleHilbert_reference (k : ℕ)
    (hbounded : ErrorFunctionalBounded k)
    (hannihilates : ErrorFunctionalAnnihilatesPolynomials k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SobolevMapOn (k + 1) referenceCell,
      l2NormOn referenceCell (referenceError k w) ≤ C * sobolevSeminorm w := by
  exact brambleHilbert_reference_complete k hbounded hannihilates

/-- Theorem 2: the reference-cell `L²` error is controlled by the order-`k+1` Sobolev seminorm,
with a constant independent of `w`. -/
theorem reference_cell_estimate (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SobolevMapOn (k + 1) referenceCell,
      l2NormOn referenceCell (referenceError k w) ≤ C * sobolevSeminorm w := by
  exact brambleHilbert_reference k (gaussRadau_errorFunctional_bounded k)
    (gaussRadau_errorFunctional_annihilates k)

/-- `wHat` is the affine pullback of `w` under `x = a + h*xHat`, including the exact scaling of
all weak derivatives through order `n`. -/
def IsAffinePullback {n : ℕ} {a h : ℝ}
    (w : SobolevMapOn n (cell a h)) (wHat : SobolevMapOn n referenceCell) : Prop :=
  ∀ j ≤ n, wHat.derivative j = fun xHat ↦ h ^ j * w.derivative j (a + h * xHat)

/-- A reference-cell test function transported to the physical cell by the inverse affine map. -/
def inverseAffineTestFunction {a h : ℝ} (hh : 0 < h)
    (φ : TestFunction referenceCell ℝ ⊤) : TestFunction (cell a h) ℝ ⊤ where
  toFun := fun y ↦ φ ((y - a) / h)
  contDiff' := by
    exact φ.contDiff.comp ((contDiff_id.sub contDiff_const).div_const h)
  hasCompactSupport' := by
    let e : ℝ ≃ₜ ℝ :=
      (Homeomorph.addRight (-a)).trans (Homeomorph.mulRight₀ h⁻¹ (inv_ne_zero hh.ne'))
    have he : (e : ℝ → ℝ) = fun y ↦ (y - a) / h := by
      funext y
      simp [e, sub_eq_add_neg, div_eq_mul_inv]
    have hc := φ.hasCompactSupport.comp_homeomorph e
    rw [he] at hc
    exact hc
  tsupport_subset' := by
    change tsupport ((φ : ℝ → ℝ) ∘ fun y ↦ (y - a) / h) ⊆ (cell a h : Set ℝ)
    have hc : Continuous (fun y : ℝ ↦ (y - a) / h) := by fun_prop
    have hsub := tsupport_comp_subset_preimage (φ : ℝ → ℝ) hc
    intro y hy
    have hmem : (y - a) / h ∈ referenceCell := by
      apply φ.tsupport_subset
      apply hsub
      exact hy
    change y ∈ Set.Ioo a (a + h)
    have hmem' : (y - a) / h ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [referenceCell, cell] using hmem
    have hlower : 0 < y - a := by
      have hmul := mul_pos hmem'.1 hh
      field_simp [hh.ne'] at hmul
      exact hmul
    have hupper : y - a < h := by
      have hmul := mul_lt_mul_of_pos_right hmem'.2 hh
      field_simp [hh.ne'] at hmul
      exact hmul
    constructor <;> linarith

theorem inverseAffineTestFunction_apply {a h : ℝ} (hh : 0 < h)
    (φ : TestFunction referenceCell ℝ ⊤) (y : ℝ) :
    inverseAffineTestFunction (a := a) hh φ y = φ ((y - a) / h) := rfl

theorem inverseAffineTestFunction_deriv {a h : ℝ} (hh : 0 < h)
    (φ : TestFunction referenceCell ℝ ⊤) (y : ℝ) :
    deriv (inverseAffineTestFunction (a := a) hh φ) y =
      h⁻¹ * deriv φ ((y - a) / h) := by
  have hφ : DifferentiableAt ℝ (φ : ℝ → ℝ) ((y - a) / h) :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  have hin : HasDerivAt (fun y : ℝ ↦ (y - a) / h) h⁻¹ y := by
    have hd := ((hasDerivAt_id y).sub_const a)
    have hs := hd.const_smul h⁻¹
    convert hs using 1
    · funext z
      simp [div_eq_mul_inv, mul_comm]
    · simp
  have hc := hφ.hasDerivAt.comp y hin
  simpa [inverseAffineTestFunction, mul_comm] using hc.deriv

/-- Exact affine transport of the custom distributional weak-derivative identity. -/
theorem WeakDerivativeOn.affine_comp {a h c : ℝ} (hh : 0 < h) {f g : ℝ → ℝ}
    (hfg : WeakDerivativeOn (cell a h) f g) :
    WeakDerivativeOn referenceCell
      (fun x ↦ c * f (a + h * x))
      (fun x ↦ (c * h) * g (a + h * x)) := by
  intro φ
  let ψ : TestFunction (cell a h) ℝ ⊤ := inverseAffineTestFunction hh φ
  let A : ℝ := ∫ x in Set.Ioo (0 : ℝ) 1, f (a + h * x) * deriv φ x
  let B : ℝ := ∫ x in Set.Ioo (0 : ℝ) 1, g (a + h * x) * φ x
  let PF : ℝ := ∫ y in Set.Ioo a (a + h), f y * deriv φ ((y - a) / h)
  let PG : ℝ := ∫ y in Set.Ioo a (a + h), g y * φ ((y - a) / h)
  have hinv : ∀ x : ℝ, (a + h * x - a) / h = x := by
    intro x
    rw [show a + h * x - a = h * x by ring]
    field_simp [hh.ne']
  have hF : A = h⁻¹ * PF := by
    have hcv := Exp2AffineMeasure.setIntegral_comp_affine_Ioo
      (fun y ↦ f y * deriv φ ((y - a) / h)) (a := a) hh
    simp_rw [hinv] at hcv
    simpa [A, PF, smul_eq_mul] using hcv
  have hG : B = h⁻¹ * PG := by
    have hcv := Exp2AffineMeasure.setIntegral_comp_affine_Ioo
      (fun y ↦ g y * φ ((y - a) / h)) (a := a) hh
    simp_rw [hinv] at hcv
    simpa [B, PG, smul_eq_mul] using hcv
  have hweak := hfg ψ
  have hweak' : h⁻¹ * PF = -PG := by
    have hleft :
        (∫ y in Set.Ioo a (a + h), f y * deriv ψ y) = h⁻¹ * PF := by
      dsimp only [PF]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [inverseAffineTestFunction_deriv hh]
      ring
    have hright :
        (∫ y in Set.Ioo a (a + h), g y * ψ y) = PG := by
      apply integral_congr_ae
      filter_upwards with y
      rfl
    simpa [WeakDerivativeOn, cell, hleft, hright] using hweak
  have hPG : PG = h * B := by
    calc
      PG = h * (h⁻¹ * PG) := by field_simp [hh.ne']
      _ = h * B := by rw [← hG]
  have hrel : A = -(h * B) := by
    rw [hF, hweak', hPG]
  have hleftTarget :
      (∫ x in Set.Ioo (0 : ℝ) 1, (c * f (a + h * x)) * deriv φ x) = c * A := by
    dsimp only [A]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hrightTarget :
      (∫ x in Set.Ioo (0 : ℝ) 1, ((c * h) * g (a + h * x)) * φ x) =
        (c * h) * B := by
    dsimp only [B]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hfinal : (∫ x in Set.Ioo (0 : ℝ) 1,
        (c * f (a + h * x)) * deriv φ x) =
      -(∫ x in Set.Ioo (0 : ℝ) 1, ((c * h) * g (a + h * x)) * φ x) := by
    rw [hleftTarget, hrightTarget, hrel]
    ring
  simpa [referenceCell, cell] using hfinal

/-- `MemLp` is preserved by the positive affine pullback to the reference cell. -/
theorem MemLp.affine_comp {p : ℝ≥0∞} {a h : ℝ} (hh : 0 < h) {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (cell a h : Set ℝ))) :
    MemLp (fun x ↦ f (a + h * x)) p (volume.restrict (referenceCell : Set ℝ)) := by
  let μ := volume.restrict (referenceCell : Set ℝ)
  let ν := volume.restrict (cell a h : Set ℝ)
  let c : ℝ≥0∞ := ENNReal.ofReal h⁻¹
  have hmap : Measure.map (fun x : ℝ ↦ a + h * x) μ = c • ν := by
    simpa [μ, ν, c, referenceCell, cell] using
      (Exp2AffineMeasure.map_affine_restrict_Ioo (a := a) hh)
  have hmp : MeasurePreserving (fun x : ℝ ↦ a + h * x) μ (c • ν) :=
    ⟨by fun_prop, hmap⟩
  have hc : c ≠ ∞ := by simp [c]
  have hfc : MemLp f p (c • ν) := hf.smul_measure hc
  simpa [μ, Function.comp_def] using hfc.comp_measurePreserving hmp

theorem SobolevMapOn.continuousOn_affine {n : ℕ} {a h : ℝ} (hh : 0 < h)
    (w : SobolevMapOn n (cell a h)) :
    ContinuousOn (fun x ↦ w (a + h * x)) (closure (referenceCell : Set ℝ)) := by
  apply w.continuousOn.comp (by fun_prop)
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [referenceCell, cell] using hx
  have hTx : a + h * x ∈ Set.Icc a (a + h) := by
    constructor <;> nlinarith [hh, hx'.1, hx'.2]
  change a + h * x ∈ closure (Set.Ioo a (a + h))
  rw [closure_Ioo (by linarith : a ≠ a + h)]
  exact hTx

/-- A positive affine cell map carries every physical-cell Sobolev representative to a reference
representative with the derivative scaling recorded by `IsAffinePullback`. -/
theorem affinePullback_exists {n : ℕ} {a h : ℝ} (hh : 0 < h)
    (w : SobolevMapOn n (cell a h)) :
    ∃ wHat : SobolevMapOn n referenceCell, IsAffinePullback w wHat := by
  let wHat : SobolevMapOn n referenceCell :=
    { toFun := fun x ↦ w (a + h * x)
      derivative := fun j x ↦ h ^ j * w.derivative j (a + h * x)
      derivative_zero := by
        funext x
        simp [w.derivative_zero]
      continuousOn := w.continuousOn_affine hh
      memLp_derivative := by
        intro j hj
        have hcomp := MemLp.affine_comp hh (w.memLp_derivative j hj)
        have hscaled := hcomp.const_smul (h ^ j)
        simpa [Pi.smul_apply, smul_eq_mul] using hscaled
      weakDerivative_succ := by
        intro j hj
        have hweak := WeakDerivativeOn.affine_comp (c := h ^ j) hh
          (w.weakDerivative_succ j hj)
        simpa [pow_succ] using hweak }
  refine ⟨wHat, ?_⟩
  intro j hj
  rfl

/-- The selected affine pullback. -/
def affinePullback {n : ℕ} {a h : ℝ} (hh : 0 < h)
    (w : SobolevMapOn n (cell a h)) : SobolevMapOn n referenceCell :=
  Classical.choose (affinePullback_exists hh w)

/-- The selected pullback has the exact weak-derivative scaling. -/
theorem affinePullback_spec {n : ℕ} {a h : ℝ} (hh : 0 < h)
    (w : SobolevMapOn n (cell a h)) :
    IsAffinePullback w (affinePullback hh w) :=
  Classical.choose_spec (affinePullback_exists hh w)

/-- The physical-cell Gauss--Radau projection induced from the reference projection by the affine
coordinate `xHat = (x-a)/h`. -/
def physicalProjection (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : SobolevMapOn (k + 1) (cell a h)) : ℝ → ℝ :=
  fun x ↦ (gaussRadau k (affinePullback hh w)).1.eval ((x - a) / h)

/-- The exact `L²` change-of-variables identity for the physical projection error. -/
theorem physicalError_l2_scaling (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : SobolevMapOn (k + 1) (cell a h)) :
    l2NormOn (cell a h) (fun x ↦ physicalProjection k hh w x - w x) =
      Real.sqrt h * l2NormOn referenceCell (referenceError k (affinePullback hh w)) := by
  have hpullback := affinePullback_spec hh w
  let f : ℝ → ℝ := fun x ↦ physicalProjection k hh w x - w x
  have hf : AEStronglyMeasurable f
      (volume.restrict (Set.Ioo a (a + h))) := by
    dsimp [f]
    have hw := w.toFun_memLp.aestronglyMeasurable
    have hp : Continuous (physicalProjection k hh w) := by
      unfold physicalProjection
      exact (polynomial_eval_continuous _).comp (by continuity)
    exact hp.aestronglyMeasurable.sub hw
  have hscale := Exp2AffineMeasure.eLpNorm_comp_affine_restrict_Ioo
    (p := (2 : ℝ≥0∞)) f hh hf
  have htrace : ∀ x : ℝ,
      (affinePullback hh w) x = w (a + h * x) := by
    intro x
    have h0 := hpullback 0 (Nat.zero_le (k + 1))
    have h0x := congrFun h0 x
    rw [(affinePullback hh w).derivative_zero, w.derivative_zero] at h0x
    simpa using h0x
  have herr : (fun x : ℝ ↦ f (a + h * x)) =
      referenceError k (affinePullback hh w) := by
    funext x
    dsimp [f, physicalProjection, referenceError]
    rw [htrace x]
    have hx : (a + h * x - a) / h = x := by
      field_simp [ne_of_gt hh]
      ring
    rw [hx]
  dsimp [l2NormOn, cell, referenceCell]
  have hscale' :
      eLpNorm (fun x : ℝ ↦ f (a + h * x)) 2
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
        (ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal •
          eLpNorm f 2 (volume.restrict (Set.Ioo a (a + h))) := hscale
  rw [herr] at hscale'
  have hto := congrArg ENNReal.toReal hscale'
  rw [smul_eq_mul, ENNReal.toReal_mul] at hto
  have hinv : (ENNReal.ofReal h⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal).toReal =
      (Real.sqrt h)⁻¹ := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (inv_nonneg.mpr hh.le)]
    rw [Real.sqrt_eq_rpow]
    norm_num
    exact Real.inv_rpow hh.le _
  rw [hinv] at hto
  have hsqrt : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hmul := congrArg (fun t : ℝ ↦ Real.sqrt h * t) hto
  field_simp [ne_of_gt hsqrt] at hmul
  simpa [f, zero_add] using hmul.symm

/-- The exact order-`k+1` Sobolev-seminorm scaling, written without negative or half powers. -/
theorem sobolevSeminorm_scaling (k : ℕ) {a h : ℝ} (hh : 0 < h)
    (w : SobolevMapOn (k + 1) (cell a h)) :
      Real.sqrt h * sobolevSeminorm (affinePullback hh w) =
      h ^ (k + 1) * sobolevSeminorm w := by
  have hpullback := affinePullback_spec hh w
  let n : ℕ := k + 1
  let g : ℝ → ℝ := fun x ↦ w.derivative n x
  have hg : AEStronglyMeasurable g (volume.restrict (Set.Ioo a (a + h))) :=
    (w.memLp_derivative n (by rfl)).aestronglyMeasurable
  have hscale := Exp2AffineMeasure.eLpNorm_comp_affine_restrict_Ioo
    (p := (2 : ℝ≥0∞)) g hh hg
  have hderiv : (affinePullback hh w).derivative n =
      fun x ↦ h ^ n * g (a + h * x) := by
    exact hpullback n (by dsimp [n]; omega)
  have hscale' :
      eLpNorm (fun x ↦ g (a + h * x)) 2
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
        (ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal •
          eLpNorm g 2 (volume.restrict (Set.Ioo a (a + h))) := hscale
  have hconst := eLpNorm_const_smul (h ^ n : ℝ)
      (fun x ↦ g (a + h * x)) (2 : ℝ≥0∞)
      (volume.restrict (Set.Ioo (0 : ℝ) 1))
  have hcombined :
      eLpNorm (fun x ↦ h ^ n * g (a + h * x)) 2
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) =
        ‖(h ^ n : ℝ)‖ₑ *
          ((ENNReal.ofReal h⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal •
            eLpNorm g 2 (volume.restrict (Set.Ioo a (a + h)))) := by
    have hfun : (fun x ↦ h ^ n * g (a + h * x)) =
        (h ^ n : ℝ) • (fun x ↦ g (a + h * x)) := by
      funext x
      simp [smul_eq_mul]
    rw [hfun, hconst, hscale']
  have hto := congrArg ENNReal.toReal hcombined
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
  dsimp [sobolevSeminorm, l2NormOn, n, g, cell, referenceCell]
  rw [hderiv]
  have hsqrt : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hmul := congrArg (fun t : ℝ ↦ Real.sqrt h * t) hto
  field_simp [ne_of_gt hsqrt] at hmul
  simpa [pow_succ] using hmul

/-- The physical-cell estimate obtained from the reference estimate and the two affine scaling
identities, with the same constant `C`. -/
theorem physical_cell_estimate (k : ℕ) (C : ℝ)
    (href : ∀ w : SobolevMapOn (k + 1) referenceCell,
      l2NormOn referenceCell (referenceError k w) ≤ C * sobolevSeminorm w) :
    ∀ {a h : ℝ} (hh : 0 < h) (w : SobolevMapOn (k + 1) (cell a h)),
      l2NormOn (cell a h) (fun x ↦ physicalProjection k hh w x - w x) ≤
        C * h ^ (k + 1) * sobolevSeminorm w := by
  intro a h hh w
  have hL2 := physicalError_l2_scaling k hh w
  have hHs := sobolevSeminorm_scaling k hh w
  have hRef := href (affinePullback hh w)
  rw [hL2]
  calc
    Real.sqrt h * l2NormOn referenceCell (referenceError k (affinePullback hh w)) ≤
        Real.sqrt h * (C * sobolevSeminorm (affinePullback hh w)) :=
      mul_le_mul_of_nonneg_left hRef (Real.sqrt_nonneg h)
    _ = C * (Real.sqrt h * sobolevSeminorm (affinePullback hh w)) := by ring
    _ = C * (h ^ (k + 1) * sobolevSeminorm w) := by rw [hHs]
    _ = C * h ^ (k + 1) * sobolevSeminorm w := by ring

/-- The complete Exp.2 conclusion: one constant, independent of the function and physical cell,
gives both the reference-cell estimate and its affine physical-cell consequence. -/
theorem main_theorem (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ w : SobolevMapOn (k + 1) referenceCell,
        l2NormOn referenceCell (referenceError k w) ≤ C * sobolevSeminorm w) ∧
      (∀ {a h : ℝ} (hh : 0 < h) (w : SobolevMapOn (k + 1) (cell a h)),
        l2NormOn (cell a h) (fun x ↦ physicalProjection k hh w x - w x) ≤
          C * h ^ (k + 1) * sobolevSeminorm w) := by
  obtain ⟨C, hC, href⟩ := reference_cell_estimate k
  exact ⟨C, hC, href, physical_cell_estimate k C href⟩

end Exp2
