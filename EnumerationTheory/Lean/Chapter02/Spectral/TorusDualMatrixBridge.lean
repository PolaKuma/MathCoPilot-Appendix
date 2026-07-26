import Chapter02.Common
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section

open Classical MeasureTheory
open scoped BigOperators ENNReal

namespace Chapter02.TorusDualMatrixBridge

variable {n : ℕ}

local instance unitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The continuous torus character with integer frequency `k`. -/
def fourierCharacter (k : Fin n → ℤ) :
    ContinuousCircleCharacter (Chapter01.Torus n) where
  toFun := UnitAddTorus.mFourier k
  map_zero := by
    simp [UnitAddTorus.mFourier]
  map_add x y := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
    simp_rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
    exact Finset.prod_mul_distrib
  continuous := (UnitAddTorus.mFourier k).continuous
  unit_norm x := by
    simp [UnitAddTorus.mFourier]

@[simp]
lemma fourierCharacter_apply (k : Fin n → ℤ) (x : Chapter01.Torus n) :
    (fourierCharacter k).toFun x = UnitAddTorus.mFourier k x :=
  rfl

lemma fourierCharacter_add (k : Fin n → ℤ) (x y : Chapter01.Torus n) :
    (fourierCharacter k).toFun (x + y) =
      (fourierCharacter k).toFun x * (fourierCharacter k).toFun y :=
  (fourierCharacter k).map_add x y

def characterContinuousMap
    (χ : ContinuousCircleCharacter (Chapter01.Torus n)) :
    C(UnitAddTorus (Fin n), ℂ) where
  toFun := χ.toFun
  continuous_toFun := χ.continuous

@[simp]
lemma characterContinuousMap_apply
    (χ : ContinuousCircleCharacter (Chapter01.Torus n))
    (x : Chapter01.Torus n) :
    characterContinuousMap χ x = χ.toFun x :=
  rfl

set_option maxHeartbeats 800000 in
lemma exists_ne_zero_mFourierCoeff
    (χ : ContinuousCircleCharacter (Chapter01.Torus n)) :
    ∃ k : Fin n → ℤ,
      UnitAddTorus.mFourierCoeff (characterContinuousMap χ) k ≠ 0 := by
  by_contra h
  push_neg at h
  let F : Lp ℂ 2
      (volume : MeasureTheory.Measure (UnitAddTorus (Fin n))) :=
    ContinuousMap.toLp 2 volume ℂ (characterContinuousMap χ)
  have hrepr : UnitAddTorus.mFourierBasis.repr F = 0 := by
    ext k
    rw [UnitAddTorus.mFourierBasis_repr]
    calc
      UnitAddTorus.mFourierCoeff (fun x => F x) k =
          UnitAddTorus.mFourierCoeff (characterContinuousMap χ) k := by
            exact UnitAddTorus.mFourierCoeff_toLp
              (characterContinuousMap χ) k
      _ = 0 := h k
  have hF : F = 0 := by
    apply UnitAddTorus.mFourierBasis.repr.injective
    simpa using hrepr
  have haeF :
      (fun x => F x) =ᵐ[volume]
        (characterContinuousMap χ : UnitAddTorus (Fin n) → ℂ) :=
    ContinuousMap.coeFn_toLp volume (characterContinuousMap χ)
  have hae0 : (χ.toFun : UnitAddTorus (Fin n) → ℂ) =ᵐ[volume] 0 := by
    have hcoeF0 : (fun x => F x) =ᵐ[volume] 0 := by
      rw [hF]
      exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [haeF, hcoeF0] with x hx hx0
    exact hx.symm.trans hx0
  have hfun : χ.toFun = (fun _ : UnitAddTorus (Fin n) => (0 : ℂ)) :=
    MeasureTheory.Measure.eq_of_ae_eq hae0 χ.continuous continuous_zero
  have hzero := congrFun hfun 0
  rw [χ.map_zero] at hzero
  exact one_ne_zero hzero

lemma character_eq_fourierCharacter
    (χ : ContinuousCircleCharacter (Chapter01.Torus n)) :
    ∃ k : Fin n → ℤ, χ.toFun = (fourierCharacter k).toFun := by
  obtain ⟨k, hk⟩ := exists_ne_zero_mFourierCoeff χ
  refine ⟨k, funext fun y => ?_⟩
  let c : ℂ :=
    UnitAddTorus.mFourierCoeff (characterContinuousMap χ) k
  have hc : c ≠ 0 := hk
  have htranslate :=
    MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure (UnitAddTorus (Fin n))))
      (fun x : UnitAddTorus (Fin n) =>
        UnitAddTorus.mFourier (-k) x * χ.toFun x) y
  have hfactor :
      (UnitAddTorus.mFourier (-k) y * χ.toFun y) * c = c := by
    calc
      (UnitAddTorus.mFourier (-k) y * χ.toFun y) * c =
          ∫ x : UnitAddTorus (Fin n),
            (UnitAddTorus.mFourier (-k) y * χ.toFun y) *
              (UnitAddTorus.mFourier (-k) x * χ.toFun x) := by
                rw [MeasureTheory.integral_const_mul]
                rfl
      _ = ∫ x : UnitAddTorus (Fin n),
            UnitAddTorus.mFourier (-k) (x + y) * χ.toFun (x + y) := by
              apply integral_congr_ae
              exact .of_forall fun x => by
                change
                  (UnitAddTorus.mFourier (-k) y * χ.toFun y) *
                      (UnitAddTorus.mFourier (-k) x * χ.toFun x) =
                    UnitAddTorus.mFourier (-k) (x + y) *
                      χ.toFun (x + y)
                have hf := fourierCharacter_add (-k) x y
                change UnitAddTorus.mFourier (-k) (x + y) =
                  UnitAddTorus.mFourier (-k) x *
                    UnitAddTorus.mFourier (-k) y at hf
                rw [hf, χ.map_add]
                ring
      _ = ∫ x : UnitAddTorus (Fin n),
            UnitAddTorus.mFourier (-k) x * χ.toFun x := htranslate
      _ = c := by
        simp only [c, UnitAddTorus.mFourierCoeff, characterContinuousMap,
          smul_eq_mul]
        rfl
  have hone : UnitAddTorus.mFourier (-k) y * χ.toFun y = 1 := by
    exact (mul_right_cancel₀ hc) (by simpa using hfactor)
  let z : ℂ := UnitAddTorus.mFourier k y
  have hzNorm : ‖z‖ = 1 := by
    simp [z, UnitAddTorus.mFourier]
  have hneg : UnitAddTorus.mFourier (-k) y = star z := by
    simpa [z] using (UnitAddTorus.mFourier_neg (n := k) (x := y))
  have hzstar : z * star z = 1 := by
    rw [mul_comm]
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hzNorm]
    norm_num
  change χ.toFun y = UnitAddTorus.mFourier k y
  change χ.toFun y = z
  calc
    χ.toFun y = 1 * χ.toFun y := by simp
    _ = (z * star z) * χ.toFun y := by rw [hzstar]
    _ = z * (star z * χ.toFun y) := by ring
    _ = z := by rw [← hneg, hone, mul_one]

def dualFrequency (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) :
    Fin n → ℤ :=
  fun j => ∑ i, A i j * k i

lemma coe_toCircle_sum {ι : Type*} [Fintype ι]
    (f : ι → UnitAddCircle) :
    ((AddCircle.toCircle (∑ i, f i) : Circle) : ℂ) =
      ∏ i, ((AddCircle.toCircle (f i) : Circle) : ℂ) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        AddCircle.toCircle_add, Circle.coe_mul, ih]

lemma zpow_sum_fintype {ι : Type*} [Fintype ι]
    (z : ℂ) (hz : z ≠ 0) (e : ι → ℤ) :
    z ^ (∑ i, e i) = ∏ i, z ^ e i := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hz, ih]

lemma mFourier_torusMatrixMap
    (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ)
    (x : Chapter01.Torus n) :
    UnitAddTorus.mFourier k (torusMatrixMap n A x) =
      UnitAddTorus.mFourier (dualFrequency A k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusMatrixMap,
    fourier_apply, dualFrequency]
  simp_rw [AddCircle.toCircle_zsmul]
  simp_rw [Circle.coe_zpow]
  simp_rw [coe_toCircle_sum]
  rw [show (∏ i, (∏ j, ((AddCircle.toCircle (A i j • x j) : Circle) : ℂ)) ^ k i) =
      ∏ i, ∏ j, ((AddCircle.toCircle (A i j • x j) : Circle) : ℂ) ^ k i by
        apply Finset.prod_congr rfl
        intro i _
        simpa using
          (Finset.prod_zpow
            (fun j => ((AddCircle.toCircle (A i j • x j) : Circle) : ℂ))
            Finset.univ (k i)).symm]
  simp_rw [AddCircle.toCircle_zsmul]
  simp_rw [Circle.coe_zpow]
  simp_rw [← zpow_mul]
  rw [Finset.prod_comm]
  simp_rw [zpow_sum_fintype _ (Circle.coe_ne_zero _) _]

lemma mFourier_injective :
    Function.Injective
      (UnitAddTorus.mFourier :
        (Fin n → ℤ) → C(UnitAddTorus (Fin n), ℂ)) := by
  intro k l hkl
  apply UnitAddTorus.orthonormal_mFourier.linearIndependent.injective
  apply Lp.ext
  filter_upwards
      [UnitAddTorus.coeFn_mFourierLp 2 k,
        UnitAddTorus.coeFn_mFourierLp 2 l] with x hk hl
  rw [hk, hl, congrFun (congrArg DFunLike.coe hkl) x]

lemma mFourier_ne_one_iff (k : Fin n → ℤ) :
    (∃ x : Chapter01.Torus n, UnitAddTorus.mFourier k x ≠ 1) ↔
      k ≠ 0 := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    exact hx (by simp [UnitAddTorus.mFourier])
  · intro hk
    by_contra h
    push_neg at h
    have hfun : UnitAddTorus.mFourier k =
        UnitAddTorus.mFourier (0 : Fin n → ℤ) := by
      ext x
      rw [h x]
      simp [UnitAddTorus.mFourier]
    exact hk (mFourier_injective hfun)

lemma mFourier_torusMatrixMap_iterate
    (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) (q : ℕ)
    (x : Chapter01.Torus n) :
    UnitAddTorus.mFourier k ((torusMatrixMap n A)^[q] x) =
      UnitAddTorus.mFourier ((dualFrequency A)^[q] k) x := by
  induction q generalizing k x with
  | zero => rfl
  | succ q ih =>
      rw [Function.iterate_succ_apply']
      rw [mFourier_torusMatrixMap]
      rw [ih]
      rw [Function.iterate_succ_apply]

lemma fourier_periodic_iff
    (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) (q : ℕ) :
    (fun x => UnitAddTorus.mFourier k
      ((torusMatrixMap n A)^[q] x)) =
        UnitAddTorus.mFourier k ↔
      (dualFrequency A)^[q] k = k := by
  constructor
  · intro h
    apply mFourier_injective
    ext x
    rw [← mFourier_torusMatrixMap_iterate]
    exact congrFun h x
  · intro h
    funext x
    rw [mFourier_torusMatrixMap_iterate, h]

lemma dualFrequency_eq_transpose_mulVec
    (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) :
    dualFrequency A k = A.transpose.mulVec k := by
  ext j
  simp [dualFrequency, Matrix.mulVec, dotProduct]

lemma dualFrequency_iterate_eq
    (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n → ℤ) (q : ℕ) :
    (dualFrequency A)^[q] k = (A.transpose ^ q).mulVec k := by
  induction q generalizing k with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply, ih, dualFrequency_eq_transpose_mulVec,
        pow_succ, Matrix.mulVec_mulVec]

private def complexMatrix (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℂ :=
  A.map (Int.castRingHom ℂ)

private def complexOperator (A : Matrix (Fin n) (Fin n) ℤ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  (complexMatrix A).toLin'.toContinuousLinearMap

lemma complexMatrix_pow
    (A : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    (complexMatrix A) ^ q = complexMatrix (A ^ q) :=
  (Matrix.map_pow A (Int.castRingHom ℂ) q).symm

lemma complexOperator_pow
    (A : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    (complexOperator A) ^ q =
      ((complexMatrix A) ^ q).toLin'.toContinuousLinearMap := by
  induction q with
  | zero =>
      apply ContinuousLinearMap.ext
      intro x
      simp
  | succ q ih =>
      apply ContinuousLinearMap.ext
      intro x
      rw [pow_succ, ContinuousLinearMap.mul_def, ih]
      simp [complexOperator, Matrix.toLin'_apply, pow_succ]

lemma complexOperator_pow_eq
    (A : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    (complexOperator A) ^ q = complexOperator (A ^ q) := by
  rw [complexOperator_pow, complexMatrix_pow]
  rfl

lemma mem_spectrum_complexOperator_iff
    (A : Matrix (Fin n) (Fin n) ℤ) (lam : ℂ) :
    lam ∈ spectrum ℂ (complexOperator A) ↔
      lam ∈ spectrum ℂ (complexMatrix A) := by
  rw [← Matrix.spectrum_toLin']
  rw [spectrum.mem_iff, spectrum.mem_iff]
  simp only [ContinuousLinearMap.isUnit_iff_bijective,
    Module.End.isUnit_iff]
  rfl

lemma hasRootOfUnityEigenvalue_iff_spectrum
    (A : Matrix (Fin n) (Fin n) ℤ) :
    Chapter02.HasRootOfUnityEigenvalue A ↔
      ∃ lam : ℂ, (∃ q : ℕ, 0 < q ∧ lam ^ q = 1) ∧
        lam ∈ spectrum ℂ (complexMatrix A) := by
  constructor
  · rintro ⟨lam, hlam, v, hv, hAv⟩
    refine ⟨lam, hlam, ?_⟩
    have heq : (complexMatrix A).toLin' v = lam • v := by
      ext i
      simpa [complexMatrix, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct] using hAv i
    have hvec :
        Module.End.HasEigenvector (complexMatrix A).toLin' lam v :=
      ⟨Module.End.mem_eigenspace_iff.mpr heq, hv⟩
    have heig :=
      Module.End.hasEigenvalue_of_hasEigenvector hvec
    simpa using Module.End.HasEigenvalue.mem_spectrum heig
  · rintro ⟨lam, hlam, hspectrum⟩
    have hspectrum' :
        lam ∈ spectrum ℂ (complexMatrix A).toLin' := by
      simpa using hspectrum
    obtain ⟨v, hv⟩ :=
      (Module.End.HasEigenvalue.of_mem_spectrum hspectrum').exists_hasEigenvector
    refine ⟨lam, hlam, v, hv.2, fun i => ?_⟩
    have hi := congrFun hv.apply_eq_smul i
    simpa [complexMatrix, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct] using hi

lemma one_mem_spectrum_iff_det_sub_one
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (1 : ℂ) ∈ spectrum ℂ M ↔ (M - 1).det = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  simp only [Polynomial.IsRoot, Matrix.eval_charpoly]
  rw [show (Matrix.scalar (Fin n) (1 : ℂ) - M) = -(M - 1) by
    ext i j
    simp [Matrix.scalar_apply]]
  rw [Matrix.det_neg]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · intro h
    rw [h, mul_zero]

lemma complexMatrix_pow_sub_one_det
    (A : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    ((complexMatrix A) ^ q - 1).det =
      ((A ^ q - 1).det : ℂ) := by
  rw [show (complexMatrix A) ^ q - 1 =
      complexMatrix (A ^ q - 1) by
    change (A.map (Int.castRingHom ℂ)) ^ q - 1 =
      (A ^ q - 1).map (Int.castRingHom ℂ)
    rw [← Matrix.map_pow A (Int.castRingHom ℂ) q]
    ext i j
    simp [Matrix.one_apply]]
  exact (RingHom.map_det (Int.castRingHom ℂ) (A ^ q - 1)).symm

lemma exists_dual_fixed_iff_det_sub_one
    (A : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) :
    (∃ k : Fin n → ℤ, k ≠ 0 ∧
        (A.transpose ^ q).mulVec k = k) ↔
      (A ^ q - 1).det = 0 := by
  have hmatrix :
      (A.transpose ^ q) - 1 = (A ^ q - 1).transpose := by
    rw [Matrix.transpose_sub, Matrix.transpose_pow, Matrix.transpose_one]
  constructor
  · rintro ⟨k, hk, hfixed⟩
    have hzero :
        ((A.transpose ^ q) - 1).mulVec k = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfixed, sub_self]
    have hdet :
        ((A.transpose ^ q) - 1).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨k, hk, hzero⟩
    rw [hmatrix, Matrix.det_transpose] at hdet
    exact hdet
  · intro hdet
    have hdet' :
        ((A.transpose ^ q) - 1).det = 0 := by
      rw [hmatrix, Matrix.det_transpose]
      exact hdet
    obtain ⟨k, hk, hzero⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
    refine ⟨k, hk, ?_⟩
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hzero

lemma hasRootOfUnityEigenvalue_iff_periodic_frequency
    (A : Matrix (Fin n) (Fin n) ℤ) :
    Chapter02.HasRootOfUnityEigenvalue A ↔
      ∃ k : Fin n → ℤ, k ≠ 0 ∧
        ∃ q : ℕ, 0 < q ∧ (dualFrequency A)^[q] k = k := by
  constructor
  · intro hroot
    obtain ⟨lam, ⟨q, hq, hlam⟩, v, hv, hAv⟩ := hroot
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    letI : Nonempty (Fin n) := ⟨i⟩
    obtain ⟨lam, ⟨q, hq, hlam⟩, hspectrum⟩ :=
      (hasRootOfUnityEigenvalue_iff_spectrum A).mp
        ⟨lam, ⟨q, hq, hlam⟩, v, hv, hAv⟩
    have hspectrumOp :
        lam ∈ spectrum ℂ (complexOperator A) := by
      exact (mem_spectrum_complexOperator_iff A lam).mpr hspectrum
    have honeOp :
        (1 : ℂ) ∈ spectrum ℂ ((complexOperator A) ^ q) := by
      rw [spectrum.map_pow (complexOperator A) q]
      exact ⟨lam, hspectrumOp, hlam⟩
    have hone :
        (1 : ℂ) ∈ spectrum ℂ ((complexMatrix A) ^ q) := by
      have honeAq :
          (1 : ℂ) ∈ spectrum ℂ (complexOperator (A ^ q)) := by
        rw [← complexOperator_pow_eq]
        exact honeOp
      rw [complexMatrix_pow]
      exact (mem_spectrum_complexOperator_iff (A := A ^ q) 1).mp honeAq
    have hdetC :
        (((complexMatrix A) ^ q) - 1).det = 0 :=
      (one_mem_spectrum_iff_det_sub_one _).mp hone
    rw [complexMatrix_pow_sub_one_det] at hdetC
    have hdetZ : (A ^ q - 1).det = 0 := by
      exact_mod_cast hdetC
    obtain ⟨k, hk, hfixed⟩ :=
      (exists_dual_fixed_iff_det_sub_one A q).mpr hdetZ
    refine ⟨k, hk, q, hq, ?_⟩
    rw [dualFrequency_iterate_eq]
    exact hfixed
  · rintro ⟨k, hk, q, hq, hfixed⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    letI : Nonempty (Fin n) := ⟨i⟩
    have hmatrixFixed :
        (A.transpose ^ q).mulVec k = k := by
      rw [← dualFrequency_iterate_eq]
      exact hfixed
    have hdetZ : (A ^ q - 1).det = 0 :=
      (exists_dual_fixed_iff_det_sub_one A q).mp
        ⟨k, hk, hmatrixFixed⟩
    have hdetC :
        (((complexMatrix A) ^ q) - 1).det = 0 := by
      rw [complexMatrix_pow_sub_one_det]
      exact_mod_cast hdetZ
    have hone :
        (1 : ℂ) ∈ spectrum ℂ ((complexMatrix A) ^ q) :=
      (one_mem_spectrum_iff_det_sub_one _).mpr hdetC
    have honeOp :
        (1 : ℂ) ∈ spectrum ℂ ((complexOperator A) ^ q) := by
      rw [complexOperator_pow_eq]
      apply (mem_spectrum_complexOperator_iff (A := A ^ q) 1).mpr
      rw [← complexMatrix_pow]
      exact hone
    rw [spectrum.map_pow (complexOperator A) q] at honeOp
    obtain ⟨lam, hspectrumOp, hlam⟩ := honeOp
    have hspectrum :
        lam ∈ spectrum ℂ (complexMatrix A) := by
      exact (mem_spectrum_complexOperator_iff A lam).mp hspectrumOp
    exact (hasRootOfUnityEigenvalue_iff_spectrum A).mpr
      ⟨lam, ⟨q, hq, hlam⟩, hspectrum⟩

theorem torus_rootOfUnity_iff_periodic_nontrivial_character
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    Chapter02.HasRootOfUnityEigenvalue A ↔
      ∃ χ : Chapter02.ContinuousCircleCharacter (Chapter01.Torus n),
        (∃ q : ℕ, 0 < q ∧
          (fun x => χ.toFun
            ((Chapter02.torusMatrixMap n A)^[q] x)) = χ.toFun) ∧
        ∃ x, χ.toFun x ≠ 1 := by
  constructor
  · intro hroot
    obtain ⟨k, hk, q, hq, hfixed⟩ :=
      (hasRootOfUnityEigenvalue_iff_periodic_frequency A).mp hroot
    refine ⟨fourierCharacter k, ⟨q, hq, ?_⟩, ?_⟩
    · exact (fourier_periodic_iff A k q).mpr hfixed
    · exact (mFourier_ne_one_iff k).mpr hk
  · rintro ⟨χ, ⟨q, hq, hperiodic⟩, x, hx⟩
    obtain ⟨k, hχ⟩ := character_eq_fourierCharacter χ
    rw [hχ] at hperiodic hx
    have hk : k ≠ 0 :=
      (mFourier_ne_one_iff k).mp ⟨x, hx⟩
    have hfixed :
        (dualFrequency A)^[q] k = k :=
      (fourier_periodic_iff A k q).mp hperiodic
    exact (hasRootOfUnityEigenvalue_iff_periodic_frequency A).mpr
      ⟨k, hk, q, hq, hfixed⟩

end Chapter02.TorusDualMatrixBridge
