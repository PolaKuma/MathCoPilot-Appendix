import Chapter02.Recurrence.BohrWeightedUniform

open Classical
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Chapter02.ForwardKroneckerBohr

universe u

open BohrWeightedUniform

/-- The scalar matrix coefficient of the forward orbit of one Hilbert
vector. -/
def orbitMatrixCoefficient
    (D : HilbertOperatorData.{u}) (x : D.H) (n : ℕ) : ℂ :=
  @inner ℂ D.H _ x ((D.U^[n]) x)

/-- The time-zero orbit matrix coefficient is the squared norm. -/
lemma orbitMatrixCoefficient_zero
    (D : HilbertOperatorData.{u}) (x : D.H) :
    orbitMatrixCoefficient D x 0 = (‖x‖ ^ 2 : ℂ) := by
  unfold orbitMatrixCoefficient
  simpa only [Function.iterate_zero_apply] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x)

/-- Every orbit matrix coefficient of a linear isometry is bounded by its
time-zero squared norm. -/
lemma norm_orbitMatrixCoefficient_le
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (n : ℕ) :
    ‖orbitMatrixCoefficient D x n‖ ≤ ‖x‖ ^ 2 := by
  unfold orbitMatrixCoefficient
  calc
    ‖@inner ℂ D.H _ x ((D.U^[n]) x)‖ ≤
        ‖x‖ * ‖(D.U^[n]) x‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖x‖ := by
      rw [AlmostPeriodicIsometry.iterate_norm D hU]
    _ = ‖x‖ ^ 2 := by ring

/-- The squared orbit-return distance is exactly the loss in the real part
of the normalized matrix coefficient. -/
lemma norm_iterate_sub_sq_eq
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (n : ℕ) :
    ‖(D.U^[n]) x - x‖ ^ 2 =
      2 * (‖x‖ ^ 2 - (orbitMatrixCoefficient D x n).re) := by
  let y : D.H := (D.U^[n]) x
  have hyNorm : ‖y‖ = ‖x‖ :=
    AlmostPeriodicIsometry.iterate_norm D hU x n
  have hxx :
      (@inner ℂ D.H _ x x).re = ‖x‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  have hyy :
      (@inner ℂ D.H _ y y).re = ‖x‖ ^ 2 := by
    have hyself :
        (@inner ℂ D.H _ y y).re = ‖y‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) y)
    rw [hyself, hyNorm]
  have hyx :
      (@inner ℂ D.H _ y x).re =
        (@inner ℂ D.H _ x y).re :=
    by
      exact @inner_re_symm ℂ D.H _ _ _ y x
  change
    ‖y - x‖ ^ 2 =
      2 * (‖x‖ ^ 2 - (@inner ℂ D.H _ x y).re)
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [map_sub]
  change
    (@inner ℂ D.H _ y y).re - (@inner ℂ D.H _ y x).re -
        ((@inner ℂ D.H _ x y).re - (@inner ℂ D.H _ x x).re) =
      2 * (‖x‖ ^ 2 - (@inner ℂ D.H _ x y).re)
  rw [hxx, hyy, hyx]
  ring

/-- After division by its positive time-zero value, every orbit matrix
coefficient of a nonzero isometric vector lies in the closed unit disk. -/
lemma norm_normalizedOrbitMatrixCoefficient_le_one
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : x ≠ 0) (n : ℕ) :
    ‖((‖x‖ ^ 2 : ℂ)⁻¹) * orbitMatrixCoefficient D x n‖ ≤ 1 := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hQ : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hxnorm
  have hcastnorm : ‖((‖x‖ : ℂ) ^ 2)‖ = ‖x‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x)]
  rw [norm_mul, norm_inv, hcastnorm]
  calc
    (‖x‖ ^ 2)⁻¹ * ‖orbitMatrixCoefficient D x n‖ ≤
        (‖x‖ ^ 2)⁻¹ * (‖x‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (norm_orbitMatrixCoefficient_le D hU x n)
        (inv_nonneg.mpr hQ.le)
    _ = 1 := inv_mul_cancel₀ hQ.ne'

/-- The unit-circle eigenvalue attached to an eigenvector of a linear
isometry; surjectivity is not required. -/
def isometricEigenCircle
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (y : D.H) (hy : IsEigenvector D y) : Circle :=
  ⟨AlmostPeriodic.eigenvalueOf D y hy,
    mem_sphere_zero_iff_norm.mpr
      (AlmostPeriodicIsometry.eigenvalue_norm_one
        D hU y hy.1 (AlmostPeriodic.eigenvalueOf D y hy)
        (AlmostPeriodic.eigenvalueOf_spec D y hy))⟩

/-- A matrix coefficient coming from a finite combination of eigenvectors
is an exact finite circle-character polynomial. -/
lemma finiteEigenCombination_orbitMatrixCoefficient_isFinite
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (s : Finset D.H) (hs : ∀ y ∈ s, IsEigenvector D y)
    (c : D.H → ℂ) :
    IsFiniteCirclePolynomial
      (orbitMatrixCoefficient D (∑ y ∈ s, c y • y)) := by
  let V : D.H := ∑ y ∈ s, c y • y
  let coeff : (y : s) → ℂ :=
    fun y ↦ c y.1 * @inner ℂ D.H _ V y.1
  let phase : (y : s) → Circle :=
    fun y ↦ isometricEigenCircle D hU y.1 (hs y.1 y.2)
  have hfinite :=
    isFiniteCirclePolynomial_fintype coeff phase
  convert hfinite using 1
  funext n
  unfold orbitMatrixCoefficient
  change
    @inner ℂ D.H _ V ((D.U^[n]) V) =
      fintypeCirclePolynomial coeff phase n
  dsimp only [V]
  rw [AlmostPeriodic.iterate_finset_sum, inner_sum]
  unfold fintypeCirclePolynomial
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro y hy
  have hiter (v : D.H) : (D.U ^ n) v = (D.U^[n]) v := by
    rw [ContinuousLinearMap.coe_pow]
  rw [← hiter, map_smul, hiter]
  rw [SpectralPointMass.eigen_iterate D y
    (AlmostPeriodic.eigenvalueOf D y (hs y y.property))
    (AlmostPeriodic.eigenvalueOf_spec D y (hs y y.property))]
  rw [smul_smul, inner_smul_right]
  dsimp [coeff, phase, isometricEigenCircle]
  ring

/-- Uniform perturbation bound for orbit matrix coefficients of a unitary
operator. -/
lemma norm_orbitMatrixCoefficient_sub_le
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x y : D.H) (n : ℕ) :
    ‖orbitMatrixCoefficient D x n -
        orbitMatrixCoefficient D y n‖ ≤
      ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have hdecomp :
      orbitMatrixCoefficient D x n -
          orbitMatrixCoefficient D y n =
        @inner ℂ D.H _ (x - y) ((D.U^[n]) x) +
          @inner ℂ D.H _ y
            ((D.U^[n]) x - (D.U^[n]) y) := by
    unfold orbitMatrixCoefficient
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hdecomp]
  calc
    ‖_ + _‖ ≤
        ‖@inner ℂ D.H _ (x - y) ((D.U^[n]) x)‖ +
          ‖@inner ℂ D.H _ y
            ((D.U^[n]) x - (D.U^[n]) y)‖ :=
      norm_add_le _ _
    _ ≤
        ‖x - y‖ * ‖(D.U^[n]) x‖ +
          ‖y‖ * ‖(D.U^[n]) x - (D.U^[n]) y‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ := by
      rw [AlmostPeriodicIsometry.iterate_norm D hU,
        AlmostPeriodicIsometry.iterate_sub_norm D hU]
    _ = ‖x - y‖ * (‖x‖ + ‖y‖) := by ring

/-- The orbit matrix coefficient of every almost-periodic unitary vector is
a uniform limit of finite circle-character polynomials. -/
theorem almostPeriodic_orbitMatrixCoefficient_isUniformLimit
    (D : HilbertOperatorData.{u})
    (hU : ∀ x : D.H, ‖D.U x‖ = ‖x‖)
    (x : D.H) (hx : IsAlmostPeriodicVector D x) :
    IsUniformLimitOfFiniteCirclePolynomials
      (orbitMatrixCoefficient D x) := by
  have hxDiscrete :
      InDiscreteSpectralSubspace D x :=
    AlmostPeriodicIsometry.almostPeriodic_implies_discrete D hU x hx
  intro δ hδ
  let K : ℝ := 2 * ‖x‖ + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let η : ℝ := min 1 (δ / (2 * K))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by norm_num) (div_pos hδ (by positivity))
  have hηone : η ≤ 1 := min_le_left _ _
  have hηK : η * K ≤ δ / 2 := by
    calc
      η * K ≤ (δ / (2 * K)) * K := by
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) hK.le
      _ = δ / 2 := by field_simp
  obtain ⟨s, hs, c, happrox⟩ := hxDiscrete η hη
  let V : D.H := ∑ y ∈ s, c y • y
  refine ⟨orbitMatrixCoefficient D V,
    finiteEigenCombination_orbitMatrixCoefficient_isFinite
      D hU s hs c, ?_⟩
  intro n
  have hVnorm : ‖V‖ ≤ ‖x‖ + 1 := by
    calc
      ‖V‖ = ‖(V - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖V - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ η + ‖x‖ := by
        exact add_le_add_left
          (by simpa [V, norm_sub_rev] using happrox.le) _
      _ ≤ ‖x‖ + 1 := by linarith
  calc
    ‖orbitMatrixCoefficient D x n -
        orbitMatrixCoefficient D V n‖ ≤
      ‖x - V‖ * (‖x‖ + ‖V‖) :=
        norm_orbitMatrixCoefficient_sub_le D hU x V n
    _ ≤ η * K := by
      apply mul_le_mul happrox.le
      · dsimp [K]
        linarith
      · positivity
      · exact hη.le
    _ ≤ δ / 2 := hηK
    _ < δ := by linarith

/-- Autocorrelation of the forward-Kronecker projection vector. -/
def forwardKroneckerAutocorrelation
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) : ℂ :=
  orbitMatrixCoefficient
    (MultipleKhintchineCharacteristic.KData M hM.1)
    (ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA) n

/-- The forward-Kronecker autocorrelation is a Bohr-uniform limit of
finite circle-character polynomials. -/
theorem forwardKroneckerAutocorrelation_isUniformLimit
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    IsUniformLimitOfFiniteCirclePolynomials
      (forwardKroneckerAutocorrelation M hM A hA) := by
  let D := MultipleKhintchineCharacteristic.KData M hM.1
  let G : D.H :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map X
  have hGap : IsAlmostPeriodicVector D G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp_almostPeriodic
      M hM A hA
  exact almostPeriodic_orbitMatrixCoefficient_isUniformLimit
    D hU G hGap

/-- Positive measure forces the forward-Kronecker projection vector to be
nonzero. -/
lemma forwardKroneckerIndicatorLp_ne_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A) :
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA ≠ 0 := by
  letI : MeasureTheory.IsProbabilityMeasure M.μ := hM.1.1
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let hGtop :=
    MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_mem_top
      M hM A hA
  let P :=
    MultipleKhintchineKronecker.lpPointwiseMul G G hGtop
  have hbase :
      (realMeasure M A) ^ 3 ≤
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G P).re := by
    rw [ForwardKroneckerFactor.re_inner_forwardKroneckerIndicatorLp_self_eq_cube_integral
      M hM A hA]
    exact
      ForwardKroneckerFactor.cube_integral_condExp_indicator_lower_bound
        M hM A hA
  have hrealpos : 0 < realMeasure M A := by
    unfold realMeasure
    exact ENNReal.toReal_pos hApos.ne'
      (MeasureTheory.measure_ne_top M.μ A)
  intro hzero
  change G = 0 at hzero
  have hout :
      @inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G P = 0 := by
    rw [hzero]
    simp
  rw [hout, Complex.zero_re] at hbase
  nlinarith [pow_pos hrealpos 3]

/-- The forward-Kronecker triple correlation is Lipschitz in the first two
orbit slots around time zero. -/
lemma abs_forwardKroneckerTripleCorrelation_sub_zero_le
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    |ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA n -
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA 0| ≤
      ‖ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA‖ *
        (‖(show MeasureTheory.Lp ℂ 2 M.μ from
              ((MultipleKhintchineCharacteristic.KData M hM.1).U^[2 * n])
                (ForwardKroneckerFactor.forwardKroneckerIndicatorLp
                  M hM A hA)) -
            ForwardKroneckerFactor.forwardKroneckerIndicatorLp
              M hM A hA‖ +
          ‖(show MeasureTheory.Lp ℂ 2 M.μ from
              ((MultipleKhintchineCharacteristic.KData M hM.1).U^[n])
                (ForwardKroneckerFactor.forwardKroneckerIndicatorLp
                  M hM A hA)) -
            ForwardKroneckerFactor.forwardKroneckerIndicatorLp
              M hM A hA‖) := by
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  let F : MeasureTheory.Lp ℂ 2 M.μ :=
    ((MultipleKhintchineCharacteristic.KData M hM.1).U^[n]) G
  let H : MeasureTheory.Lp ℂ 2 M.μ :=
    ((MultipleKhintchineCharacteristic.KData M hM.1).U^[2 * n]) G
  have hFtop :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp_iterate_mem_top
      M hM A hA n
  have hGtop :=
    MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_mem_top
      M hM A hA
  have hFbound :
      ∀ᵐ x ∂M.μ, ‖F x‖ ≤ (1 : ℝ) := by
    simpa only [F, G] using
      ForwardKroneckerFactor.forwardKroneckerIndicatorLp_iterate_norm_le_one
        M hM A hA n
  have hGbound :
      ∀ᵐ x ∂M.μ, ‖G x‖ ≤ (1 : ℝ) :=
    MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_norm_le_one
      M hM A hA
  have hpert :=
    MultipleKhintchineKronecker.abs_re_inner_lpPointwiseMul_sub_self_le
      F G H hFtop hGtop hFbound hGbound
  simpa only [
    ForwardKroneckerFactor.forwardKroneckerTripleCorrelation,
    G, F, H, Nat.zero_mul, Function.iterate_zero_apply] using hpert

/-- A single near-return controls the structured triple correlation, since
the double-time return costs at most twice as much. -/
lemma abs_forwardKroneckerTripleCorrelation_sub_zero_le_three
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) :
    |ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA n -
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA 0| ≤
      3 *
        ‖ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA‖ *
        ‖(show MeasureTheory.Lp ℂ 2 M.μ from
            ((MultipleKhintchineCharacteristic.KData M hM.1).U^[n])
              (ForwardKroneckerFactor.forwardKroneckerIndicatorLp
                M hM A hA)) -
            ForwardKroneckerFactor.forwardKroneckerIndicatorLp
              M hM A hA‖ := by
  let D := MultipleKhintchineCharacteristic.KData M hM.1
  let G : D.H :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map X
  have htwo :=
    AlmostPeriodicIsometry.iterate_mul_sub_norm_le D hU G n 2
  have hbase :=
    abs_forwardKroneckerTripleCorrelation_sub_zero_le
      M hM A hA n
  change
    |ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA n -
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA 0| ≤
      3 * ‖G‖ * ‖(D.U^[n]) G - G‖
  calc
    |ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA n -
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
          M hM A hA 0| ≤
        ‖G‖ *
          (‖(D.U^[2 * n]) G - G‖ + ‖(D.U^[n]) G - G‖) := hbase
    _ ≤ ‖G‖ *
          (2 * ‖(D.U^[n]) G - G‖ + ‖(D.U^[n]) G - G‖) := by
      gcongr
      simpa using htwo
    _ = 3 * ‖G‖ * ‖(D.U^[n]) G - G‖ := by ring

/-- At time zero the structured triple correlation dominates the cubic
Khintchine benchmark. -/
lemma cube_le_forwardKroneckerTripleCorrelation_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    (realMeasure M A) ^ 3 ≤
      ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
        M hM A hA 0 := by
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hGtop :=
    MultipleKhintchineCharacteristic.forwardKroneckerIndicatorLp_mem_top
      M hM A hA
  have hbase :
      (realMeasure M A) ^ 3 ≤
        (@inner ℂ (MeasureTheory.Lp ℂ 2 M.μ) _ G
          (MultipleKhintchineKronecker.lpPointwiseMul G G hGtop)).re := by
    rw [ForwardKroneckerFactor.re_inner_forwardKroneckerIndicatorLp_self_eq_cube_integral
      M hM A hA]
    exact
      ForwardKroneckerFactor.cube_integral_condExp_indicator_lower_bound
        M hM A hA
  simpa only [
    ForwardKroneckerFactor.forwardKroneckerTripleCorrelation,
    G, Nat.zero_mul, Function.iterate_zero_apply] using hbase

/-- The affine peak base used to localize an autocorrelation near its
time-zero value. -/
def peakBase (q : ℕ → ℂ) (r : ℂ) (n : ℕ) : ℂ :=
  (1 + r * q n) / 2

/-- A nonnegative polynomial peak built from an autocorrelation.  For the
application, `r` is the inverse of the positive time-zero value. -/
def peakWeight (q : ℕ → ℂ) (r : ℂ) (k n : ℕ) : ℂ :=
  (peakBase q r n * conj (peakBase q r n)) ^ k

/-- A peak weight is the real nonnegative power of the squared norm of its
base. -/
lemma peakWeight_eq_norm_sq_pow
    (q : ℕ → ℂ) (r : ℂ) (k n : ℕ) :
    peakWeight q r k n =
      (((‖peakBase q r n‖ ^ 2) ^ k : ℝ) : ℂ) := by
  unfold peakWeight
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- The normalized affine base of a point in the closed unit disk has norm
at most one. -/
lemma norm_peakBase_le_one_of_norm_le
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(1 + z) / 2‖ ≤ 1 := by
  rw [norm_div]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo, div_le_one (by norm_num : (0 : ℝ) < 2)]
  calc
    ‖1 + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by simpa using add_le_add_left hz 1
    _ = 2 := by norm_num

/-- Squared-norm refinement of the affine unit-disk estimate. -/
lemma norm_sq_peakBase_le_of_norm_le
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(1 + z) / 2‖ ^ 2 ≤ (1 + z.re) / 2 := by
  have hnormsq : ‖z‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg z]
  have hzsq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    rw [pow_two, pow_two]
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
    exact hnormsq
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  norm_num [Complex.div_re, Complex.div_im]
  nlinarith

/-- Affine peak bases preserve Bohr uniform approximability. -/
lemma peakBase_isUniformLimit
    (q : ℕ → ℂ) (r : ℂ)
    (hq : IsUniformLimitOfFiniteCirclePolynomials q) :
    IsUniformLimitOfFiniteCirclePolynomials (peakBase q r) := by
  have hone :=
    isUniformLimitOfFiniteCirclePolynomials_const (1 : ℂ)
  have hrq := hq.const_mul r
  have hsum := hone.add hrq
  have hhalf := hsum.const_mul ((2 : ℂ)⁻¹)
  convert hhalf using 1
  funext n
  unfold peakBase
  ring

/-- Polynomial autocorrelation peaks are Bohr uniform limits. -/
lemma peakWeight_isUniformLimit
    (q : ℕ → ℂ) (r : ℂ) (k : ℕ)
    (hq : IsUniformLimitOfFiniteCirclePolynomials q) :
    IsUniformLimitOfFiniteCirclePolynomials (peakWeight q r k) := by
  have hb := peakBase_isUniformLimit q r hq
  have hsq := hb.mul hb.star
  have hk := hsq.pow k
  exact hk

/-- The forward-Kronecker autocorrelation normalized by its positive
time-zero value. -/
def normalizedForwardKroneckerAutocorrelation
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (n : ℕ) : ℂ :=
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  ((‖G‖ ^ 2 : ℂ)⁻¹) *
    forwardKroneckerAutocorrelation M hM A hA n

/-- The normalized forward-Kronecker autocorrelation remains a Bohr
uniform limit. -/
lemma normalizedForwardKroneckerAutocorrelation_isUniformLimit
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) :
    IsUniformLimitOfFiniteCirclePolynomials
      (normalizedForwardKroneckerAutocorrelation M hM A hA) := by
  let G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hq :=
    forwardKroneckerAutocorrelation_isUniformLimit M hM A hA
  have hscaled := hq.const_mul ((‖G‖ ^ 2 : ℂ)⁻¹)
  simpa only [normalizedForwardKroneckerAutocorrelation, G] using hscaled

/-- Positive measure makes the normalized autocorrelation equal to one at
time zero. -/
lemma normalizedForwardKroneckerAutocorrelation_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A) :
    normalizedForwardKroneckerAutocorrelation M hM A hA 0 = 1 := by
  let D := MultipleKhintchineCharacteristic.KData M hM.1
  let G : D.H :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hG : G ≠ 0 :=
    forwardKroneckerIndicatorLp_ne_zero M hM A hA hApos
  have hQ : (‖G‖ ^ 2 : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr hG))
  change
    ((‖G‖ ^ 2 : ℂ)⁻¹) * orbitMatrixCoefficient D G 0 = 1
  rw [orbitMatrixCoefficient_zero]
  exact inv_mul_cancel₀ hQ

/-- Every normalized forward-Kronecker autocorrelation value lies in the
closed unit disk. -/
lemma norm_normalizedForwardKroneckerAutocorrelation_le_one
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A) (n : ℕ) :
    ‖normalizedForwardKroneckerAutocorrelation M hM A hA n‖ ≤ 1 := by
  let D := MultipleKhintchineCharacteristic.KData M hM.1
  let G : D.H :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map X
  have hG : G ≠ 0 :=
    forwardKroneckerIndicatorLp_ne_zero M hM A hA hApos
  change
    ‖((‖G‖ ^ 2 : ℂ)⁻¹) * orbitMatrixCoefficient D G n‖ ≤ 1
  exact norm_normalizedOrbitMatrixCoefficient_le_one D hU G hG n

/-- The real-part deficit of the normalized autocorrelation is exactly the
squared return distance, after clearing the positive denominator. -/
lemma two_norm_sq_mul_one_sub_normalized_re_eq
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A) (n : ℕ) :
    let D := MultipleKhintchineCharacteristic.KData M hM.1
    let G : D.H :=
      ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
    2 * ‖G‖ ^ 2 *
        (1 -
          (normalizedForwardKroneckerAutocorrelation M hM A hA n).re) =
      ‖(D.U^[n]) G - G‖ ^ 2 := by
  let D := MultipleKhintchineCharacteristic.KData M hM.1
  let G : D.H :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map X
  have hG : G ≠ 0 :=
    forwardKroneckerIndicatorLp_ne_zero M hM A hA hApos
  have hQ : ‖G‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hG)
  have hinv :
      ((‖G‖ ^ 2 : ℂ)⁻¹) = (((‖G‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    norm_cast
  have hreal :
      (normalizedForwardKroneckerAutocorrelation M hM A hA n).re =
        (‖G‖ ^ 2)⁻¹ * (orbitMatrixCoefficient D G n).re := by
    change
      (((‖G‖ ^ 2 : ℂ)⁻¹) *
          orbitMatrixCoefficient D G n).re =
        (‖G‖ ^ 2)⁻¹ * (orbitMatrixCoefficient D G n).re
    rw [hinv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hdist := norm_iterate_sub_sq_eq D hU G n
  change
    2 * ‖G‖ ^ 2 *
        (1 -
          (normalizedForwardKroneckerAutocorrelation M hM A hA n).re) =
      ‖(D.U^[n]) G - G‖ ^ 2
  rw [hreal, hdist]
  field_simp

/-- The specialized nonnegative Bohr peak used for the triple recurrence
argument. -/
def forwardKroneckerPeakWeight
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (k n : ℕ) : ℂ :=
  peakWeight
    (normalizedForwardKroneckerAutocorrelation M hM A hA) 1 k n

/-- Specialized forward-Kronecker peaks are Bohr uniform limits. -/
lemma forwardKroneckerPeakWeight_isUniformLimit
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A) (k : ℕ) :
    IsUniformLimitOfFiniteCirclePolynomials
      (forwardKroneckerPeakWeight M hM A hA k) := by
  exact peakWeight_isUniformLimit _ _ _
    (normalizedForwardKroneckerAutocorrelation_isUniformLimit
      M hM A hA)

/-- The specialized peak is one at time zero. -/
lemma forwardKroneckerPeakWeight_zero
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A) (k : ℕ) :
    forwardKroneckerPeakWeight M hM A hA k 0 = 1 := by
  rw [show forwardKroneckerPeakWeight M hM A hA k 0 =
      peakWeight
        (normalizedForwardKroneckerAutocorrelation M hM A hA) 1 k 0
    by rfl]
  rw [peakWeight_eq_norm_sq_pow]
  have hbase :
      peakBase
          (normalizedForwardKroneckerAutocorrelation M hM A hA) 1 0 =
        1 := by
    unfold peakBase
    rw [normalizedForwardKroneckerAutocorrelation_zero
      M hM A hA hApos]
    norm_num
  rw [hbase]
  simp only [norm_one, one_pow]
  norm_cast

/-- The specialized peak is the real nonnegative power of its affine-base
squared norm. -/
lemma forwardKroneckerPeakWeight_eq_norm_sq_pow
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (k n : ℕ) :
    forwardKroneckerPeakWeight M hM A hA k n =
      (((‖peakBase
          (normalizedForwardKroneckerAutocorrelation M hM A hA)
          1 n‖ ^ 2) ^ k : ℝ) : ℂ) := by
  exact peakWeight_eq_norm_sq_pow _ _ _ _

/-- The affine base of the specialized peak has norm at most one. -/
lemma norm_forwardKroneckerPeakBase_le_one
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A) (n : ℕ) :
    ‖peakBase
        (normalizedForwardKroneckerAutocorrelation M hM A hA) 1 n‖ ≤
      1 := by
  have hq :=
    norm_normalizedForwardKroneckerAutocorrelation_le_one
      M hM A hA hApos n
  simpa only [peakBase, one_mul] using
    norm_peakBase_le_one_of_norm_le
      (normalizedForwardKroneckerAutocorrelation M hM A hA n) hq

/-- Specialized peak weights are real and nonnegative. -/
lemma forwardKroneckerPeakWeight_re_nonneg
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (k n : ℕ) :
    0 ≤ (forwardKroneckerPeakWeight M hM A hA k n).re := by
  rw [forwardKroneckerPeakWeight_eq_norm_sq_pow]
  change
    0 ≤
      (‖peakBase
          (normalizedForwardKroneckerAutocorrelation M hM A hA)
          1 n‖ ^ 2) ^ k
  positivity

/-- Specialized peak weights are bounded above by one. -/
lemma forwardKroneckerPeakWeight_re_le_one
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A) (k n : ℕ) :
    (forwardKroneckerPeakWeight M hM A hA k n).re ≤ 1 := by
  rw [forwardKroneckerPeakWeight_eq_norm_sq_pow]
  have hb :=
    norm_forwardKroneckerPeakBase_le_one
      M hM A hA hApos n
  have hb0 :
      0 ≤ ‖peakBase
          (normalizedForwardKroneckerAutocorrelation M hM A hA)
          1 n‖ :=
    norm_nonneg _
  have hbsq :
      ‖peakBase
          (normalizedForwardKroneckerAutocorrelation M hM A hA)
          1 n‖ ^ 2 ≤ 1 := by
    nlinarith
  exact pow_le_one₀ (sq_nonneg _) hbsq

/-- Away from the time-zero structured triple value, the affine peak base
is uniformly contracted by a constant strictly below one. -/
lemma exists_forwardKroneckerPeakBase_contraction
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ n : ℕ,
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA n ≤
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA 0 - η →
          ‖peakBase
              (normalizedForwardKroneckerAutocorrelation M hM A hA)
              1 n‖ ^ 2 ≤ ρ := by
  let D := MultipleKhintchineCharacteristic.KData M hM.1
  let G : D.H :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hG : G ≠ 0 :=
    forwardKroneckerIndicatorLp_ne_zero M hM A hA hApos
  have hg : 0 < ‖G‖ := norm_pos_iff.mpr hG
  let θ : ℝ := min (1 / 2) (η ^ 2 / (36 * ‖G‖ ^ 4))
  let ρ : ℝ := 1 - θ
  have hden : 0 < 36 * ‖G‖ ^ 4 := by positivity
  have hθ : 0 < θ := by
    dsimp [θ]
    exact lt_min (by norm_num) (div_pos (sq_pos_of_pos hη) hden)
  have hθhalf : θ ≤ 1 / 2 := by
    dsimp [θ]
    exact min_le_left _ _
  have hρ0 : 0 ≤ ρ := by
    dsimp [ρ]
    linarith
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    linarith
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro n hdrop
  let d : ℝ := ‖(D.U^[n]) G - G‖
  let q : ℂ :=
    normalizedForwardKroneckerAutocorrelation M hM A hA n
  let B : ℝ :=
    ‖peakBase
      (normalizedForwardKroneckerAutocorrelation M hM A hA) 1 n‖
  have hd0 : 0 ≤ d := by
    dsimp [d]
    positivity
  have hdiff :
      η ≤
        |ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA n -
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA 0| := by
    have hneg :
        ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA n -
            ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
              M hM A hA 0 < 0 := by
      linarith
    rw [abs_of_neg hneg]
    linarith
  have hlip :=
    abs_forwardKroneckerTripleCorrelation_sub_zero_le_three
      M hM A hA n
  have hηd : η ≤ 3 * ‖G‖ * d := by
    dsimp only [D, G, d] at hlip ⊢
    exact hdiff.trans hlip
  have hηsq : η ^ 2 ≤ 9 * ‖G‖ ^ 2 * d ^ 2 := by
    nlinarith [sq_nonneg (3 * ‖G‖ * d - η)]
  have hqnorm : ‖q‖ ≤ 1 := by
    dsimp [q]
    exact norm_normalizedForwardKroneckerAutocorrelation_le_one
      M hM A hA hApos n
  have hB :
      B ^ 2 ≤ (1 + q.re) / 2 := by
    dsimp [B, q]
    simpa only [peakBase, one_mul] using
      norm_sq_peakBase_le_of_norm_le
        (normalizedForwardKroneckerAutocorrelation M hM A hA n)
        hqnorm
  have hdist :
      2 * ‖G‖ ^ 2 * (1 - q.re) = d ^ 2 := by
    dsimp [D, G, q, d]
    exact two_norm_sq_mul_one_sub_normalized_re_eq
      M hM A hA hApos n
  have hmul :
      ‖G‖ ^ 2 * B ^ 2 ≤
        ‖G‖ ^ 2 * ((1 + q.re) / 2) :=
    mul_le_mul_of_nonneg_left hB (sq_nonneg ‖G‖)
  have hdeficit :
      d ^ 2 ≤ 4 * ‖G‖ ^ 2 * (1 - B ^ 2) := by
    nlinarith
  have hdeficit_mul :
      9 * ‖G‖ ^ 2 * d ^ 2 ≤
        9 * ‖G‖ ^ 2 *
          (4 * ‖G‖ ^ 2 * (1 - B ^ 2)) :=
    mul_le_mul_of_nonneg_left hdeficit
      (mul_nonneg (by norm_num) (sq_nonneg ‖G‖))
  have hproduct :
      η ^ 2 ≤
        (36 * ‖G‖ ^ 4) * (1 - B ^ 2) := by
    calc
      η ^ 2 ≤ 9 * ‖G‖ ^ 2 * d ^ 2 := hηsq
      _ ≤ 9 * ‖G‖ ^ 2 *
          (4 * ‖G‖ ^ 2 * (1 - B ^ 2)) := hdeficit_mul
      _ = (36 * ‖G‖ ^ 4) * (1 - B ^ 2) := by ring
  have hfraction :
      η ^ 2 / (36 * ‖G‖ ^ 4) ≤ 1 - B ^ 2 :=
    (div_le_iff₀ hden).2 (by
      simpa only [mul_comm] using hproduct)
  have hraw :
      B ^ 2 ≤ 1 - η ^ 2 / (36 * ‖G‖ ^ 4) := by
    linarith
  have hθraw :
      θ ≤ η ^ 2 / (36 * ‖G‖ ^ 4) := by
    dsimp [θ]
    exact min_le_right _ _
  dsimp [B, ρ]
  exact hraw.trans (by linarith)

/-- By taking a sufficiently high power, the specialized peak is
arbitrarily small wherever the structured triple correlation has a fixed
drop from its time-zero value. -/
lemma exists_forwardKroneckerPeakWeight_small_on_drop
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A)
    (η β : ℝ) (hη : 0 < η) (hβ : 0 < β) :
    ∃ k : ℕ, ∀ n : ℕ,
      ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA n ≤
          ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA 0 - η →
        (forwardKroneckerPeakWeight M hM A hA k n).re < β := by
  obtain ⟨ρ, hρ0, hρ1, hcontract⟩ :=
    exists_forwardKroneckerPeakBase_contraction
      M hM A hA hApos η hη
  obtain ⟨k, hk⟩ :=
    exists_pow_lt_of_lt_one hβ hρ1
  refine ⟨k, ?_⟩
  intro n hdrop
  rw [forwardKroneckerPeakWeight_eq_norm_sq_pow]
  change
    (‖peakBase
        (normalizedForwardKroneckerAutocorrelation M hM A hA)
        1 n‖ ^ 2) ^ k < β
  exact
    (pow_le_pow_left₀ (sq_nonneg _)
      (hcontract n hdrop) k).trans_lt hk

/-- For every fixed peak power there is a positive weight floor on a
syndetic set of structured near-returns. -/
lemma syndetic_forwardKroneckerPeakWeight_floor
    (M : System.{u}) (hM : IsErgodic M)
    (A : Set M.X) (hA : MeasurableSet A)
    (hApos : 0 < M.μ A)
    (η : ℝ) (hη : 0 < η)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (k : ℕ) :
    IsSyndetic {n : ℕ |
      ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA 0 - η / 2 <
          ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA n ∧
      (t ^ 2) ^ k ≤
        (forwardKroneckerPeakWeight M hM A hA k n).re} := by
  let D := MultipleKhintchineCharacteristic.KData M hM.1
  let G : D.H :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp M hM A hA
  have hU : ∀ X : D.H, ‖D.U X‖ = ‖X‖ :=
    fun X ↦
      (MeasureTheory.Lp.compMeasurePreservingₗᵢ
        ℂ M.T hM.1.2).norm_map X
  have hG : G ≠ 0 :=
    forwardKroneckerIndicatorLp_ne_zero M hM A hA hApos
  have hg : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hGap : IsAlmostPeriodicVector D G :=
    ForwardKroneckerFactor.forwardKroneckerIndicatorLp_almostPeriodic
      M hM A hA
  let δ : ℝ := min (‖G‖ * (1 - t)) (η / (6 * ‖G‖))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (mul_pos hg (sub_pos.mpr ht1))
      (div_pos hη (mul_pos (by norm_num) hg))
  have hδg : δ ≤ ‖G‖ * (1 - t) := by
    dsimp [δ]
    exact min_le_left _ _
  have hδη : δ ≤ η / (6 * ‖G‖) := by
    dsimp [δ]
    exact min_le_right _ _
  have hret :
      IsSyndetic {n : ℕ | ‖(D.U^[n]) G - G‖ < δ} :=
    AlmostPeriodicIsometry.almostPeriodic_returns_syndetic
      D hU G hGap δ hδ
  obtain ⟨L, hL, hretL⟩ := hret
  refine ⟨L, hL, ?_⟩
  intro i
  obtain ⟨n, hnret, hin, hnupper⟩ := hretL i
  refine ⟨n, ?_, hin, hnupper⟩
  have hdδ : ‖(D.U^[n]) G - G‖ < δ := hnret
  have hdη :
      3 * ‖G‖ * ‖(D.U^[n]) G - G‖ < η / 2 := by
    have hdη' :
        ‖(D.U^[n]) G - G‖ < η / (6 * ‖G‖) :=
      hdδ.trans_le hδη
    have hsix : 0 < 6 * ‖G‖ := mul_pos (by norm_num) hg
    rw [lt_div_iff₀ hsix] at hdη'
    nlinarith
  have hlip :=
    abs_forwardKroneckerTripleCorrelation_sub_zero_le_three
      M hM A hA n
  have hbclose :
      |ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA n -
          ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA 0| < η / 2 :=
    lt_of_le_of_lt hlip (by
      simpa only [D, G] using hdη)
  have hbhigh :
      ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA 0 - η / 2 <
          ForwardKroneckerFactor.forwardKroneckerTripleCorrelation
            M hM A hA n := by
    linarith [neg_lt_of_abs_lt hbclose]
  refine ⟨hbhigh, ?_⟩
  let q : ℂ :=
    normalizedForwardKroneckerAutocorrelation M hM A hA n
  let B : ℝ :=
    ‖peakBase
      (normalizedForwardKroneckerAutocorrelation M hM A hA) 1 n‖
  have hdt :
      ‖(D.U^[n]) G - G‖ < ‖G‖ * (1 - t) :=
    hdδ.trans_le hδg
  have hdist :
      2 * ‖G‖ ^ 2 * (1 - q.re) =
        ‖(D.U^[n]) G - G‖ ^ 2 := by
    dsimp [D, G, q]
    exact two_norm_sq_mul_one_sub_normalized_re_eq
      M hM A hA hApos n
  have hdt_sq :
      ‖(D.U^[n]) G - G‖ ^ 2 <
        ‖G‖ ^ 2 * (1 - t) ^ 2 := by
    nlinarith [norm_nonneg ((D.U^[n]) G - G),
      sub_pos.mpr ht1]
  have hqre : 2 * t - 1 < q.re := by
    by_contra hnot
    have hqle : q.re ≤ 2 * t - 1 := le_of_not_gt hnot
    have hqdeficit :
        4 * (1 - t) ≤ 2 * (1 - q.re) := by
      linarith
    have hqdeficit_mul :
        ‖G‖ ^ 2 * (4 * (1 - t)) ≤
          ‖G‖ ^ 2 * (2 * (1 - q.re)) :=
      mul_le_mul_of_nonneg_left hqdeficit (sq_nonneg ‖G‖)
    have husq : (1 - t) ^ 2 < 4 * (1 - t) := by
      nlinarith [sub_pos.mpr ht1, ht0]
    have husq_mul :
        ‖G‖ ^ 2 * (1 - t) ^ 2 <
          ‖G‖ ^ 2 * (4 * (1 - t)) :=
      mul_lt_mul_of_pos_left husq (sq_pos_of_pos hg)
    nlinarith
  have hbase_re :
      t <
        (peakBase
          (normalizedForwardKroneckerAutocorrelation M hM A hA)
          1 n).re := by
    rw [show
      peakBase
          (normalizedForwardKroneckerAutocorrelation M hM A hA)
          1 n =
        (1 + q) / 2 by
      unfold peakBase
      rw [one_mul]]
    have htwoinv :
        ((2 : ℂ)⁻¹) = (((1 / 2 : ℝ) : ℂ)) := by
      norm_num
    have hrealformula :
        ((1 + q) / 2).re = (1 + q.re) / 2 := by
      rw [div_eq_mul_inv, htwoinv]
      simp only [Complex.mul_re, Complex.add_re, Complex.one_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [hrealformula]
    linarith
  have hB : t < B := by
    dsimp [B]
    exact hbase_re.trans_le
      (le_trans (le_abs_self _)
        (Complex.abs_re_le_norm _))
  have hBsq :
      t ^ 2 ≤ B ^ 2 := by
    exact pow_le_pow_left₀ ht0.le hB.le 2
  rw [forwardKroneckerPeakWeight_eq_norm_sq_pow]
  rw [Complex.ofReal_re]
  simpa only [B] using
    (pow_le_pow_left₀ (sq_nonneg _) hBsq k)

end Chapter02.ForwardKroneckerBohr
