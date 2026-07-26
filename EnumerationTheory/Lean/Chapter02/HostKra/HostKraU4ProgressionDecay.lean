import Chapter02.HostKra.HostKraU3ProgressionDecay
import Chapter02.HostKra.HostKraDualFunction
import Chapter02.HostKra.HostKraCubeThree
import Chapter02.HostKra.HostKraU3Nullspace

open Classical Filter MeasureTheory

noncomputable section

namespace Chapter02.HostKraU4ProgressionDecay

universe u

open HostKraCubeSeminorm

abbrev KData (M : System.{u})
    (hM : Chapter01.IsMeasurePreservingSystem M) :=
  MultipleKhintchineCharacteristic.KData M hM

/-- The bounded multiplicative Koopman derivative
`star (U^a Q) * U^b Q`, packaged in `L²`. -/
noncomputable def koopmanMultiplicativeDerivative
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) : Lp ℂ 2 M.μ :=
  MultipleKhintchineKronecker.lpPointwiseMul
    (ForwardKroneckerFactor.lpStar M (((KData M hM).U^[a]) Q))
    (((KData M hM).U^[b]) Q)
    (HostKraDualFunction.lpStar_memLp_top M
      (((KData M hM).U^[a]) Q)
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM a Q hQtop))

lemma koopmanMultiplicativeDerivative_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) :
    (fun x ↦ koopmanMultiplicativeDerivative
      M hM Q hQtop a b x) =ᵐ[M.μ]
      (fun x ↦
        star ((show Lp ℂ 2 M.μ from ((KData M hM).U^[a]) Q) x) *
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[b]) Q) x) := by
  filter_upwards [
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (ForwardKroneckerFactor.lpStar M (((KData M hM).U^[a]) Q))
      (((KData M hM).U^[b]) Q)
      (HostKraDualFunction.lpStar_memLp_top M
        (((KData M hM).U^[a]) Q)
        (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
          M hM a Q hQtop)),
    ForwardKroneckerFactor.lpStar_coe
      M (((KData M hM).U^[a]) Q)] with x hmul hstar
  change
    MultipleKhintchineKronecker.lpPointwiseMul
        (ForwardKroneckerFactor.lpStar M (((KData M hM).U^[a]) Q))
        (((KData M hM).U^[b]) Q)
        (HostKraDualFunction.lpStar_memLp_top M
          (((KData M hM).U^[a]) Q)
          (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
            M hM a Q hQtop)) x = _
  rw [hmul, hstar]

lemma koopmanMultiplicativeDerivative_memLp_top
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) :
    MemLp (fun x ↦
      koopmanMultiplicativeDerivative M hM Q hQtop a b x) ⊤ M.μ := by
  rw [memLp_congr_ae
    (koopmanMultiplicativeDerivative_coe M hM Q hQtop a b)]
  exact
    (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM b Q hQtop).mul
      (r := ⊤)
      ((MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM a Q hQtop).star)

lemma koopmanMultiplicativeDerivative_norm_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hQbound : ∀ᵐ x ∂M.μ, ‖Q x‖ ≤ C)
    (a b : ℕ) :
    ∀ᵐ x ∂M.μ,
      ‖koopmanMultiplicativeDerivative M hM Q hQtop a b x‖ ≤ C ^ 2 := by
  filter_upwards [
    koopmanMultiplicativeDerivative_coe M hM Q hQtop a b,
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM a Q C hQbound,
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM b Q C hQbound] with x hcoe ha hb
  rw [hcoe, norm_mul, norm_star]
  nlinarith [norm_nonneg
    ((show Lp ℂ 2 M.μ from ((KData M hM).U^[a]) Q) x),
    norm_nonneg
    ((show Lp ℂ 2 M.μ from ((KData M hM).U^[b]) Q) x)]

/-- `L²` norm bound for a multiplicative derivative when the original
vector has an essential pointwise bound. -/
lemma norm_koopmanMultiplicativeDerivative_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hQbound : ∀ᵐ x ∂M.μ, ‖Q x‖ ≤ C)
    (a b : ℕ) :
    ‖koopmanMultiplicativeDerivative M hM Q hQtop a b‖ ≤
      C * ‖Q‖ := by
  let Qa : Lp ℂ 2 M.μ := ((KData M hM).U^[a]) Q
  let Qb : Lp ℂ 2 M.μ := ((KData M hM).U^[b]) Q
  let hQaTop :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM a Q hQtop
  have hstarBound :
      ∀ᵐ x ∂M.μ,
        ‖ForwardKroneckerFactor.lpStar M Qa x‖ ≤ C := by
    filter_upwards [
      ForwardKroneckerFactor.lpStar_coe M Qa,
      MultipleKhintchineKronecker.koopmanData_iter_norm_le
        M hM a Q C hQbound] with x hstar hQa
    rw [hstar, norm_star]
    exact hQa
  have hmul :=
    MultipleKhintchineKronecker.norm_lpPointwiseMul_le
      (ForwardKroneckerFactor.lpStar M Qa) Qb
      (HostKraDualFunction.lpStar_memLp_top M Qa hQaTop)
      C hC hstarBound
  calc
    ‖koopmanMultiplicativeDerivative M hM Q hQtop a b‖ ≤
        C * ‖Qb‖ := by
      simpa only [koopmanMultiplicativeDerivative, Qa, Qb, hQaTop] using hmul
    _ = C * ‖Q‖ := by
      congr 1
      exact AlmostPeriodicIsometry.iterate_norm
        (KData M hM)
        (fun V ↦
          (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map V)
        Q b

lemma koopmanMultiplicativeDerivative_iter
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (n a b : ℕ) :
    ((KData M hM).U^[n])
        (koopmanMultiplicativeDerivative M hM Q hQtop a b) =
      koopmanMultiplicativeDerivative M hM Q hQtop (n + a) (n + b) := by
  rw [koopmanMultiplicativeDerivative,
    MultipleKhintchineKronecker.koopmanData_iter_lpPointwiseMul]
  unfold koopmanMultiplicativeDerivative
  congr 1
  · rw [← ForwardKroneckerFactor.lpStar_iterate_koopman]
    congr 1
    rw [Function.iterate_add_apply]
  · rw [Function.iterate_add_apply]

lemma koopmanMultiplicativeDerivative_iter_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (n a b : ℕ) :
    (fun x ↦
      (show Lp ℂ 2 M.μ from
        ((KData M hM).U^[n])
          (koopmanMultiplicativeDerivative M hM Q hQtop a b)) x) =ᵐ[M.μ]
      (fun x ↦
        star ((show Lp ℂ 2 M.μ from
          ((KData M hM).U^[n + a]) Q) x) *
        (show Lp ℂ 2 M.μ from
          ((KData M hM).U^[n + b]) Q) x) := by
  rw [koopmanMultiplicativeDerivative_iter M hM Q hQtop n a b]
  exact koopmanMultiplicativeDerivative_coe
    M hM Q hQtop (n + a) (n + b)

/-- Swapping the two times conjugates the multiplicative derivative. -/
lemma koopmanMultiplicativeDerivative_swap
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) :
    koopmanMultiplicativeDerivative M hM Q hQtop a b =
      ForwardKroneckerFactor.lpStar M
        (koopmanMultiplicativeDerivative M hM Q hQtop b a) := by
  apply Lp.ext
  filter_upwards [
    koopmanMultiplicativeDerivative_coe M hM Q hQtop a b,
    ForwardKroneckerFactor.lpStar_coe M
      (koopmanMultiplicativeDerivative M hM Q hQtop b a),
    koopmanMultiplicativeDerivative_coe M hM Q hQtop b a] with
      x hab hstar hba
  rw [hab, hstar, hba, star_mul, star_star]

/-- When `a ≤ b`, the two-time derivative is the common forward translate
of the canonical cube derivative with edge length `b - a`. -/
lemma koopmanMultiplicativeDerivative_eq_iter_cubeDerivativeLp_of_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) (hab : a ≤ b) :
    koopmanMultiplicativeDerivative M hM Q hQtop a b =
      ((KData M hM).U^[a])
        (HostKraCubeThree.cubeDerivativeLp
          M hM Q hQtop (b - a)) := by
  apply Lp.ext
  have hderivShift :=
    (hM.2.iterate a).quasiMeasurePreserving.ae
      (HostKraCubeThree.cubeDerivativeLp_coe
        M hM Q hQtop (b - a))
  have hcubeShift :=
    (hM.2.iterate a).quasiMeasurePreserving.ae
      (HostKraCubeTwo.cubeDerivative_ae_eq
        M hM Q (b - a))
  filter_upwards [
    koopmanMultiplicativeDerivative_coe M hM Q hQtop a b,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM a
      (HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop (b - a)),
    hderivShift, hcubeShift,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM a Q,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM b Q] with
      x hleft hiter hderiv hcube hQa hQb
  rw [hleft, hiter, hderiv, hcube, hQa, hQb]
  have hab' : b - a + a = b := Nat.sub_add_cancel hab
  rw [show
      (M.T^[b - a]) ((M.T^[a]) x) = (M.T^[b]) x by
    rw [← Function.iterate_add_apply, hab']]
  rw [mul_comm]

/-- The reverse order uses the conjugate canonical cube derivative; no
negative iterate or invertibility assumption is needed. -/
lemma koopmanMultiplicativeDerivative_eq_iter_star_cubeDerivativeLp_of_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) (hba : b ≤ a) :
    koopmanMultiplicativeDerivative M hM Q hQtop a b =
      ((KData M hM).U^[b])
        (ForwardKroneckerFactor.lpStar M
          (HostKraCubeThree.cubeDerivativeLp
            M hM Q hQtop (a - b))) := by
  rw [koopmanMultiplicativeDerivative_swap M hM Q hQtop a b,
    koopmanMultiplicativeDerivative_eq_iter_cubeDerivativeLp_of_le
      M hM Q hQtop b a hba]
  exact ForwardKroneckerFactor.lpStar_iterate_koopman
    M hM
      (HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop (a - b))
      b

/-- Orthogonal projection onto the Koopman fixed space commutes with
pointwise conjugation. -/
lemma fixedProjection_lpStar
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F : Lp ℂ 2 M.μ) :
    let D := KData M hM
    let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
      LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
    (S.starProjection (ForwardKroneckerFactor.lpStar M F) :
        Lp ℂ 2 M.μ) =
      ForwardKroneckerFactor.lpStar M
        (S.starProjection F : Lp ℂ 2 M.μ) := by
  dsimp only
  let D := KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  have hstarMem {G : Lp ℂ 2 M.μ} (hG : G ∈ S) :
      ForwardKroneckerFactor.lpStar M G ∈ S := by
    change D.U (ForwardKroneckerFactor.lpStar M G) =
      ForwardKroneckerFactor.lpStar M G
    rw [← ForwardKroneckerFactor.lpStar_koopman M hM]
    change ForwardKroneckerFactor.lpStar M (D.U G) =
      ForwardKroneckerFactor.lpStar M G
    change D.U G = G at hG
    rw [hG]
  have hstarOrth {G : Lp ℂ 2 M.μ} (hG : G ∈ Sᗮ) :
      ForwardKroneckerFactor.lpStar M G ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal] at hG ⊢
    intro Y hY
    have hstarY := hstarMem hY
    have hzero := hG (ForwardKroneckerFactor.lpStar M Y) hstarY
    rw [Chapter02.HostKraU3Nullspace.inner_lpStar_right M Y G,
      hzero, star_zero]
  change S.starProjection (ForwardKroneckerFactor.lpStar M F) =
    ForwardKroneckerFactor.lpStar M (S.starProjection F)
  apply S.eq_starProjection_of_mem_orthogonal
  · exact hstarMem (S.starProjection_apply_mem F)
  · have horth : F - S.starProjection F ∈ Sᗮ :=
      S.sub_starProjection_mem_orthogonal F
    have hstar := hstarOrth horth
    simpa only [ForwardKroneckerFactor.lpStar_sub] using hstar

/-- The invariant-projection energy is unchanged by pointwise complex
conjugation. -/
lemma invariantEnergy_star
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    HostKraCubeSeminorm.invariantEnergy M hM
        (fun x ↦ star (f x)) hf.star =
      HostKraCubeSeminorm.invariantEnergy M hM f hf := by
  have htoLp :
      hf.star.toLp (fun x ↦ star (f x)) =
        ForwardKroneckerFactor.lpStar M (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [
      (show
        (fun x ↦ hf.star.toLp (fun y ↦ star (f y)) x) =ᵐ[M.μ]
          (fun x ↦ star (f x)) by
        simpa only [Pi.star_apply] using hf.star.coeFn_toLp),
      ForwardKroneckerFactor.lpStar_coe M (hf.toLp f),
      hf.coeFn_toLp] with x hleft hstar hright
    rw [hleft, hstar, hright]
  unfold HostKraCubeSeminorm.invariantEnergy
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection,
    HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  change
    ‖((LinearMap.eqLocus
        (KData M hM).U
        (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)).orthogonalProjection
          (hf.star.toLp (fun x ↦ star (f x)))).val‖ ^ 2 =
      ‖((LinearMap.eqLocus
        (KData M hM).U
        (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)).orthogonalProjection
          (hf.toLp f)).val‖ ^ 2
  rw [htoLp]
  have hproj := fixedProjection_lpStar M hM (hf.toLp f)
  change
    ((LinearMap.eqLocus
      (KData M hM).U
      (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)).orthogonalProjection
        (ForwardKroneckerFactor.lpStar M (hf.toLp f))).val =
      ForwardKroneckerFactor.lpStar M
        ((LinearMap.eqLocus
          (KData M hM).U
          (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)).orthogonalProjection
            (hf.toLp f)).val at hproj
  rw [hproj, ForwardKroneckerFactor.norm_lpStar]

/-- The invariant projection captures the constant direction, so the
absolute integral of an `L²` function is bounded by the norm of its
invariant mean. -/
lemma norm_integral_le_norm_invariantMeanLp
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    ‖∫ x, f x ∂M.μ‖ ≤
      ‖HostKraRelativeMean.invariantMeanLp M hM f hf‖ := by
  let D := KData M hM
  let S : Submodule ℂ (Lp ℂ 2 M.μ) :=
    LinearMap.eqLocus D.U (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
  let F : Lp ℂ 2 M.μ := hf.toLp f
  let P : Lp ℂ 2 M.μ := (S.orthogonalProjection F).val
  have hmean :
      HostKraRelativeMean.invariantMeanLp M hM f hf = P := by
    simpa only [D, S, F, P] using
      HostKraRelativeMean.invariantMeanLp_eq_fixedProjection M hM f hf
  have honeFixed :
      D.U (CorrelationMean.oneLp M hM) =
        CorrelationMean.oneLp M hM := by
    apply Lp.ext
    have hiter :=
      MultipleKhintchineKronecker.koopmanData_iter_ae
        M hM 1 (CorrelationMean.oneLp M hM)
    have hcoeShift :=
      hM.2.quasiMeasurePreserving.ae_eq_comp
        (WeakSpectrum.oneLp_coe M hM)
    filter_upwards [hiter, hcoeShift, WeakSpectrum.oneLp_coe M hM]
      with x hx hshift hone
    simp only [Function.iterate_one] at hx
    change
      (show Lp ℂ 2 M.μ from
        D.U (CorrelationMean.oneLp M hM)) x =
        CorrelationMean.oneLp M hM x
    rw [hx]
    exact hshift.trans hone.symm
  have honeMem : CorrelationMean.oneLp M hM ∈ S := by
    change D.U (CorrelationMean.oneLp M hM) =
      (1 : Lp ℂ 2 M.μ →L[ℂ] Lp ℂ 2 M.μ)
        (CorrelationMean.oneLp M hM)
    simpa only [ContinuousLinearMap.one_apply] using honeFixed
  have horth : F - P ∈ Sᗮ := by
    exact S.sub_starProjection_mem_orthogonal F
  have hinnerOrth :
      @inner ℂ (Lp ℂ 2 M.μ) _
        (CorrelationMean.oneLp M hM) (F - P) = 0 :=
    S.inner_right_of_mem_orthogonal honeMem horth
  have honeNorm : ‖CorrelationMean.oneLp M hM‖ = 1 := by
    have honeInner := WeakSpectrum.inner_oneLp_self M hM
    rw [inner_self_eq_norm_sq_to_K] at honeInner
    have hsquare : ‖CorrelationMean.oneLp M hM‖ ^ 2 = 1 := by
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_pow, Complex.ofReal_one] using honeInner
    nlinarith [norm_nonneg (CorrelationMean.oneLp M hM)]
  calc
    ‖∫ x, f x ∂M.μ‖ = ‖∫ x, F x ∂M.μ‖ := by
      rw [integral_congr_ae hf.coeFn_toLp]
    _ = ‖@inner ℂ (Lp ℂ 2 M.μ) _
        (CorrelationMean.oneLp M hM) F‖ := by
      rw [CorrelationMean.integral_eq_inner_oneLp]
    _ = ‖@inner ℂ (Lp ℂ 2 M.μ) _
        (CorrelationMean.oneLp M hM) P‖ := by
      have hdecomp : F = P + (F - P) := by abel
      rw [hdecomp, inner_add_right, hinnerOrth, add_zero]
    _ ≤ ‖CorrelationMean.oneLp M hM‖ * ‖P‖ :=
      norm_inner_le_norm _ _
    _ = ‖HostKraRelativeMean.invariantMeanLp M hM f hf‖ := by
      rw [honeNorm, one_mul, hmean]

/-- Squared form of `norm_integral_le_norm_invariantMeanLp`. -/
lemma norm_integral_sq_le_invariantEnergy
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : M.lpMember 2 f) :
    ‖∫ x, f x ∂M.μ‖ ^ 2 ≤
      HostKraCubeSeminorm.invariantEnergy M hM f hf := by
  unfold HostKraCubeSeminorm.invariantEnergy
  exact pow_le_pow_left₀ (norm_nonneg _) 
    (norm_integral_le_norm_invariantMeanLp M hM f hf) 2

/-- Quantitative adjacent-order monotonicity in the normalization used by
this chapter: the square of the `U²` power is bounded by the `U³`
power. -/
lemma hostKraU2Power_sq_le_hostKraU3Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    (hostKraU2Power M hM f hf) ^ 2 ≤
      hostKraU3Power M hM f hf := by
  let C1 :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne M hM
  let hC1 :=
    HostKraStandardRelativeJoining.relativeCubeSystemOne_mps M hM
  let C2 :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM
  let hC2 :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo_mps M hM
  let F1 := cubeLiftOne M hM f
  let hF1top := cubeLiftOne_memLp_top M hM f hf
  let hF1two := cubeLiftOne_memLp_two M hM f hf
  let F2 := cubeLiftTwo M hM f
  let hF2two := cubeLiftTwo_memLp_two M hM f hf
  have hrec :=
    Chapter02.HostKraRelativeJoiningComplex.integral_cubeLift_eq_invariantEnergy
      C1 hC1 F1 hF1top
  have hrec' :
      ∫ p, F2 p ∂C2.μ =
        ((HostKraCubeSeminorm.invariantEnergy
          C1 hC1 F1 hF1two : ℝ) : ℂ) := by
    simpa only [C1, hC1, C2, F1, F2, cubeLiftTwo, cubeLiftOne,
      HostKraStandardRelativeJoining.relativeCubeSystemOne,
      HostKraStandardRelativeJoining.relativeCubeSystemTwo,
      HostKraStandardRelativeJoining.relativeJoiningSystem] using hrec
  have hbound :=
    norm_integral_sq_le_invariantEnergy C2 hC2 F2 hF2two
  have hE2nonneg :
      0 ≤ HostKraCubeSeminorm.invariantEnergy C1 hC1 F1 hF1two :=
    HostKraCubeSeminorm.invariantEnergy_nonneg C1 hC1 F1 hF1two
  rw [hrec', Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE2nonneg] at hbound
  unfold hostKraU2Power hostKraU3Power
  exact hbound

/-- Real-valued unshifted form of the quantitative `U²`
autocorrelation-square limit. -/
lemma autocorrelationSq_average_tendsto_hostKraU2Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    Tendsto
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          ‖functionCorrelation M f f n‖ ^ 2)
      atTop (nhds (hostKraU2Power M hM f hf)) := by
  have huniform :=
    Chapter02.HostKraU2Continuous.hostKraU2Power_uniform_autocorrelation_sq
      M hM hErg f hf
  have hcomplex :
      Tendsto
        (fun N : ℕ ↦ if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
            ((‖functionCorrelation M f f n‖ ^ 2 : ℝ) : ℂ))
        atTop (nhds ((hostKraU2Power M hM f hf : ℝ) : ℂ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 (huniform ε hε)
    refine ⟨N, ?_⟩
    intro n hn
    simpa using hN n hn 0
  rw [show
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
          ((‖functionCorrelation M f f n‖ ^ 2 : ℝ) : ℂ)) =
        fun N : ℕ ↦ ((if N = 0 then 0 else
          ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
            ‖functionCorrelation M f f n‖ ^ 2 : ℝ) : ℂ) by
    funext N
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false]
      push_cast
      rfl] at hcomplex
  simpa only [Function.comp_apply, Complex.ofReal_re] using
    (Complex.continuous_re.continuousAt.tendsto.comp hcomplex)

/-- The even autocorrelation norms admit a finite block estimate whose
main term is the quantitative `U²` power. -/
lemma exists_evenAutocorrelationNorm_sq_lt_hostKraU2Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (G : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧
      ((Finset.range L).sum
        (MultipleKhintchineCharacteristic.evenAutocorrelationNorm
          M hM G)) ^ 2 <
        2 * (L : ℝ) ^ 2 *
          (hostKraU2Power M hM (fun x ↦ G x) hGtop + η) := by
  let a : ℕ → ℝ := fun n ↦
    ‖functionCorrelation M (fun x ↦ G x) (fun x ↦ G x) n‖ ^ 2
  have ha : ∀ n, 0 ≤ a n := fun n ↦ sq_nonneg _
  have htend :
      Tendsto
        (fun N : ℕ ↦ if N = 0 then 0 else
          ((N : ℝ)⁻¹) * (Finset.range N).sum a)
        atTop
        (nhds (hostKraU2Power M hM (fun x ↦ G x) hGtop)) := by
    simpa only [a] using
      autocorrelationSq_average_tendsto_hostKraU2Power
        M hM hErg (fun x ↦ G x) hGtop
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend η hη
  let L := N₀ + 1
  have hL : 0 < L := by
    dsimp only [L]
    omega
  have hlarge : N₀ ≤ 2 * L := by
    dsimp only [L]
    omega
  have havgdist := hN₀ (2 * L) hlarge
  have htwoL : 2 * L ≠ 0 := by omega
  have havgdist' :
      |(((2 * L : ℕ) : ℝ)⁻¹) *
          (Finset.range (2 * L)).sum a -
        hostKraU2Power M hM (fun x ↦ G x) hGtop| < η := by
    simpa only [htwoL, if_false, Real.dist_eq] using havgdist
  have havg :
      (((2 * L : ℕ) : ℝ)⁻¹) *
          (Finset.range (2 * L)).sum a <
        hostKraU2Power M hM (fun x ↦ G x) hGtop + η :=
    by
      have habs := abs_sub_lt_iff.mp havgdist'
      linarith
  have hsub :
      (Finset.range L).sum (fun r ↦ a (2 * r)) ≤
        (Finset.range (2 * L)).sum a := by
    let e : ℕ → ℕ := fun r ↦ 2 * r
    have hinj : Set.InjOn e (Finset.range L) := by
      intro x hx y hy hxy
      dsimp only [e] at hxy
      omega
    have himage :
        (Finset.range L).image e ⊆ Finset.range (2 * L) := by
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
      apply Finset.mem_range.mpr
      have hrL := Finset.mem_range.mp hr
      dsimp only [e]
      omega
    calc
      (Finset.range L).sum (fun r ↦ a (2 * r)) =
          ((Finset.range L).image e).sum a := by
        rw [Finset.sum_image hinj]
      _ ≤ (Finset.range (2 * L)).sum a :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun n hn hnot ↦ ha n)
  have hcorr (r : ℕ) :
      MultipleKhintchineCharacteristic.evenAutocorrelationNorm
          M hM G r =
        ‖functionCorrelation M (fun x ↦ G x) (fun x ↦ G x)
          (2 * r)‖ := by
    have hc :=
      Chapter02.HostKraU2Continuous.functionCorrelation_eq_koopman_inner
        M hM (fun x ↦ G x) (Lp.memLp G) (2 * r)
    apply Eq.symm
    simpa only [Lp.toLp_coeFn, norm_inner_symm,
      MultipleKhintchineCharacteristic.evenAutocorrelationNorm,
      MultipleKhintchineCharacteristic.KData,
      WeakSpectrum.koopmanData,
      MultipleKhintchineKronecker.koopmanData] using congrArg norm hc
  have hcs :
      ((Finset.range L).sum
        (MultipleKhintchineCharacteristic.evenAutocorrelationNorm
          M hM G)) ^ 2 ≤
        (L : ℝ) * (Finset.range L).sum (fun r ↦ a (2 * r)) := by
    have hs :=
      sq_sum_le_card_mul_sum_sq
        (s := Finset.range L)
        (f := MultipleKhintchineCharacteristic.evenAutocorrelationNorm
          M hM G)
    simpa only [Finset.card_range, a, hcorr] using hs
  have htwoLreal : (0 : ℝ) < (2 * L : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hL
  rw [inv_mul_lt_iff₀ htwoLreal] at havg
  refine ⟨L, hL, ?_⟩
  have hcast : (((2 * L : ℕ) : ℝ)) = 2 * (L : ℝ) :=
    Nat.cast_mul 2 L
  rw [hcast] at havg
  nlinarith

/-- The same even-correlation estimate expressed only through the
quantitative `U³` power. -/
lemma exists_evenAutocorrelationNorm_sq_lt_sqrt_hostKraU3Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (G : Lp ℂ 2 M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧
      ((Finset.range L).sum
        (MultipleKhintchineCharacteristic.evenAutocorrelationNorm
          M hM G)) ^ 2 <
        2 * (L : ℝ) ^ 2 *
          (Real.sqrt
            (hostKraU3Power M hM (fun x ↦ G x) hGtop) + η) := by
  obtain ⟨L, hL, hbound⟩ :=
    exists_evenAutocorrelationNorm_sq_lt_hostKraU2Power
      M hM hErg G hGtop η hη
  have hU3nonneg :
      0 ≤ hostKraU3Power M hM (fun x ↦ G x) hGtop :=
    hostKraU3Power_nonneg M hM _ _
  have hsqrtSq :
      (Real.sqrt (hostKraU3Power M hM (fun x ↦ G x) hGtop)) ^ 2 =
        hostKraU3Power M hM (fun x ↦ G x) hGtop :=
    Real.sq_sqrt hU3nonneg
  have hU2nonneg :
      0 ≤ hostKraU2Power M hM (fun x ↦ G x) hGtop :=
    hostKraU2Power_nonneg M hM _ _
  have hmono :=
    hostKraU2Power_sq_le_hostKraU3Power
      M hM (fun x ↦ G x) hGtop
  have hU2le :
      hostKraU2Power M hM (fun x ↦ G x) hGtop ≤
        Real.sqrt (hostKraU3Power M hM (fun x ↦ G x) hGtop) := by
    nlinarith [Real.sqrt_nonneg
      (hostKraU3Power M hM (fun x ↦ G x) hGtop)]
  refine ⟨L, hL, ?_⟩
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  nlinarith [sq_pos_of_pos hLreal]

/-- Quantitative uniform block-correlation estimate for a bilinear
progression.  The second factor need not be `U³`-null; its exact `U³`
power appears in the bound. -/
lemma doubleKoopmanProduct_uniform_blockCorrelation_lt_hostKraU3Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ L : ℕ, 0 < L ∧
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        cesaroAverage
          (fun n ↦ ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L,
            (@inner ℂ (Lp ℂ 2 M.μ) _
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM F G hFtop (i + (n + k)))
              (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                M hM F G hFtop (i + (n + h)))).re) N <
          (2 * C ^ 2 *
              Real.sqrt (2 * (Real.sqrt
                (hostKraU3Power M hM (fun x ↦ G x) hGtop) + η)) + η) *
            (L : ℝ) ^ 2 := by
  obtain ⟨L, hL, heven⟩ :=
    exists_evenAutocorrelationNorm_sq_lt_sqrt_hostKraU3Power
      M hM hErg G hGtop η hη
  let P : ℝ := hostKraU3Power M hM (fun x ↦ G x) hGtop
  let R : ℝ := Real.sqrt (2 * (Real.sqrt P + η))
  let S : ℝ :=
    (Finset.range L).sum
      (MultipleKhintchineCharacteristic.evenAutocorrelationNorm M hM G)
  have hP : 0 ≤ P := by
    exact hostKraU3Power_nonneg M hM _ _
  have hRarg : 0 < 2 * (Real.sqrt P + η) := by
    have := Real.sqrt_nonneg P
    positivity
  have hRsq : R ^ 2 = 2 * (Real.sqrt P + η) := by
    exact Real.sq_sqrt hRarg.le
  have hR : 0 < R := Real.sqrt_pos.2 hRarg
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun r hr ↦ norm_nonneg _
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hSL : S < (L : ℝ) * R := by
    have heven' : S ^ 2 < ((L : ℝ) * R) ^ 2 := by
      calc
        S ^ 2 < 2 * (L : ℝ) ^ 2 * (Real.sqrt P + η) := by
          simpa only [S, P] using heven
        _ = ((L : ℝ) * R) ^ 2 := by
          rw [mul_pow, hRsq]
          ring
    have hLR : 0 < (L : ℝ) * R := mul_pos hLreal hR
    nlinarith
  let Qlim : ℝ :=
    (Finset.range L).sum (fun h ↦
      (Finset.range L).sum (fun k ↦
        (productOfMeans M
          (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
          (fun x ↦ star
            (MultipleKhintchineCharacteristic.leftPairFunction
              M hM F h k x))).re))
  have hQnorm :
      Qlim ≤ (Finset.range L).sum (fun h ↦
        (Finset.range L).sum (fun k ↦
          ‖productOfMeans M
            (MultipleKhintchineCharacteristic.rightPairFunction
              M hM G h k)
            (fun x ↦ star
              (MultipleKhintchineCharacteristic.leftPairFunction
                M hM F h k x))‖)) := by
    dsimp only [Qlim]
    gcongr with h hh k hk
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hsumBound :=
    MultipleKhintchineCharacteristic.sum_pairLimit_norm_le
      M hM F G C hC hFbound L
  have hQbound :
      Qlim ≤ 2 * (L : ℝ) ^ 2 * C ^ 2 * R := by
    calc
      Qlim ≤ (Finset.range L).sum (fun h ↦
          (Finset.range L).sum (fun k ↦
            ‖productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))‖)) := hQnorm
      _ ≤ 2 * (L : ℝ) * C ^ 2 * S := by
        simpa only [S] using hsumBound
      _ ≤ 2 * (L : ℝ) ^ 2 * C ^ 2 * R := by
        have hcoef : 0 ≤ 2 * (L : ℝ) * C ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hSL.le hcoef
        nlinarith
  let ρ : ℝ := η / 2
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    positivity
  have hall :
      ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ Finset.range L, ∀ k ∈ Finset.range L, ∀ i : ℕ,
          |cesaroAverage
              (fun n ↦
                (@inner ℂ (Lp ℂ 2 M.μ) _
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + k)))
                  (MultipleKhintchineCharacteristic.doubleKoopmanProduct
                    M hM F G hFtop (i + (n + h)))).re) N -
            (productOfMeans M
              (MultipleKhintchineCharacteristic.rightPairFunction
                M hM G h k)
              (fun x ↦ star
                (MultipleKhintchineCharacteristic.leftPairFunction
                  M hM F h k x))).re| < ρ := by
    rw [Filter.eventually_all_finset]
    intro h hh
    rw [Filter.eventually_all_finset]
    intro k hk
    exact
      MultipleKhintchineUniform.uniform_shifted_cesaro_re_inner_doubleKoopmanProduct
        M hM hErg F G hFtop hGtop h k ρ hρ
  refine ⟨L, hL, ?_⟩
  filter_upwards [hall] with N hN
  intro i
  let A : ℕ → ℕ → ℝ := fun h k ↦
    cesaroAverage
      (fun n ↦
        (@inner ℂ (Lp ℂ 2 M.μ) _
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + k)))
          (MultipleKhintchineCharacteristic.doubleKoopmanProduct
            M hM F G hFtop (i + (n + h)))).re) N
  let Qpair : ℕ → ℕ → ℝ := fun h k ↦
    (productOfMeans M
      (MultipleKhintchineCharacteristic.rightPairFunction M hM G h k)
      (fun x ↦ star
        (MultipleKhintchineCharacteristic.leftPairFunction
          M hM F h k x))).re
  have hdecomp :
      cesaroAverage
        (fun n ↦ ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L,
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + k)))
            (MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + (n + h)))).re) N =
        ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, A h k := by
    unfold A cesaroAverage
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_comm]
  have hdiff :
      |(∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, A h k) - Qlim| ≤
        (L : ℝ) ^ 2 * ρ := by
    have hQ :
        Qlim = ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, Qpair h k := by
      rfl
    rw [hQ, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      |∑ h ∈ Finset.range L,
          ∑ k ∈ Finset.range L, (A h k - Qpair h k)| ≤
          ∑ h ∈ Finset.range L,
            |∑ k ∈ Finset.range L, (A h k - Qpair h k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range L,
          ∑ k ∈ Finset.range L, |A h k - Qpair h k| := by
        gcongr with h hh
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range L,
          ∑ _k ∈ Finset.range L, ρ := by
        gcongr with h hh k hk
        exact (hN h hh k hk i).le
      _ = (L : ℝ) ^ 2 * ρ := by
        simp
        ring
  rw [hdecomp]
  have hupper :=
    (le_abs_self
      ((∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, A h k) - Qlim))
  dsimp only [ρ, R, P] at hdiff hQbound ⊢
  nlinarith [sq_pos_of_pos hLreal]

/-- Quantitative generalized von Neumann estimate for the bilinear
progression, uniform over translated intervals. -/
lemma doubleKoopmanProduct_uniform_cesaro_norm_lt_hostKraU3Power
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            MultipleKhintchineCharacteristic.doubleKoopmanProduct
              M hM F G hFtop (i + n)‖ <
        Real.sqrt
          (2 * C ^ 2 *
              Real.sqrt (2 * (Real.sqrt
                (hostKraU3Power M hM (fun x ↦ G x) hGtop) + η)) + η) +
          η := by
  let B : ℝ :=
    2 * C ^ 2 *
      Real.sqrt (2 * (Real.sqrt
        (hostKraU3Power M hM (fun x ↦ G x) hGtop) + η)) + η
  have hB : 0 < B := by
    dsimp only [B]
    have houter : 0 ≤ Real.sqrt
        (2 * (Real.sqrt
          (hostKraU3Power M hM (fun x ↦ G x) hGtop) + η)) :=
      Real.sqrt_nonneg _
    positivity
  obtain ⟨L, hL, hcorr⟩ :=
    doubleKoopmanProduct_uniform_blockCorrelation_lt_hostKraU3Power
      M hM hErg F G hFtop hGtop C hC hFbound η hη
  rw [Filter.eventually_atTop] at hcorr
  obtain ⟨Nb, hNb⟩ := hcorr
  let M₀ : ℝ := C * ‖G‖
  have hM₀ : 0 ≤ M₀ := mul_nonneg hC (norm_nonneg G)
  obtain ⟨N₀ : ℕ, hN₀⟩ :=
    exists_nat_gt (2 * (L : ℝ) * M₀ / η)
  refine Filter.eventually_atTop.2 ⟨max Nb N₀, ?_⟩
  intro N hN i
  have hNbN : Nb ≤ N := le_trans (le_max_left _ _) hN
  have hN₀N : N₀ ≤ N := le_trans (le_max_right _ _) hN
  have hCavg := hNb N hNbN i
  let u : ℕ → Lp ℂ 2 M.μ := fun n ↦
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM F G hFtop n
  let v : ℕ → Lp ℂ 2 M.μ := fun n ↦ u (i + n)
  let Craw : ℝ :=
    ∑ n ∈ Finset.range (N + 1),
      ∑ h ∈ Finset.range L,
        ∑ k ∈ Finset.range L,
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (v (n + k)) (v (n + h))).re
  have hNpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hCavg' :
      (((N + 1 : ℕ) : ℝ)⁻¹) * Craw <
        B * (L : ℝ) ^ 2 := by
    simpa only [cesaroAverage, Craw, v, u, B, Nat.add_assoc] using hCavg
  have hCraw :
      Craw < ((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2) := by
    calc
      Craw = ((N + 1 : ℕ) : ℝ) *
          ((((N + 1 : ℕ) : ℝ)⁻¹) * Craw) := by field_simp
      _ < ((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hCavg' hNpos
  let Block : Lp ℂ 2 M.μ := ∑ n ∈ Finset.range (N + 1),
    ∑ h ∈ Finset.range L, v (n + h)
  have hblockSq : ‖Block‖ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) * Craw :=
    VanDerCorput.norm_sum_forwardBlocks_sq_le v L (N + 1)
  have hNC : 0 ≤ ((N + 1 : ℕ) : ℝ) * Craw :=
    (sq_nonneg ‖Block‖).trans hblockSq
  have hsqrtSq :
      (Real.sqrt (((N + 1 : ℕ) : ℝ) * Craw)) ^ 2 =
        ((N + 1 : ℕ) : ℝ) * Craw :=
    Real.sq_sqrt hNC
  have hsqrtB :
      (Real.sqrt B) ^ 2 = B :=
    Real.sq_sqrt hB.le
  have hroot :
      Real.sqrt (((N + 1 : ℕ) : ℝ) * Craw) <
        Real.sqrt B * (L : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hupper :
        ((N + 1 : ℕ) : ℝ) * Craw <
          (Real.sqrt B * (L : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 := by
      have hfirst :
          ((N + 1 : ℕ) : ℝ) * Craw <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hCraw hNpos
      calc
        ((N + 1 : ℕ) : ℝ) * Craw <
            ((N + 1 : ℕ) : ℝ) *
              (((N + 1 : ℕ) : ℝ) * (B * (L : ℝ) ^ 2)) := hfirst
        _ = (Real.sqrt B * (L : ℝ) *
              ((N + 1 : ℕ) : ℝ)) ^ 2 := by
          rw [mul_pow, mul_pow, hsqrtB]
          ring
    have hsqrtNonneg :=
      Real.sqrt_nonneg (((N + 1 : ℕ) : ℝ) * Craw)
    have hrhspos :
        0 < Real.sqrt B * (L : ℝ) * ((N + 1 : ℕ) : ℝ) := by
      have : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
      positivity
    nlinarith
  have hboundary :
      2 * (L : ℝ) ^ 2 * M₀ <
        η * (L : ℝ) * ((N + 1 : ℕ) : ℝ) := by
    have hN₀real : (2 * (L : ℝ) * M₀ / η) < (N₀ : ℝ) := hN₀
    have hNreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
    have hratio :
        2 * (L : ℝ) * M₀ / η <
          ((N + 1 : ℕ) : ℝ) := by
      calc
        2 * (L : ℝ) * M₀ / η < (N₀ : ℝ) := hN₀real
        _ ≤ (N : ℝ) := hNreal
        _ < ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.lt_succ_self N
    have hlarge :
        2 * (L : ℝ) * M₀ <
          η * ((N + 1 : ℕ) : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hη).1 hratio
    nlinarith [sq_pos_of_pos hLreal]
  have hu : ∀ n, ‖v n‖ ≤ M₀ := by
    intro n
    exact MultipleKhintchineCharacteristic.norm_doubleKoopmanProduct_le
      M hM F G hFtop C hC hFbound (i + n)
  have hvdc :=
    VanDerCorput.finite_vanDerCorput v M₀ L (N + 1) hu
  change (L : ℝ) *
      ‖∑ n ∈ Finset.range (N + 1), v n‖ ≤
    Real.sqrt (((N + 1 : ℕ) : ℝ) * Craw) +
      2 * (L : ℝ) ^ 2 * M₀ at hvdc
  change
    ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
      ∑ n ∈ Finset.range (N + 1), v n‖ <
        Real.sqrt B + η
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  have hsum :
      ‖∑ n ∈ Finset.range (N + 1), v n‖ <
        (Real.sqrt B + η) * ((N + 1 : ℕ) : ℝ) := by
    nlinarith [sq_pos_of_pos hLreal]
  rw [inv_mul_lt_iff₀ hNpos]
  simpa only [mul_comm] using hsum

/-- A scalar Cesàro average of real parts of Hilbert pairings is the real
part of the pairing against the vector Cesàro average. -/
lemma cesaroAverage_re_inner_right
    (M : System.{u})
    (A : Lp ℂ 2 M.μ) (v : ℕ → Lp ℂ 2 M.μ) (N : ℕ) :
    cesaroAverage
        (fun n ↦ (@inner ℂ (Lp ℂ 2 M.μ) _ A (v n)).re) N =
      (@inner ℂ (Lp ℂ 2 M.μ) _ A
        ((((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n)).re := by
  rw [MultipleKhintchineUniform.cesaroAverage_re_eq]
  congr 1
  rw [inner_smul_right, inner_sum]

/-- Elementary bound used to turn the nested square roots in the
quantitative bilinear estimate into a linear small parameter. -/
lemma nested_sqrt_hostKraU3_bound
    (C t p : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : 0 ≤ p) (hpt : p ≤ t ^ 8) :
    Real.sqrt
        (2 * C ^ 2 *
            Real.sqrt (2 * (Real.sqrt p + t ^ 8)) + t ^ 8) +
        t ^ 8 ≤
      (Real.sqrt (4 * C ^ 2 + 1) + 1) * t := by
  have ht2 : t ^ 2 ≤ t := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have ht2one : t ^ 2 ≤ 1 := le_trans ht2 ht1
  have ht4nonneg : 0 ≤ t ^ 4 := by positivity
  have ht4 : t ^ 4 ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2), mul_nonneg (sq_nonneg t)
      (sub_nonneg.mpr ht2one)]
  have ht4one : t ^ 4 ≤ 1 := le_trans ht4 ht2one
  have ht8 : t ^ 8 ≤ t ^ 4 := by
    nlinarith [sq_nonneg (t ^ 4), mul_nonneg ht4nonneg
      (sub_nonneg.mpr ht4one)]
  have ht8t : t ^ 8 ≤ t :=
    le_trans ht8 (le_trans ht4 ht2)
  have hsqrtpSq : (Real.sqrt p) ^ 2 = p :=
    Real.sq_sqrt hp
  have hsqrtp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hsqrtp_le : Real.sqrt p ≤ t ^ 4 := by
    nlinarith
  let X : ℝ := 2 * (Real.sqrt p + t ^ 8)
  have hX : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hXle : X ≤ 4 * t ^ 4 := by
    dsimp only [X]
    nlinarith
  have hsqrtXsq : (Real.sqrt X) ^ 2 = X :=
    Real.sq_sqrt hX
  have hsqrtX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsqrtXle : Real.sqrt X ≤ 2 * t ^ 2 := by
    nlinarith
  let Y : ℝ := 2 * C ^ 2 * Real.sqrt X + t ^ 8
  have hY : 0 ≤ Y := by
    dsimp only [Y]
    positivity
  have hYle : Y ≤ (4 * C ^ 2 + 1) * t ^ 2 := by
    dsimp only [Y]
    have ht8t2 : t ^ 8 ≤ t ^ 2 :=
      le_trans ht8 ht4
    nlinarith [sq_nonneg C]
  let K : ℝ := 4 * C ^ 2 + 1
  have hK : 0 ≤ K := by
    dsimp only [K]
    nlinarith [sq_nonneg C]
  have hsqrtYsq : (Real.sqrt Y) ^ 2 = Y :=
    Real.sq_sqrt hY
  have hsqrtY : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hsqrtKsq : (Real.sqrt K) ^ 2 = K :=
    Real.sq_sqrt hK
  have hsqrtK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsqrtYle : Real.sqrt Y ≤ Real.sqrt K * t := by
    have hrhs : 0 ≤ Real.sqrt K * t := mul_nonneg hsqrtK ht
    nlinarith
  change Real.sqrt Y + t ^ 8 ≤ (Real.sqrt K + 1) * t
  nlinarith

/-- Finite Markov counting estimate in the exact form used to separate
large derivative powers from small ones in a correlation row. -/
lemma card_filter_threshold_mul_lt_of_sum_lt
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (H : ℕ) (τ α : ℝ)
    (hsum : (Finset.range H).sum a < α * (H : ℝ)) :
    (((Finset.range H).filter (fun k ↦ τ ≤ a k)).card : ℝ) * τ <
      α * (H : ℝ) := by
  let B := (Finset.range H).filter (fun k ↦ τ ≤ a k)
  calc
    (B.card : ℝ) * τ = B.sum (fun _ ↦ τ) := by
      simp [mul_comm]
    _ ≤ B.sum a := by
      apply Finset.sum_le_sum
      intro k hk
      exact (Finset.mem_filter.mp hk).2
    _ ≤ (Finset.range H).sum a := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun n hn hnot ↦ ha n)
    _ < α * (H : ℝ) := hsum

/-- The eight-vertex alternating lift is multiplicative. -/
lemma cubeLiftThree_mul
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) :
    cubeLiftThree M hM (fun x ↦ f x * g x) =
      fun p ↦ cubeLiftThree M hM f p * cubeLiftThree M hM g p := by
  funext p
  simp only [cubeLiftThree, cubeLiftTwo, cubeLiftOne, cubeLift, star_mul]
  ring

/-- The eight-vertex alternating lift commutes with pointwise
conjugation. -/
lemma cubeLiftThree_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) :
    cubeLiftThree M hM (fun x ↦ star (f x)) =
      fun p ↦ star (cubeLiftThree M hM f p) := by
  funext p
  simp only [cubeLiftThree, cubeLiftTwo, cubeLiftOne, cubeLift, star_mul,
    star_star]
  ring

/-- The eight-vertex lift intertwines every forward base iterate with
the corresponding cube-system iterate. -/
lemma cubeLiftThree_iter
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (n : ℕ) :
    cubeLiftThree M hM (f ∘ (M.T^[n])) =
      cubeLiftThree M hM f ∘
        ((HostKraStandardRelativeJoining.relativeCubeSystemThree M hM).T^[n]) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [show f ∘ (M.T^[n + 1]) = (f ∘ (M.T^[n])) ∘ M.T by
        funext x
        simp only [Function.comp_apply, Function.iterate_succ_apply]]
      rw [HostKraCubeSeminormDynamics.cubeLiftThree_comp, ih]
      funext p
      simp only [Function.comp_apply, Function.iterate_succ_apply]

/-- Lifting a canonical multiplicative derivative through all three cube
directions gives the ordinary self-correlation integrand of the
eight-vertex lift. -/
lemma cubeLiftThree_cubeDerivative_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ) (n : ℕ) :
    cubeLiftThree M hM (HostKraCubeTwo.cubeDerivative M hM Q n)
      =ᵐ[(HostKraStandardRelativeJoining.relativeCubeSystemThree M hM).μ]
    fun p ↦
      cubeLiftThree M hM (fun x ↦ Q x)
          (((HostKraStandardRelativeJoining.relativeCubeSystemThree
            M hM).T^[n]) p) *
        star (cubeLiftThree M hM (fun x ↦ Q x) p) := by
  let C2 :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM
  let hC2 :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo_mps M hM
  have hbase :=
    HostKraCubeTwo.cubeDerivative_ae_eq M hM Q n
  have hliftTwo :=
    Chapter02.HostKraU3Nullspace.cubeLiftTwo_congr_ae M hM hbase
  have hliftThree :=
    Chapter02.HostKraU3Nullspace.cubeLift_congr_ae
      C2 hC2 hliftTwo
  have hpoint :
      cubeLiftThree M hM
          (fun x ↦ Q ((M.T^[n]) x) * star (Q x)) =
        fun p ↦
          cubeLiftThree M hM (fun x ↦ Q x)
              (((HostKraStandardRelativeJoining.relativeCubeSystemThree
                M hM).T^[n]) p) *
            star (cubeLiftThree M hM (fun x ↦ Q x) p) := by
    rw [cubeLiftThree_mul]
    change
      (fun p ↦
        cubeLiftThree M hM ((fun x ↦ Q x) ∘ (M.T^[n])) p *
          cubeLiftThree M hM (fun x ↦ star (Q x)) p) = _
    rw [cubeLiftThree_iter, cubeLiftThree_star]
    rfl
  have hliftThree' :
      cubeLiftThree M hM (HostKraCubeTwo.cubeDerivative M hM Q n)
        =ᵐ[(HostKraStandardRelativeJoining.relativeCubeSystemThree M hM).μ]
      cubeLiftThree M hM
        (fun x ↦ Q ((M.T^[n]) x) * star (Q x)) := by
    simpa only [cubeLiftThree] using hliftThree
  exact hliftThree'.trans
    (Filter.Eventually.of_forall (fun p ↦ congrFun hpoint p))

/-- The quantitative `U³` power depends only on the almost-everywhere
class of a bounded representative. -/
lemma hostKraU3Power_congr_ae
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f g : M.X → ℂ) (hf : MemLp f ⊤ M.μ) (hg : MemLp g ⊤ M.μ)
    (hfg : f =ᵐ[M.μ] g) :
    hostKraU3Power M hM f hf = hostKraU3Power M hM g hg := by
  let C := HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM
  let hC :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo_mps M hM
  let F := cubeLiftTwo M hM f
  let G := cubeLiftTwo M hM g
  let hF := cubeLiftTwo_memLp_two M hM f hf
  let hG := cubeLiftTwo_memLp_two M hM g hg
  have hFG : hF.toLp F = hG.toLp G :=
    MemLp.toLp_congr hF hG
      (Chapter02.HostKraU3Nullspace.cubeLiftTwo_congr_ae M hM hfg)
  unfold hostKraU3Power
  change
    HostKraCubeSeminorm.invariantEnergy C hC F hF =
      HostKraCubeSeminorm.invariantEnergy C hC G hG
  unfold HostKraCubeSeminorm.invariantEnergy
  rw [HostKraRelativeMean.invariantMeanLp_eq_fixedProjection,
    HostKraRelativeMean.invariantMeanLp_eq_fixedProjection]
  change
    ‖((LinearMap.eqLocus
      (KData C hC).U
      (1 : Lp ℂ 2 C.μ →L[ℂ] Lp ℂ 2 C.μ)).orthogonalProjection
        (hF.toLp F)).val‖ ^ 2 =
      ‖((LinearMap.eqLocus
        (KData C hC).U
        (1 : Lp ℂ 2 C.μ →L[ℂ] Lp ℂ 2 C.μ)).orthogonalProjection
          (hG.toLp G)).val‖ ^ 2
  rw [hFG]

/-- Exact recursive identity: the `U³` power of the canonical derivative
at edge `n` is the self-correlation at time `n` of the eight-vertex lift.
This is the quantitative bridge from `U⁴` to the derivative powers. -/
lemma ofReal_hostKraU3Power_cubeDerivativeLp
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (n : ℕ) :
    ((hostKraU3Power M hM
      (fun x ↦ HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop n x)
      (HostKraCubeThree.cubeDerivativeLp_memLp_top
        M hM Q hQtop n) : ℝ) : ℂ) =
      functionCorrelation
        (HostKraStandardRelativeJoining.relativeCubeSystemThree M hM)
        (cubeLiftThree M hM (fun x ↦ Q x))
        (cubeLiftThree M hM (fun x ↦ Q x)) n := by
  let D := HostKraCubeTwo.cubeDerivative M hM Q n
  let hDtop :=
    HostKraCubeTwo.cubeDerivative_memLp_top M hM Q hQtop n
  have hpower :
      hostKraU3Power M hM
          (fun x ↦ HostKraCubeThree.cubeDerivativeLp
            M hM Q hQtop n x)
          (HostKraCubeThree.cubeDerivativeLp_memLp_top
            M hM Q hQtop n) =
        hostKraU3Power M hM D hDtop :=
    hostKraU3Power_congr_ae M hM _ _ _ _
      (HostKraCubeThree.cubeDerivativeLp_coe M hM Q hQtop n)
  let C2 :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM
  let hC2 :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo_mps M hM
  have henergy :=
    Chapter02.HostKraRelativeJoiningComplex.integral_cubeLift_eq_invariantEnergy
      C2 hC2
      (cubeLiftTwo M hM D)
      (cubeLiftTwo_memLp_top M hM D hDtop)
  calc
    _ = ((hostKraU3Power M hM D hDtop : ℝ) : ℂ) := by
      exact congrArg (fun r : ℝ ↦ (r : ℂ)) hpower
    _ = ∫ p, cubeLiftThree M hM D p
          ∂(HostKraStandardRelativeJoining.relativeCubeSystemThree M hM).μ := by
      simpa only [hostKraU3Power, cubeLiftThree, C2, hC2] using henergy.symm
    _ = functionCorrelation
          (HostKraStandardRelativeJoining.relativeCubeSystemThree M hM)
          (cubeLiftThree M hM (fun x ↦ Q x))
          (cubeLiftThree M hM (fun x ↦ Q x)) n := by
      unfold functionCorrelation
      exact integral_congr_ae
        (cubeLiftThree_cubeDerivative_ae M hM Q n)

/-- If `Q` is `U⁴`-null, the translated Cesàro averages of the `U³`
powers of all its canonical multiplicative derivatives converge
uniformly to zero. -/
lemma hasZeroHostKraU4_uniform_cubeDerivativeU3Power_zero
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM (fun x ↦ Q x) hQtop) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        dist
          (if N = 0 then 0 else
            ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
              ((hostKraU3Power M hM
                (fun x ↦ HostKraCubeThree.cubeDerivativeLp
                  M hM Q hQtop (i + n) x)
                (HostKraCubeThree.cubeDerivativeLp_memLp_top
                  M hM Q hQtop (i + n)) : ℝ) : ℂ))
          0 < ε := by
  intro ε hε
  have hlimit :=
    Chapter02.HostKraCubeSeminormRecursion.hasZeroHostKraU4_uniform_cubeCorrelation_zero
      M hM (fun x ↦ Q x) hQtop hzero ε hε
  filter_upwards [hlimit] with N hN
  intro i
  simpa only [ofReal_hostKraU3Power_cubeDerivativeLp] using hN i

/-- Real-valued form of the preceding uniform derivative-power limit. -/
lemma cubeDerivativeU3Power_average_tendsto_zero_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM (fun x ↦ Q x) hQtop) :
    Tendsto
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
          hostKraU3Power M hM
            (fun x ↦ HostKraCubeThree.cubeDerivativeLp
              M hM Q hQtop n x)
            (HostKraCubeThree.cubeDerivativeLp_memLp_top
              M hM Q hQtop n))
      atTop (nhds 0) := by
  have huniform :=
    hasZeroHostKraU4_uniform_cubeDerivativeU3Power_zero
      M hM Q hQtop hzero
  have hcomplex :
      Tendsto
        (fun N : ℕ ↦ if N = 0 then 0 else
          ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
            ((hostKraU3Power M hM
              (fun x ↦ HostKraCubeThree.cubeDerivativeLp
                M hM Q hQtop n x)
              (HostKraCubeThree.cubeDerivativeLp_memLp_top
                M hM Q hQtop n) : ℝ) : ℂ))
        atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 (huniform ε hε)
    refine ⟨N, ?_⟩
    intro n hn
    simpa using hN n hn 0
  rw [show
      (fun N : ℕ ↦ if N = 0 then 0 else
        ((N : ℂ)⁻¹) * ∑ n ∈ Finset.range N,
          ((hostKraU3Power M hM
            (fun x ↦ HostKraCubeThree.cubeDerivativeLp
              M hM Q hQtop n x)
            (HostKraCubeThree.cubeDerivativeLp_memLp_top
              M hM Q hQtop n) : ℝ) : ℂ)) =
        fun N : ℕ ↦ ((if N = 0 then 0 else
          ((N : ℝ)⁻¹) * ∑ n ∈ Finset.range N,
            hostKraU3Power M hM
              (fun x ↦ HostKraCubeThree.cubeDerivativeLp
                M hM Q hQtop n x)
              (HostKraCubeThree.cubeDerivativeLp_memLp_top
                M hM Q hQtop n) : ℝ) : ℂ) by
    funext N
    by_cases hN : N = 0
    · simp [hN]
    · simp only [hN, if_false]
      push_cast
      rfl] at hcomplex
  simpa only [Function.comp_apply, Complex.ofReal_re, Complex.zero_re] using
    (Complex.continuous_re.continuousAt.tendsto.comp hcomplex)

/-- A `U⁴`-null vector has arbitrarily small finite sums of derivative
`U³` powers sampled at the triple times needed by the `(1,2,3)`
progression. -/
lemma exists_three_cubeDerivativeU3Power_sum_lt_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM (fun x ↦ Q x) hQtop)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧
      (Finset.range H).sum (fun r ↦
        hostKraU3Power M hM
          (fun x ↦ HostKraCubeThree.cubeDerivativeLp
            M hM Q hQtop (3 * r) x)
          (HostKraCubeThree.cubeDerivativeLp_memLp_top
            M hM Q hQtop (3 * r))) < δ * (H : ℝ) := by
  let a : ℕ → ℝ := fun n ↦
    hostKraU3Power M hM
      (fun x ↦ HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop n x)
      (HostKraCubeThree.cubeDerivativeLp_memLp_top
        M hM Q hQtop n)
  have ha : ∀ n, 0 ≤ a n := by
    intro n
    exact hostKraU3Power_nonneg M hM _ _
  have htend :
      Tendsto
        (fun N : ℕ ↦ if N = 0 then 0 else
          ((N : ℝ)⁻¹) * (Finset.range N).sum a)
        atTop (nhds 0) := by
    simpa only [a] using
      cubeDerivativeU3Power_average_tendsto_zero_of_hasZeroHostKraU4
        M hM Q hQtop hzero
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend (δ / 3) (by positivity)
  let H := N₀ + 1
  have hH : 0 < H := by
    dsimp only [H]
    omega
  have hlarge : N₀ ≤ 3 * H := by
    dsimp only [H]
    omega
  have havgdist := hN₀ (3 * H) hlarge
  have hthreeH : 3 * H ≠ 0 := by omega
  have havg_nonneg :
      0 ≤ (((3 * H : ℕ) : ℝ)⁻¹) *
        (Finset.range (3 * H)).sum a := by
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun n hn ↦ ha n)
  have havg :
      (((3 * H : ℕ) : ℝ)⁻¹) *
          (Finset.range (3 * H)).sum a < δ / 3 := by
    simpa only [hthreeH, if_false, Real.dist_eq, sub_zero,
      abs_of_nonneg havg_nonneg] using havgdist
  have hsub :
      (Finset.range H).sum (fun r ↦ a (3 * r)) ≤
        (Finset.range (3 * H)).sum a := by
    let e : ℕ → ℕ := fun r ↦ 3 * r
    have hinj : Set.InjOn e (Finset.range H) := by
      intro x hx y hy hxy
      dsimp only [e] at hxy
      omega
    have himage :
        (Finset.range H).image e ⊆ Finset.range (3 * H) := by
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
      apply Finset.mem_range.mpr
      have hrH := Finset.mem_range.mp hr
      dsimp only [e]
      omega
    calc
      (Finset.range H).sum (fun r ↦ a (3 * r)) =
          ((Finset.range H).image e).sum a := by
        rw [Finset.sum_image hinj]
      _ ≤ (Finset.range (3 * H)).sum a :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun n hn hnot ↦ ha n)
  refine ⟨H, hH, ?_⟩
  have hthreeHreal : (0 : ℝ) < (3 * H : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hH
  rw [inv_mul_lt_iff₀ hthreeHreal] at havg
  have hfull :
      (Finset.range (3 * H)).sum a < δ * (H : ℝ) := by
    have hcast : (((3 * H : ℕ) : ℝ)) = 3 * (H : ℝ) := by
      exact Nat.cast_mul 3 H
    rw [hcast] at havg
    nlinarith
  exact lt_of_le_of_lt hsub hfull

/-- The quantitative `U³` power is invariant under pointwise complex
conjugation. -/
lemma hostKraU3Power_star
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) :
    hostKraU3Power M hM (fun x ↦ star (f x)) hf.star =
      hostKraU3Power M hM f hf := by
  unfold hostKraU3Power
  let C := HostKraStandardRelativeJoining.relativeCubeSystemTwo M hM
  let hC :=
    HostKraStandardRelativeJoining.relativeCubeSystemTwo_mps M hM
  change
    HostKraCubeSeminorm.invariantEnergy C hC
        (cubeLiftTwo M hM (fun x ↦ star (f x))) _ =
      HostKraCubeSeminorm.invariantEnergy C hC
        (cubeLiftTwo M hM f) _
  simpa only [Chapter02.HostKraU3Nullspace.cubeLiftTwo_star] using
    invariantEnergy_star C hC
      (cubeLiftTwo M hM f)
      (cubeLiftTwo_memLp_two M hM f hf)

/-- The quantitative `U³` power is invariant under every forward iterate.
This formulation uses only measure preservation, not invertibility. -/
lemma hostKraU3Power_iter
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (f : M.X → ℂ) (hf : MemLp f ⊤ M.μ) (n : ℕ) :
    let hfn : MemLp (f ∘ (M.T^[n])) ⊤ M.μ :=
      hf.comp_measurePreserving (hM.2.iterate n)
    hostKraU3Power M hM (f ∘ (M.T^[n])) hfn =
      hostKraU3Power M hM f hf := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let hfn : MemLp (f ∘ (M.T^[n])) ⊤ M.μ :=
        hf.comp_measurePreserving (hM.2.iterate n)
      have hstep :=
        HostKraCubeSeminormDynamics.hostKraU3Power_comp
          M hM (f ∘ (M.T^[n])) hfn
      simpa only [Function.comp_apply, Function.iterate_succ_apply'] using
        hstep.trans ih

/-- For ordered times, the `U³` power of a two-time multiplicative
derivative depends only on their distance. -/
lemma hostKraU3Power_koopmanMultiplicativeDerivative_of_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) (hab : a ≤ b) :
    hostKraU3Power M hM
        (fun x ↦ koopmanMultiplicativeDerivative
          M hM Q hQtop a b x)
        (koopmanMultiplicativeDerivative_memLp_top
          M hM Q hQtop a b) =
      hostKraU3Power M hM
        (fun x ↦ HostKraCubeThree.cubeDerivativeLp
          M hM Q hQtop (b - a) x)
        (HostKraCubeThree.cubeDerivativeLp_memLp_top
          M hM Q hQtop (b - a)) := by
  let D :=
    HostKraCubeThree.cubeDerivativeLp M hM Q hQtop (b - a)
  let hDtop :=
    HostKraCubeThree.cubeDerivativeLp_memLp_top
      M hM Q hQtop (b - a)
  let hDiter :=
    hDtop.comp_measurePreserving (hM.2.iterate a)
  have hLp :=
    koopmanMultiplicativeDerivative_eq_iter_cubeDerivativeLp_of_le
      M hM Q hQtop a b hab
  have hcoe :
      (fun x ↦ koopmanMultiplicativeDerivative
        M hM Q hQtop a b x) =ᵐ[M.μ]
        (fun x ↦ D ((M.T^[a]) x)) := by
    filter_upwards [
      MultipleKhintchineKronecker.koopmanData_iter_ae
      M hM a D] with x hx
    rw [show
      koopmanMultiplicativeDerivative M hM Q hQtop a b x =
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[a]) D) x by
          exact congrFun (congrArg
            (fun F : Lp ℂ 2 M.μ ↦ fun y ↦ F y) hLp) x]
    exact hx
  calc
    _ = hostKraU3Power M hM
          (fun x ↦ D ((M.T^[a]) x)) hDiter :=
      hostKraU3Power_congr_ae M hM _ _ _ _ hcoe
    _ = hostKraU3Power M hM (fun x ↦ D x) hDtop := by
      simpa only [Function.comp_apply] using
        hostKraU3Power_iter M hM (fun x ↦ D x) hDtop a

/-- In the reverse order the same distance formula follows through
pointwise conjugation, still using only forward iterates. -/
lemma hostKraU3Power_koopmanMultiplicativeDerivative_of_ge
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (a b : ℕ) (hba : b ≤ a) :
    hostKraU3Power M hM
        (fun x ↦ koopmanMultiplicativeDerivative
          M hM Q hQtop a b x)
        (koopmanMultiplicativeDerivative_memLp_top
          M hM Q hQtop a b) =
      hostKraU3Power M hM
        (fun x ↦ HostKraCubeThree.cubeDerivativeLp
          M hM Q hQtop (a - b) x)
        (HostKraCubeThree.cubeDerivativeLp_memLp_top
          M hM Q hQtop (a - b)) := by
  let D :=
    HostKraCubeThree.cubeDerivativeLp M hM Q hQtop (a - b)
  let hDtop :=
    HostKraCubeThree.cubeDerivativeLp_memLp_top
      M hM Q hQtop (a - b)
  let S := ForwardKroneckerFactor.lpStar M D
  let hStop :=
    HostKraDualFunction.lpStar_memLp_top M D hDtop
  let hSiter :=
    hStop.comp_measurePreserving (hM.2.iterate b)
  have hLp :=
    koopmanMultiplicativeDerivative_eq_iter_star_cubeDerivativeLp_of_le
      M hM Q hQtop a b hba
  have hcoe :
      (fun x ↦ koopmanMultiplicativeDerivative
        M hM Q hQtop a b x) =ᵐ[M.μ]
        (fun x ↦ S ((M.T^[b]) x)) := by
    filter_upwards [
      MultipleKhintchineKronecker.koopmanData_iter_ae
        M hM b S] with x hx
    rw [show
      koopmanMultiplicativeDerivative M hM Q hQtop a b x =
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[b]) S) x by
          exact congrFun (congrArg
            (fun F : Lp ℂ 2 M.μ ↦ fun y ↦ F y) hLp) x]
    exact hx
  calc
    _ = hostKraU3Power M hM
          (fun x ↦ S ((M.T^[b]) x)) hSiter :=
      hostKraU3Power_congr_ae M hM _ _ _ _ hcoe
    _ = hostKraU3Power M hM (fun x ↦ S x) hStop := by
      simpa only [Function.comp_apply] using
        hostKraU3Power_iter M hM (fun x ↦ S x) hStop b
    _ = hostKraU3Power M hM
          (fun x ↦ star (D x)) hDtop.star :=
      hostKraU3Power_congr_ae M hM _ _ _ _
        (ForwardKroneckerFactor.lpStar_coe M D)
    _ = hostKraU3Power M hM (fun x ↦ D x) hDtop :=
      hostKraU3Power_star M hM (fun x ↦ D x) hDtop

/-- In a finite correlation row, the `U³` powers of all two-time
derivatives are bounded by twice the sum of the canonical derivative
powers indexed by their nonnegative distances. -/
lemma sum_hostKraU3Power_koopmanMultiplicativeDerivative_mul_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (c H h : ℕ) (hh : h < H) :
    (Finset.range H).sum (fun k ↦
        hostKraU3Power M hM
          (fun x ↦ koopmanMultiplicativeDerivative
            M hM Q hQtop (c * k) (c * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM Q hQtop (c * k) (c * h))) ≤
      2 * (Finset.range H).sum (fun r ↦
        hostKraU3Power M hM
          (fun x ↦ HostKraCubeThree.cubeDerivativeLp
            M hM Q hQtop (c * r) x)
          (HostKraCubeThree.cubeDerivativeLp_memLp_top
            M hM Q hQtop (c * r))) := by
  let a : ℕ → ℝ := fun r ↦
    hostKraU3Power M hM
      (fun x ↦ HostKraCubeThree.cubeDerivativeLp
        M hM Q hQtop (c * r) x)
      (HostKraCubeThree.cubeDerivativeLp_memLp_top
        M hM Q hQtop (c * r))
  have ha : ∀ r, 0 ≤ a r := by
    intro r
    exact hostKraU3Power_nonneg M hM _ _
  calc
    (Finset.range H).sum (fun k ↦
        hostKraU3Power M hM
          (fun x ↦ koopmanMultiplicativeDerivative
            M hM Q hQtop (c * k) (c * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM Q hQtop (c * k) (c * h))) =
      (Finset.range H).sum (fun k ↦
        if k ≤ h then a (h - k) else a (k - h)) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkh : k ≤ h
          · rw [if_pos hkh]
            have hmul : c * k ≤ c * h :=
              Nat.mul_le_mul_left c hkh
            simpa only [a, Nat.mul_sub_left_distrib] using
              hostKraU3Power_koopmanMultiplicativeDerivative_of_le
                M hM Q hQtop (c * k) (c * h) hmul
          · rw [if_neg hkh]
            have hhk : h ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkh)
            have hmul : c * h ≤ c * k :=
              Nat.mul_le_mul_left c hhk
            simpa only [a, Nat.mul_sub_left_distrib] using
              hostKraU3Power_koopmanMultiplicativeDerivative_of_ge
                M hM Q hQtop (c * k) (c * h) hmul
    _ ≤ 2 * (Finset.range H).sum a :=
      MultipleKhintchineCharacteristic.sum_range_split_distance_le
        a ha H h hh

/-- Under `U⁴` nullity, one finite block makes every row of triple-time
derivative `U³` powers uniformly small. -/
lemma exists_uniform_three_derivativeU3Power_row_sum_lt
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (Q : Lp ℂ 2 M.μ)
    (hQtop : MemLp (fun x ↦ Q x) ⊤ M.μ)
    (hzero : HasZeroHostKraU4 M hM (fun x ↦ Q x) hQtop)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ H : ℕ, 0 < H ∧ ∀ h < H,
      (Finset.range H).sum (fun k ↦
        hostKraU3Power M hM
          (fun x ↦ koopmanMultiplicativeDerivative
            M hM Q hQtop (3 * k) (3 * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM Q hQtop (3 * k) (3 * h))) <
        2 * δ * (H : ℝ) := by
  obtain ⟨H, hH, hsmall⟩ :=
    exists_three_cubeDerivativeU3Power_sum_lt_of_hasZeroHostKraU4
      M hM Q hQtop hzero δ hδ
  refine ⟨H, hH, ?_⟩
  intro h hh
  have hrow :=
    sum_hostKraU3Power_koopmanMultiplicativeDerivative_mul_le
      M hM Q hQtop 3 H h hh
  calc
    _ ≤ 2 * (Finset.range H).sum (fun r ↦
          hostKraU3Power M hM
            (fun x ↦ HostKraCubeThree.cubeDerivativeLp
              M hM Q hQtop (3 * r) x)
            (HostKraCubeThree.cubeDerivativeLp_memLp_top
              M hM Q hQtop (3 * r))) := hrow
    _ < 2 * δ * (H : ℝ) := by nlinarith

/-- The Hilbert-valued three-factor progression
`(U^n F) (U^(2n) G) (U^(3n) H)`.  The first two factors are required to
be essentially bounded so that the nested pointwise product belongs to
`L²`. -/
noncomputable def tripleKoopmanProduct
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (n : ℕ) : Lp ℂ 2 M.μ :=
  let Fn : Lp ℂ 2 M.μ := ((KData M hM).U^[n]) F
  let Gn : Lp ℂ 2 M.μ := ((KData M hM).U^[2 * n]) G
  let Hn : Lp ℂ 2 M.μ := ((KData M hM).U^[3 * n]) H
  let hFnTop :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM n F hFtop
  let hGnTop :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM (2 * n) G hGtop
  let FGn : Lp ℂ 2 M.μ :=
    MultipleKhintchineKronecker.lpPointwiseMul Fn Gn hFnTop
  let hFGnTop :=
    HostKraDualFunction.lpPointwiseMul_memLp_top Fn Gn hFnTop hGnTop
  MultipleKhintchineKronecker.lpPointwiseMul FGn Hn hFGnTop

lemma tripleKoopmanProduct_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (n : ℕ) :
    (fun x ↦ tripleKoopmanProduct M hM F G H hFtop hGtop n x) =ᵐ[M.μ]
      (fun x ↦
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[n]) F) x *
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[2 * n]) G) x *
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[3 * n]) H) x) := by
  dsimp only [tripleKoopmanProduct]
  filter_upwards [
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (MultipleKhintchineKronecker.lpPointwiseMul
        (((KData M hM).U^[n]) F)
        (((KData M hM).U^[2 * n]) G)
        (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
          M hM n F hFtop))
      (((KData M hM).U^[3 * n]) H)
      (HostKraDualFunction.lpPointwiseMul_memLp_top
        (((KData M hM).U^[n]) F)
        (((KData M hM).U^[2 * n]) G)
        (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
          M hM n F hFtop)
        (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
          M hM (2 * n) G hGtop)),
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (((KData M hM).U^[n]) F)
      (((KData M hM).U^[2 * n]) G)
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM n F hFtop)] with x houter hinner
  rw [houter, hinner]

/-- A uniform `L²` bound for the three-factor progression. -/
lemma norm_tripleKoopmanProduct_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (n : ℕ) :
    ‖tripleKoopmanProduct M hM F G H hFtop hGtop n‖ ≤
      (CF * CG) * ‖H‖ := by
  let Fn : Lp ℂ 2 M.μ := ((KData M hM).U^[n]) F
  let Gn : Lp ℂ 2 M.μ := ((KData M hM).U^[2 * n]) G
  let Hn : Lp ℂ 2 M.μ := ((KData M hM).U^[3 * n]) H
  let hFnTop :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM n F hFtop
  let hGnTop :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM (2 * n) G hGtop
  let FGn : Lp ℂ 2 M.μ :=
    MultipleKhintchineKronecker.lpPointwiseMul Fn Gn hFnTop
  let hFGnTop :=
    HostKraDualFunction.lpPointwiseMul_memLp_top Fn Gn hFnTop hGnTop
  have hFnBound : ∀ᵐ x ∂M.μ, ‖Fn x‖ ≤ CF :=
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM n F CF hFbound
  have hGnBound : ∀ᵐ x ∂M.μ, ‖Gn x‖ ≤ CG :=
    MultipleKhintchineKronecker.koopmanData_iter_norm_le
      M hM (2 * n) G CG hGbound
  have hFGnBound : ∀ᵐ x ∂M.μ, ‖FGn x‖ ≤ CF * CG := by
    filter_upwards [
      MultipleKhintchineKronecker.lpPointwiseMul_coe Fn Gn hFnTop,
      hFnBound, hGnBound] with x hcoe hFb hGb
    rw [hcoe, norm_mul]
    exact mul_le_mul hFb hGb (norm_nonneg _) hCF
  have hmul :=
    MultipleKhintchineKronecker.norm_lpPointwiseMul_le
      FGn Hn hFGnTop (CF * CG) (mul_nonneg hCF hCG) hFGnBound
  calc
    ‖tripleKoopmanProduct M hM F G H hFtop hGtop n‖ ≤
        (CF * CG) * ‖Hn‖ := by
      simpa only [tripleKoopmanProduct, Fn, Gn, Hn, hFnTop, hGnTop,
        FGn, hFGnTop] using hmul
    _ = (CF * CG) * ‖H‖ := by
      congr 1
      exact AlmostPeriodicIsometry.iterate_norm
        (KData M hM)
        (fun V ↦
          (Lp.compMeasurePreservingₗᵢ ℂ M.T hM.2).norm_map V)
        H (3 * n)

/-- The residual three-factor expression after removing a common `U^n`
from the term at time `n + h`. -/
noncomputable def shiftedTripleCore
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (n h : ℕ) : Lp ℂ 2 M.μ :=
  let Fh : Lp ℂ 2 M.μ := ((KData M hM).U^[h]) F
  let Gnh : Lp ℂ 2 M.μ := ((KData M hM).U^[n + 2 * h]) G
  let Hnh : Lp ℂ 2 M.μ := ((KData M hM).U^[2 * n + 3 * h]) H
  let hFhTop :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM h F hFtop
  let hGnhTop :=
    MultipleKhintchineKronecker.koopmanData_iter_memLp_top
      M hM (n + 2 * h) G hGtop
  let FGnh : Lp ℂ 2 M.μ :=
    MultipleKhintchineKronecker.lpPointwiseMul Fh Gnh hFhTop
  let hFGnhTop :=
    HostKraDualFunction.lpPointwiseMul_memLp_top
      Fh Gnh hFhTop hGnhTop
  MultipleKhintchineKronecker.lpPointwiseMul FGnh Hnh hFGnhTop

lemma shiftedTripleCore_coe
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (n h : ℕ) :
    (fun x ↦ shiftedTripleCore M hM F G H hFtop hGtop n h x) =ᵐ[M.μ]
      (fun x ↦
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[h]) F) x *
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[n + 2 * h]) G) x *
        (show Lp ℂ 2 M.μ from ((KData M hM).U^[2 * n + 3 * h]) H) x) := by
  dsimp only [shiftedTripleCore]
  filter_upwards [
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (MultipleKhintchineKronecker.lpPointwiseMul
        (((KData M hM).U^[h]) F)
        (((KData M hM).U^[n + 2 * h]) G)
        (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
          M hM h F hFtop))
      (((KData M hM).U^[2 * n + 3 * h]) H)
      (HostKraDualFunction.lpPointwiseMul_memLp_top
        (((KData M hM).U^[h]) F)
        (((KData M hM).U^[n + 2 * h]) G)
        (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
          M hM h F hFtop)
        (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
          M hM (n + 2 * h) G hGtop)),
    MultipleKhintchineKronecker.lpPointwiseMul_coe
      (((KData M hM).U^[h]) F)
      (((KData M hM).U^[n + 2 * h]) G)
      (MultipleKhintchineKronecker.koopmanData_iter_memLp_top
        M hM h F hFtop)] with x houter hinner
  rw [houter, hinner]

/-- Factoring the common `U^n` from a shifted three-factor progression
term. -/
lemma tripleKoopmanProduct_add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (n h : ℕ) :
    tripleKoopmanProduct M hM F G H hFtop hGtop (n + h) =
      ((KData M hM).U^[n])
        (shiftedTripleCore M hM F G H hFtop hGtop n h) := by
  apply Lp.ext
  have hcoreComp :=
    (hM.2.iterate n).quasiMeasurePreserving.ae
      (shiftedTripleCore_coe M hM F G H hFtop hGtop n h)
  filter_upwards [
    tripleKoopmanProduct_coe M hM F G H hFtop hGtop (n + h),
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n
      (shiftedTripleCore M hM F G H hFtop hGtop n h),
    hcoreComp,
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n
      (((KData M hM).U^[h]) F),
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n
      (((KData M hM).U^[n + 2 * h]) G),
    MultipleKhintchineKronecker.koopmanData_iter_ae M hM n
      (((KData M hM).U^[2 * n + 3 * h]) H)] with
      x hleft hright hcore hFiter hGiter hHiter
  rw [hleft, hright, hcore]
  have hFadd :
      ((KData M hM).U^[n + h]) F =
        ((KData M hM).U^[n]) (((KData M hM).U^[h]) F) := by
    rw [Function.iterate_add_apply]
  have hGadd :
      ((KData M hM).U^[2 * (n + h)]) G =
        ((KData M hM).U^[n])
          (((KData M hM).U^[n + 2 * h]) G) := by
    rw [← Function.iterate_add_apply]
    congr 2
    omega
  have hHadd :
      ((KData M hM).U^[3 * (n + h)]) H =
        ((KData M hM).U^[n])
          (((KData M hM).U^[2 * n + 3 * h]) H) := by
    rw [← Function.iterate_add_apply]
    congr 2
    omega
  rw [hFadd, hGadd, hHadd, hFiter, hGiter, hHiter]

/-- After factoring the common `U^n`, the correlation of two shifted
three-factor progression terms is the correlation of their residual
cores.  This is the exact isometric reduction used in the uniform
van der Corput block condition. -/
lemma inner_tripleKoopmanProduct_add
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (n h k : ℕ) :
    @inner ℂ (Lp ℂ 2 M.μ) _
        (tripleKoopmanProduct M hM F G H hFtop hGtop (n + k))
        (tripleKoopmanProduct M hM F G H hFtop hGtop (n + h)) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (shiftedTripleCore M hM F G H hFtop hGtop n k)
      (shiftedTripleCore M hM F G H hFtop hGtop n h) := by
  rw [tripleKoopmanProduct_add M hM F G H hFtop hGtop n k,
    tripleKoopmanProduct_add M hM F G H hFtop hGtop n h]
  exact MultipleKhintchineKronecker.koopmanData_iter_inner
    M hM n
      (shiftedTripleCore M hM F G H hFtop hGtop n k)
      (shiftedTripleCore M hM F G H hFtop hGtop n h)

/-- Uniform-block indexing form of
`inner_tripleKoopmanProduct_add`. -/
lemma inner_tripleKoopmanProduct_block
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (i n h k : ℕ) :
    @inner ℂ (Lp ℂ 2 M.μ) _
        (tripleKoopmanProduct M hM F G H hFtop hGtop
          (i + (n + k)))
        (tripleKoopmanProduct M hM F G H hFtop hGtop
          (i + (n + h))) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (shiftedTripleCore M hM F G H hFtop hGtop (i + n) k)
        (shiftedTripleCore M hM F G H hFtop hGtop (i + n) h) := by
  simpa only [Nat.add_assoc] using
    inner_tripleKoopmanProduct_add
      M hM F G H hFtop hGtop (i + n) h k

/-- A residual-core correlation is exactly a scalar pairing against a
bilinear `(1,2)` progression of the multiplicative derivatives of the
second and third inputs. -/
lemma inner_shiftedTripleCore_eq_derivative_doubleKoopmanProduct
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (n h k : ℕ) :
    @inner ℂ (Lp ℂ 2 M.μ) _
        (shiftedTripleCore M hM F G H hFtop hGtop n k)
        (shiftedTripleCore M hM F G H hFtop hGtop n h) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (ForwardKroneckerFactor.lpStar M
          (koopmanMultiplicativeDerivative M hM F hFtop k h))
        (MultipleKhintchineCharacteristic.doubleKoopmanProduct
          M hM
          (koopmanMultiplicativeDerivative M hM G hGtop (2 * k) (2 * h))
          (koopmanMultiplicativeDerivative M hM H hHtop (3 * k) (3 * h))
          (koopmanMultiplicativeDerivative_memLp_top
            M hM G hGtop (2 * k) (2 * h))
          n) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    shiftedTripleCore_coe M hM F G H hFtop hGtop n k,
    shiftedTripleCore_coe M hM F G H hFtop hGtop n h,
    ForwardKroneckerFactor.lpStar_coe M
      (koopmanMultiplicativeDerivative M hM F hFtop k h),
    koopmanMultiplicativeDerivative_coe M hM F hFtop k h,
    MultipleKhintchineCharacteristic.doubleKoopmanProduct_coe
      M hM
      (koopmanMultiplicativeDerivative M hM G hGtop (2 * k) (2 * h))
      (koopmanMultiplicativeDerivative M hM H hHtop (3 * k) (3 * h))
      (koopmanMultiplicativeDerivative_memLp_top
        M hM G hGtop (2 * k) (2 * h))
      n,
    koopmanMultiplicativeDerivative_iter_coe
      M hM G hGtop n (2 * k) (2 * h),
    koopmanMultiplicativeDerivative_iter_coe
      M hM H hHtop (2 * n) (3 * k) (3 * h)] with
      x hcoreK hcoreH hstarF hderivF hdouble hderivG hderivH
  rw [hcoreK, hcoreH, hstarF, hderivF, hdouble, hderivG, hderivH]
  simp only [RCLike.inner_apply, starRingEnd_apply, map_mul, star_mul,
    star_star]
  ring

/-- Direct van der Corput block-correlation reduction for the original
three-factor progression. -/
lemma inner_tripleKoopmanProduct_block_eq_derivative_doubleKoopmanProduct
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (i n h k : ℕ) :
    @inner ℂ (Lp ℂ 2 M.μ) _
        (tripleKoopmanProduct M hM F G H hFtop hGtop
          (i + (n + k)))
        (tripleKoopmanProduct M hM F G H hFtop hGtop
          (i + (n + h))) =
      @inner ℂ (Lp ℂ 2 M.μ) _
        (ForwardKroneckerFactor.lpStar M
          (koopmanMultiplicativeDerivative M hM F hFtop k h))
        (MultipleKhintchineCharacteristic.doubleKoopmanProduct
          M hM
          (koopmanMultiplicativeDerivative M hM G hGtop (2 * k) (2 * h))
          (koopmanMultiplicativeDerivative M hM H hHtop (3 * k) (3 * h))
          (koopmanMultiplicativeDerivative_memLp_top
            M hM G hGtop (2 * k) (2 * h))
          (i + n)) := by
  rw [inner_tripleKoopmanProduct_block
    M hM F G H hFtop hGtop i n h k]
  exact inner_shiftedTripleCore_eq_derivative_doubleKoopmanProduct
    M hM F G H hFtop hGtop hHtop (i + n) h k

/-- Trivial uniform upper bound for one scalar block-correlation average
of the three-factor progression. -/
lemma cesaroAverage_re_inner_tripleKoopmanProduct_block_le
    (M : System.{u}) (hM : Chapter01.IsMeasurePreservingSystem M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (N i h k : ℕ) :
    cesaroAverage
      (fun n ↦
        (@inner ℂ (Lp ℂ 2 M.μ) _
          (tripleKoopmanProduct M hM F G H hFtop hGtop
            (i + (n + k)))
          (tripleKoopmanProduct M hM F G H hFtop hGtop
            (i + (n + h)))).re) N ≤
      ((CF * CG) * ‖H‖) ^ 2 := by
  let B : ℝ := (CF * CG) * ‖H‖
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hterm (n : ℕ) :
      (@inner ℂ (Lp ℂ 2 M.μ) _
        (tripleKoopmanProduct M hM F G H hFtop hGtop
          (i + (n + k)))
        (tripleKoopmanProduct M hM F G H hFtop hGtop
          (i + (n + h)))).re ≤ B ^ 2 := by
    calc
      _ ≤ ‖@inner ℂ (Lp ℂ 2 M.μ) _
          (tripleKoopmanProduct M hM F G H hFtop hGtop
            (i + (n + k)))
          (tripleKoopmanProduct M hM F G H hFtop hGtop
            (i + (n + h)))‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ ≤ ‖tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + k))‖ *
            ‖tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + h))‖ :=
        norm_inner_le_norm _ _
      _ ≤ B * B := by
        exact mul_le_mul
          (norm_tripleKoopmanProduct_le
            M hM F G H hFtop hGtop CF CG hCF hCG
            hFbound hGbound (i + (n + k)))
          (norm_tripleKoopmanProduct_le
            M hM F G H hFtop hGtop CF CG hCF hCG
            hFbound hGbound (i + (n + h)))
          (norm_nonneg _) hB
      _ = B ^ 2 := by ring
  unfold cesaroAverage
  have hsum :
      (Finset.range (N + 1)).sum (fun n ↦
        (@inner ℂ (Lp ℂ 2 M.μ) _
          (tripleKoopmanProduct M hM F G H hFtop hGtop
            (i + (n + k)))
          (tripleKoopmanProduct M hM F G H hFtop hGtop
            (i + (n + h)))).re) ≤
        (((N + 1 : ℕ) : ℝ)) * B ^ 2 := by
    calc
      _ ≤ (Finset.range (N + 1)).sum (fun _ ↦ B ^ 2) := by
        exact Finset.sum_le_sum fun n hn ↦ hterm n
      _ = (((N + 1 : ℕ) : ℝ)) * B ^ 2 := by simp
  have hNpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  calc
    ((N + 1 : ℕ) : ℝ)⁻¹ * _ ≤
        ((N + 1 : ℕ) : ℝ)⁻¹ *
          (((N + 1 : ℕ) : ℝ) * B ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
    _ = B ^ 2 := by
      calc
        ((N + 1 : ℕ) : ℝ)⁻¹ *
            (((N + 1 : ℕ) : ℝ) * B ^ 2) =
            (((N + 1 : ℕ) : ℝ)⁻¹ *
              ((N + 1 : ℕ) : ℝ)) * B ^ 2 := by ring
        _ = B ^ 2 := by
          rw [inv_mul_cancel₀ (ne_of_gt hNpos)]
          exact one_mul _

/-- If the `U³` power of the third multiplicative derivative is at most
`t⁸`, then the corresponding scalar block correlation of the
three-factor progression is uniformly `O(t)`. -/
lemma cesaroAverage_re_inner_tripleKoopmanProduct_block_lt_of_u3_le
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (h k : ℕ)
    (hpower :
      hostKraU3Power M hM
          (fun x ↦
            koopmanMultiplicativeDerivative
              M hM H hHtop (3 * k) (3 * h) x)
          (koopmanMultiplicativeDerivative_memLp_top
            M hM H hHtop (3 * k) (3 * h)) ≤
        t ^ 8) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
      cesaroAverage
        (fun n ↦
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + k)))
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + h)))).re) N <
        (CF * ‖F‖ + 1) *
          (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t := by
  let DG : Lp ℂ 2 M.μ :=
    koopmanMultiplicativeDerivative M hM G hGtop (2 * k) (2 * h)
  let DH : Lp ℂ 2 M.μ :=
    koopmanMultiplicativeDerivative M hM H hHtop (3 * k) (3 * h)
  let A : Lp ℂ 2 M.μ :=
    ForwardKroneckerFactor.lpStar M
      (koopmanMultiplicativeDerivative M hM F hFtop k h)
  let hDGtop : MemLp (fun x ↦ DG x) ⊤ M.μ :=
    koopmanMultiplicativeDerivative_memLp_top
      M hM G hGtop (2 * k) (2 * h)
  let hDHtop : MemLp (fun x ↦ DH x) ⊤ M.μ :=
    koopmanMultiplicativeDerivative_memLp_top
      M hM H hHtop (3 * k) (3 * h)
  have hη : 0 < t ^ 8 := pow_pos ht 8
  have hquant :=
    doubleKoopmanProduct_uniform_cesaro_norm_lt_hostKraU3Power
      M hM hErg DG DH hDGtop hDHtop
      (CG ^ 2) (sq_nonneg CG)
      (by
        simpa only [DG] using
          koopmanMultiplicativeDerivative_norm_le
            M hM G hGtop CG hCG hGbound (2 * k) (2 * h))
      (t ^ 8) hη
  filter_upwards [hquant] with N hN
  intro i
  let v : ℕ → Lp ℂ 2 M.μ := fun n ↦
    MultipleKhintchineCharacteristic.doubleKoopmanProduct
      M hM DG DH hDGtop (i + n)
  have havg :
      cesaroAverage
        (fun n ↦
          (@inner ℂ (Lp ℂ 2 M.μ) _
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + k)))
            (tripleKoopmanProduct M hM F G H hFtop hGtop
              (i + (n + h)))).re) N =
        (@inner ℂ (Lp ℂ 2 M.μ) _ A
          ((((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1), v n)).re := by
    calc
      _ = cesaroAverage
          (fun n ↦ (@inner ℂ (Lp ℂ 2 M.μ) _ A (v n)).re) N := by
        apply congrArg (fun q : ℕ → ℝ ↦ cesaroAverage q N)
        funext n
        simpa only [A, v, DG, DH, hDGtop] using
          congrArg Complex.re
            (inner_tripleKoopmanProduct_block_eq_derivative_doubleKoopmanProduct
              M hM F G H hFtop hGtop hHtop i n h k)
      _ = _ := cesaroAverage_re_inner_right M A v N
  rw [havg]
  have hAnorm : ‖A‖ ≤ CF * ‖F‖ := by
    dsimp only [A]
    rw [ForwardKroneckerFactor.norm_lpStar]
    exact norm_koopmanMultiplicativeDerivative_le
      M hM F hFtop CF hCF hFbound k h
  have hD : 0 ≤ CF * ‖F‖ := mul_nonneg hCF (norm_nonneg F)
  have hpnonneg :
      0 ≤ hostKraU3Power M hM (fun x ↦ DH x) hDHtop :=
    hostKraU3Power_nonneg M hM (fun x ↦ DH x) hDHtop
  have hnested :=
    nested_sqrt_hostKraU3_bound
      (CG ^ 2) t
      (hostKraU3Power M hM (fun x ↦ DH x) hDHtop)
      ht.le ht1 hpnonneg (by simpa only [DH, hDHtop] using hpower)
  have hvec := hN i
  have hKt :
      0 < (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t := by
    positivity
  calc
    (@inner ℂ (Lp ℂ 2 M.μ) _ A
        ((((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n)).re ≤
        ‖@inner ℂ (Lp ℂ 2 M.μ) _ A
          ((((N + 1 : ℕ) : ℂ)⁻¹) •
            ∑ n ∈ Finset.range (N + 1), v n)‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ ≤ ‖A‖ *
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n‖ :=
      norm_inner_le_norm _ _
    _ ≤ (CF * ‖F‖) *
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1), v n‖ :=
      mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    _ ≤ (CF * ‖F‖) *
        ((Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t) := by
      exact mul_le_mul_of_nonneg_left
        (hvec.le.trans hnested) hD
    _ < (CF * ‖F‖ + 1) *
        (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1) * t := by
      nlinarith

/-- Cesàro averaging commutes with the two finite block sums used in
the complete van der Corput correlation. -/
lemma cesaroAverage_sum_range_two
    (a : ℕ → ℕ → ℕ → ℝ) (L N : ℕ) :
    cesaroAverage
        (fun n ↦ ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L, a h k n) N =
      ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L,
        cesaroAverage (a h k) N := by
  unfold cesaroAverage
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

/-- One row of a good/bad decomposition: good entries cost `G`, while
the exceptional entries cost at most an additional `B`. -/
lemma sum_range_le_good_add_bad
    (q p : ℕ → ℝ) (L : ℕ) (τ G B : ℝ)
    (hG : 0 ≤ G)
    (hq : ∀ k < L, q k ≤ if τ ≤ p k then B else G) :
    (Finset.range L).sum q ≤
      (L : ℝ) * G +
        (((Finset.range L).filter (fun k ↦ τ ≤ p k)).card : ℝ) * B := by
  calc
    (Finset.range L).sum q ≤
        (Finset.range L).sum (fun k ↦
          G + if τ ≤ p k then B else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkL := Finset.mem_range.mp hk
      by_cases hbad : τ ≤ p k
      · have hqk := hq k hkL
        rw [if_pos hbad] at hqk
        simp only [if_pos hbad]
        linarith
      · have hqk := hq k hkL
        rw [if_neg hbad] at hqk
        simpa only [if_neg hbad, add_zero] using hqk
    _ = (L : ℝ) * G +
        (((Finset.range L).filter (fun k ↦ τ ≤ p k)).card : ℝ) * B := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      classical
      rw [← Finset.sum_filter]
      simp

/-- `U⁴` nullity of the third factor gives the complete uniform
van der Corput block-correlation decay for the `(1,2,3)` progression. -/
lemma tripleKoopmanProduct_hasUniformVanDerCorputBlockDecay
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (hzero : HasZeroHostKraU4 M hM (fun x ↦ H x) hHtop) :
    VanDerCorput.HasUniformVanDerCorputBlockDecay
      (tripleKoopmanProduct M hM F G H hFtop hGtop) := by
  intro δ hδ
  let K : ℝ :=
    (CF * ‖F‖ + 1) *
      (Real.sqrt (4 * (CG ^ 2) ^ 2 + 1) + 1)
  let B : ℝ := ((CF * CG) * ‖H‖) ^ 2
  have hK : 0 < K := by
    dsimp only [K]
    have hCFnorm : 0 ≤ CF * ‖F‖ :=
      mul_nonneg hCF (norm_nonneg F)
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  let t : ℝ := min 1 (δ / (8 * K))
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : K * t ≤ δ / 8 := by
    have htupper : t ≤ δ / (8 * K) := min_le_right _ _
    rw [le_div_iff₀ (by positivity : 0 < (8 : ℝ))]
    calc
      K * t * 8 = (8 * K) * t := by ring
      _ ≤ (8 * K) * (δ / (8 * K)) :=
        mul_le_mul_of_nonneg_left htupper (by positivity)
      _ = δ := by field_simp
  have ht8 : 0 < t ^ 8 := pow_pos ht 8
  let α : ℝ := δ * t ^ 8 / (16 * (B + 1))
  have hα : 0 < α := by
    dsimp only [α]
    positivity
  obtain ⟨L, hL, hrow⟩ :=
    exists_uniform_three_derivativeU3Power_row_sum_lt
      M hM H hHtop hzero α hα
  refine ⟨L, hL, ?_⟩
  let p : ℕ → ℕ → ℝ := fun h k ↦
    hostKraU3Power M hM
      (fun x ↦ koopmanMultiplicativeDerivative
        M hM H hHtop (3 * k) (3 * h) x)
      (koopmanMultiplicativeDerivative_memLp_top
        M hM H hHtop (3 * k) (3 * h))
  have hpnonneg : ∀ h k, 0 ≤ p h k := by
    intro h k
    exact hostKraU3Power_nonneg M hM _ _
  have hall :
      ∀ᶠ N : ℕ in atTop,
        ∀ h ∈ Finset.range L, ∀ k ∈ Finset.range L, ∀ i : ℕ,
          cesaroAverage
            (fun n ↦
              (@inner ℂ (Lp ℂ 2 M.μ) _
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + k)))
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + h)))).re) N ≤
            if t ^ 8 ≤ p h k then B else K * t := by
    rw [Filter.eventually_all_finset]
    intro h hh
    rw [Filter.eventually_all_finset]
    intro k hk
    by_cases hbad : t ^ 8 ≤ p h k
    · exact Filter.Eventually.of_forall fun N i ↦ by
        rw [if_pos hbad]
        dsimp only [B]
        exact cesaroAverage_re_inner_tripleKoopmanProduct_block_le
          M hM F G H hFtop hGtop CF CG hCF hCG
          hFbound hGbound N i h k
    · have hgood : p h k ≤ t ^ 8 :=
        le_of_lt (lt_of_not_ge hbad)
      have hevent :=
        cesaroAverage_re_inner_tripleKoopmanProduct_block_lt_of_u3_le
          M hM hErg F G H hFtop hGtop hHtop
          CF CG hCF hCG hFbound hGbound t ht ht1 h k
          (by simpa only [p] using hgood)
      filter_upwards [hevent] with N hN
      intro i
      rw [if_neg hbad]
      simpa only [K, mul_assoc] using (hN i).le
  filter_upwards [hall] with N hN
  intro i
  rw [cesaroAverage_sum_range_two]
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hgoodrow : 0 ≤ K * t := mul_nonneg hK.le ht.le
  have hrowBound (h : ℕ) (hh : h < L) :
      (Finset.range L).sum (fun k ↦
        cesaroAverage
          (fun n ↦
            (@inner ℂ (Lp ℂ 2 M.μ) _
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + k)))
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + h)))).re) N) <
        δ / 4 * (L : ℝ) := by
    let Bad := (Finset.range L).filter (fun k ↦ t ^ 8 ≤ p h k)
    have hsum :=
      sum_range_le_good_add_bad
        (fun k ↦
          cesaroAverage
            (fun n ↦
              (@inner ℂ (Lp ℂ 2 M.μ) _
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + k)))
                (tripleKoopmanProduct M hM F G H hFtop hGtop
                  (i + (n + h)))).re) N)
        (p h) L (t ^ 8) (K * t) B hgoodrow
        (fun k hk ↦ hN h (Finset.mem_range.mpr hh)
          k (Finset.mem_range.mpr hk) i)
    have hmark :
        (Bad.card : ℝ) * t ^ 8 < (2 * α) * (L : ℝ) := by
      apply card_filter_threshold_mul_lt_of_sum_lt
        (p h) (hpnonneg h) L (t ^ 8) (2 * α)
      simpa only [p, Bad, mul_assoc] using hrow h hh
    have hbadScaled :
        (Bad.card : ℝ) * B < δ / 8 * (L : ℝ) := by
      by_cases hBzero : B = 0
      · simp only [hBzero, mul_zero]
        positivity
      · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
        have hmul :
            ((Bad.card : ℝ) * t ^ 8) * B <
              ((2 * α) * (L : ℝ)) * B :=
          mul_lt_mul_of_pos_right hmark hBpos
        have hratio : B / (B + 1) ≤ 1 := by
          exact (div_le_one (by positivity : 0 < B + 1)).2 (by linarith)
        have hcoef :
            2 * α * B ≤ δ / 8 * t ^ 8 := by
          calc
            2 * α * B =
                (δ * t ^ 8 / 8) * (B / (B + 1)) := by
              dsimp only [α]
              field_simp
              norm_num
            _ ≤ (δ * t ^ 8 / 8) * 1 :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = δ / 8 * t ^ 8 := by ring
        have hscaled :
            ((Bad.card : ℝ) * B) * t ^ 8 <
              (δ / 8 * (L : ℝ)) * t ^ 8 := by
          calc
            ((Bad.card : ℝ) * B) * t ^ 8 =
                ((Bad.card : ℝ) * t ^ 8) * B := by ring
            _ < ((2 * α) * (L : ℝ)) * B := hmul
            _ = (2 * α * B) * (L : ℝ) := by ring
            _ ≤ (δ / 8 * t ^ 8) * (L : ℝ) :=
              mul_le_mul_of_nonneg_right hcoef hLreal.le
            _ = (δ / 8 * (L : ℝ)) * t ^ 8 := by ring
        nlinarith [hscaled]
    calc
      _ ≤ (L : ℝ) * (K * t) + (Bad.card : ℝ) * B := by
        simpa only [Bad] using hsum
      _ < δ / 4 * (L : ℝ) := by
        have hgoodScaled :
            (L : ℝ) * (K * t) ≤ δ / 8 * (L : ℝ) := by
          nlinarith
        nlinarith
  calc
    ∑ h ∈ Finset.range L, ∑ k ∈ Finset.range L,
        cesaroAverage
          (fun n ↦
            (@inner ℂ (Lp ℂ 2 M.μ) _
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + k)))
              (tripleKoopmanProduct M hM F G H hFtop hGtop
                (i + (n + h)))).re) N <
        ∑ _h ∈ Finset.range L, δ / 4 * (L : ℝ) := by
      apply Finset.sum_lt_sum
      · intro h hh
        exact (hrowBound h (Finset.mem_range.mp hh)).le
      · exact ⟨0, Finset.mem_range.mpr hL,
          hrowBound 0 hL⟩
    _ = δ / 4 * (L : ℝ) ^ 2 := by
      simp
      ring
    _ < δ * (L : ℝ) ^ 2 := by
      nlinarith [sq_pos_of_pos hLreal]

/-- Uniform translated `L²` decay of the three-factor progression when
its third factor is `U⁴`-null. -/
lemma tripleKoopmanProduct_uniform_cesaro_norm_zero_of_hasZeroHostKraU4
    (M : System.{u}) [StandardBorelSpace M.X]
    (hM : Chapter01.IsMeasurePreservingSystem M)
    (hErg : IsErgodic M)
    (F G H : Lp ℂ 2 M.μ)
    (hFtop : MemLp (fun x ↦ F x) ⊤ M.μ)
    (hGtop : MemLp (fun x ↦ G x) ⊤ M.μ)
    (hHtop : MemLp (fun x ↦ H x) ⊤ M.μ)
    (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFbound : ∀ᵐ x ∂M.μ, ‖F x‖ ≤ CF)
    (hGbound : ∀ᵐ x ∂M.μ, ‖G x‖ ≤ CG)
    (hzero : HasZeroHostKraU4 M hM (fun x ↦ H x) hHtop) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ i : ℕ,
        ‖(((N + 1 : ℕ) : ℂ)⁻¹) •
          ∑ n ∈ Finset.range (N + 1),
            tripleKoopmanProduct M hM F G H hFtop hGtop (i + n)‖ < ε := by
  exact VanDerCorput.vectorCesaro_uniform_tendsto_zero_of_blockDecay
    (tripleKoopmanProduct M hM F G H hFtop hGtop)
    ((CF * CG) * ‖H‖)
    (norm_tripleKoopmanProduct_le
      M hM F G H hFtop hGtop CF CG hCF hCG hFbound hGbound)
    (tripleKoopmanProduct_hasUniformVanDerCorputBlockDecay
      M hM hErg F G H hFtop hGtop hHtop
      CF CG hCF hCG hFbound hGbound hzero)

end Chapter02.HostKraU4ProgressionDecay
